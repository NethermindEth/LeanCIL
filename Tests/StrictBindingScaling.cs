using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;

partial class Program
{
    /// <summary>The most a claim may cost more, per claim, when the claims grow at a fixed image.</summary>
    const double MaximumPerClaimGrowth = 2;

    /// <summary>The most the check may take longer, as a multiple, for a larger image with the same claims.</summary>
    const double MaximumImageGrowth = 4;

    /// <summary>The most a carried key byte may cost more, per byte, when the carried key grows fourfold.</summary>
    const double MaximumPerByteGrowth = 1.25;

    /// <summary>The most a carried row may cost more, per row, when the carried rows grow fourfold.</summary>
    const double MaximumPerRowGrowth = 1.5;

    /// <summary>
    /// Body-check heartbeats grow linearly with claims and cover decoding the image once per page.
    /// The fixture's heartbeat count is the fixed cost subtracted from each larger case.
    /// </summary>
    static void CheckBindingScaling(string root)
    {
        // Memory cannot be measured here, so the page layout that bounds it is pinned: pages of about 250 methods
        // until the page cap, then pages that grow with the evidence, and one empty page for no methods.
        (int Methods, int Size, int Pages)[] layouts =
            [(0, 1, 1), (318, 159, 2), (1272, 212, 6), (2000, 250, 8), (5088, 636, 8), (10767, 1346, 8)];
        foreach (var (methods, size, pages) in layouts)
            if (BindingPageSize(methods) != size || BindingPageCount(methods) != pages ||
                pages * size < methods)
                throw new InvalidOperationException($"{methods} methods are paged {BindingPageCount(methods)} x " +
                    $"{BindingPageSize(methods)}, not {pages} x {size}");
        Console.WriteLine("PASS the body proof pages at about 250 methods up to 8 pages");
        var package = FixturePackage();
        Run(["lake", "build", "StrictBinding.Evidence"], package, progress: "Building the strict binding library");
        CheckGeneratedBodiesModuleElaborates(root, package);
        CheckAssemblyBlockScaling(root, package);
        CheckSliceRowsScaling(root, package);
        var examples = File.ReadAllBytes(At("Examples/Assembly/bin/Examples.dll"));
        var larger = new byte[examples.Length + 770 * 1024];
        examples.CopyTo(larger, 0);
        new Random(5).NextBytes(larger.AsSpan(examples.Length));
        const int smaller = 1272;
        const int largerClaims = 5088;
        (string Name, byte[] Bytes, int? Claims)[] cases =
        [
            ("fixture", StrictBindingFacts.ReadImage(File.ReadAllText(Fixture)), null),
            ($"Examples.dll, {smaller} claims", examples, smaller),
            ($"Examples.dll and 770 KB more, {smaller} claims", larger, smaller),
            ($"Examples.dll, {largerClaims} claims", examples, largerClaims)
        ];
        Directory.CreateDirectory(root);
        var heartbeats = new long[cases.Length];
        for (var index = 0; index < cases.Length; index++)
        {
            var path = Path.Combine(root, $"Bodies{index}.lean");
            File.WriteAllText(path, AllBodiesModule(cases[index].Bytes, cases[index].Claims) +
                "\n#eval show IO Nat from IO.getNumHeartbeats\n");
            var run = Execute(["lake", "env", "lean", "-DElab.async=false", path], cwd: package);
            if (run.Code != 0)
                throw new InvalidOperationException($"The bodies of {cases[index].Name} were not found: {run.Output}");
            heartbeats[index] = long.Parse(run.Output.Split('\n', StringSplitOptions.TrimEntries |
                StringSplitOptions.RemoveEmptyEntries).Last(), System.Globalization.CultureInfo.InvariantCulture);
        }
        var costs = cases.Zip(heartbeats, (item, count) => $"{item.Name} {count} heartbeats");
        Console.WriteLine("Body checks: " + string.Join(", ", costs));
        double Above(int index) => heartbeats[index] - heartbeats[0];
        if (Above(1) <= 0)
            throw new InvalidOperationException("The body check has no measured work above the fixture");
        var perClaim = Above(3) / largerClaims / (Above(1) / smaller);
        var perImage = Above(2) / Above(1);
        if (perClaim > MaximumPerClaimGrowth || perImage > MaximumImageGrowth)
            throw new InvalidOperationException(
                $"The body check used {perClaim:F1} times the heartbeats per claim for " +
                $"{largerClaims / smaller} times the claims and {perImage:F1} times for 8.8 times the image");
        Console.WriteLine($"PASS the body check is linear in the claims ({perClaim:F1} times per claim) and " +
            $"independent of the image size ({perImage:F1} times for 8.8)");
    }

    /// <summary>
    /// The check of a carried Assembly block reads each carried entry byte once, so its kernel heartbeats grow
    /// linearly with them. Images with a short name and a public key blob of 256, 1024 and 4096 bytes are checked,
    /// and the heartbeats of preparing each image are subtracted; the name stays short because preparing spells
    /// the identity at a cost quadratic in its length. A byte added from 1024 to 4096 may cost at most 1.25 times
    /// a byte added from 256 to 1024, where a cost quadratic in the bytes would give four times; reruns differ by
    /// a few heartbeats, far inside that bound.
    /// </summary>
    static void CheckAssemblyBlockScaling(string root, string package)
    {
        const string report = "#eval show IO Nat from IO.getNumHeartbeats";
        int[] sizes = [256, 1024, 4096];
        Run(["lake", "build", "StrictBinding.Rows"], package, progress: "Building the carried metadata checks");
        var cases = string.Concat(sizes.Select(size =>
        {
            var file = SyntheticAssembly(size);
            var pinned = $"{{ identity := \"{StrictBindingFacts.Identity(file)}\", image := image }}";
            return $$"""
                namespace Size{{size}}
                {{BindingImage.Definitions(file)}}
                def pinned : StrictBinding.PinnedImage := {{pinned}}
                def block : CIL.Extraction.AssemblyMetadata :=
                  {{StrictBindingFacts.AssemblyBlock(file)}}
                {{report}}
                theorem prepared : StrictBinding.ok (StrictBinding.prepareOne pinned) = true := by decide +kernel
                {{report}}
                theorem checked : StrictBinding.ok
                    (StrictBinding.prepareOne pinned >>= (StrictBinding.assemblyBound · block)) = true := by
                  decide +kernel
                {{report}}
                end Size{{size}}

                """;
        }));
        var path = Path.Combine(root, "AssemblyBlocks.lean");
        File.WriteAllText(path, $"import StrictBinding.Rows\n\n{cases}");
        var measured = RequireGrowth(sizes, CheckHeartbeats(path, package, sizes.Length, "carried Assembly blocks"),
            MaximumPerByteGrowth, "carried Assembly block check", "byte");
        Console.WriteLine($"PASS the carried Assembly block check is linear in its key bytes ({measured})");
    }

    /// <summary>
    /// The rows check sorts the heap cells of the carried rows once per heap and reads each row and entry once, so
    /// its kernel heartbeats grow as n log n in the rows. Images with 64, 256 and 1024 MethodDef rows, each with its
    /// own name and all with one signature, are checked against a slice of all their rows, and the heartbeats of
    /// preparing each image are subtracted. A row added from 256 to 1024 may cost at most 1.5 times a row added
    /// from 64 to 256, where n log n gives at most 1.23 and a numbering quadratic in the rows about four.
    /// </summary>
    static void CheckSliceRowsScaling(string root, string package)
    {
        const string report = "#eval show IO Nat from IO.getNumHeartbeats";
        int[] sizes = [64, 256, 1024];
        var cases = string.Concat(sizes.Select(size =>
        {
            var file = SyntheticMethods(size);
            var pinned = $"{{ identity := \"{StrictBindingFacts.Identity(file)}\", image := image }}";
            return $$"""
                namespace Rows{{size}}
                {{BindingImage.Definitions(file)}}
                def pinned : StrictBinding.PinnedImage := {{pinned}}
                def assemblyBlock : CIL.Extraction.AssemblyMetadata :=
                  {{StrictBindingFacts.AssemblyBlock(file)}}
                -- A list literal of a thousand rows elaborates deeper than the default limit.
                set_option maxRecDepth 65536 in
                def slice : CIL.Extraction.MetadataSlice :=
                  {{StrictBindingFacts.Slice(file)}}
                {{report}}
                theorem prepared : StrictBinding.ok (StrictBinding.prepareOne pinned) = true := by decide +kernel
                {{report}}
                theorem checked : StrictBinding.ok (StrictBinding.prepareOne pinned >>= fun image =>
                    StrictBinding.rowsBound image slice.rows slice.strings slice.blobs) = true := by
                  decide +kernel
                {{report}}
                end Rows{{size}}

                """;
        }));
        var path = Path.Combine(root, "SliceRows.lean");
        File.WriteAllText(path, $"import StrictBinding.Rows\n\n{cases}");
        var measured = RequireGrowth(sizes, CheckHeartbeats(path, package, sizes.Length, "carried rows"),
            MaximumPerRowGrowth, "rows check", "row");
        Console.WriteLine($"PASS the rows check grows as n log n in the carried rows ({measured})");
    }

    /// <summary>
    /// The kernel heartbeats of each case's check above preparing its image, from a module that reports the count
    /// before preparing, after preparing, and after a check that prepares the image again.
    /// </summary>
    static long[] CheckHeartbeats(string path, string package, int cases, string subject)
    {
        // Without the flag the kernel checks on another thread and its heartbeats go uncounted.
        var output = Run(["lake", "env", "lean", "-DElab.async=false", "-M", "8192", path], cwd: package);
        var counts = output.Split('\n').Select(line => line.Trim())
            .Where(line => line.Length > 0 && line.All(char.IsAsciiDigit))
            .Select(line => long.Parse(line, System.Globalization.CultureInfo.InvariantCulture)).ToArray();
        if (counts.Length != 3 * cases || output.Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidOperationException($"Unchecked {subject}:\n{output}");
        return [.. Enumerable.Range(0, cases).Select(index =>
            counts[3 * index + 2] - 2 * counts[3 * index + 1] + counts[3 * index])];
    }

    /// <summary>
    /// A unit added from the second size to the third costs at most `bound` times a unit added from the first to
    /// the second; returns the measurements as text.
    /// </summary>
    static string RequireGrowth(int[] sizes, long[] checks, double bound, string subject, string unit)
    {
        var smaller = (double)(checks[1] - checks[0]) / (sizes[1] - sizes[0]);
        var larger = (double)(checks[2] - checks[1]) / (sizes[2] - sizes[1]);
        var measured = string.Join(", ", sizes.Zip(checks, (size, cost) => $"{cost} heartbeats at {size}"));
        var growth = (larger / smaller).ToString("F2", System.Globalization.CultureInfo.InvariantCulture);
        if (smaller <= 0 || larger / smaller > bound)
            throw new InvalidOperationException($"The {subject} costs {measured}; a {unit} costs {growth} times as " +
                $"much from {sizes[1]} to {sizes[2]} as from {sizes[0]} to {sizes[1]}");
        return $"{measured}; {growth} times per {unit}";
    }

    /// <summary>
    /// A library named Synthetic whose Assembly row names a public key blob that takes <paramref name="size"/>
    /// bytes of the `#Blob` heap, with its length prefix.
    /// </summary>
    static byte[] SyntheticAssembly(int size)
    {
        const int shortBlob = 0x80;
        var metadata = new MetadataBuilder();
        var name = metadata.GetOrAddString("Synthetic");
        var keyLength = size <= shortBlob ? size - 1 : size - 2;
        var keyBytes = Enumerable.Range(0, keyLength).Select(index => (byte)(index * 7 + 1)).ToArray();
        var key = metadata.GetOrAddBlob(keyBytes);
        metadata.AddAssembly(name, new Version(1, 2, 3, 4), default, key, AssemblyFlags.PublicKey,
            AssemblyHashAlgorithm.Sha1);
        metadata.AddModule(0, metadata.GetOrAddString("Synthetic.dll"), metadata.GetOrAddGuid(Guid.Empty), default,
            default);
        metadata.AddTypeDefinition(default, default, metadata.GetOrAddString("<Module>"), default,
            MetadataTokens.FieldDefinitionHandle(1), MetadataTokens.MethodDefinitionHandle(1));
        var builder = new ManagedPEBuilder(PEHeaderBuilder.CreateLibraryHeader(), new MetadataRootBuilder(metadata),
            new BlobBuilder());
        var image = new BlobBuilder();
        builder.Serialize(image);
        return image.ToArray();
    }

    /// <summary>
    /// A library named Synthetic with `count` MethodDef rows without bodies, each named for its row and all with one
    /// signature.
    /// </summary>
    static byte[] SyntheticMethods(int count)
    {
        var metadata = new MetadataBuilder();
        var name = metadata.GetOrAddString("Synthetic");
        metadata.AddAssembly(name, new Version(1, 2, 3, 4), default, default, default, AssemblyHashAlgorithm.Sha1);
        metadata.AddModule(0, metadata.GetOrAddString("Synthetic.dll"), metadata.GetOrAddGuid(Guid.Empty), default,
            default);
        metadata.AddTypeDefinition(default, default, metadata.GetOrAddString("<Module>"), default,
            MetadataTokens.FieldDefinitionHandle(1), MetadataTokens.MethodDefinitionHandle(1));
        var signature = new BlobBuilder();
        new BlobEncoder(signature).MethodSignature().Parameters(0, returnType => returnType.Void(), _ => { });
        var shared = metadata.GetOrAddBlob(signature);
        for (var index = 0; index < count; index++)
            metadata.AddMethodDefinition(MethodAttributes.Public | MethodAttributes.Static, default,
                metadata.GetOrAddString("M" + index), shared, -1, MetadataTokens.ParameterHandle(1));
        var builder = new ManagedPEBuilder(PEHeaderBuilder.CreateLibraryHeader(), new MetadataRootBuilder(metadata),
            new BlobBuilder());
        var image = new BlobBuilder();
        builder.Serialize(image);
        return image.ToArray();
    }

    /// <summary>
    /// Elaborates the module the audit generates, over an extraction with no methods, so a malformed
    /// declaration in the generator fails here and not only in an end-to-end audit.
    /// </summary>
    static void CheckGeneratedBodiesModuleElaborates(string root, string package)
    {
        const string imports = "import BindingAudit.Images\nimport Extracted\nimport StrictBinding.Evidence\n";
        const string stubs = """
            import StrictBinding.Evidence
            namespace Extracted
            def methodEvidence : List CIL.Extraction.MethodEvidence := []
            end Extracted
            namespace BindingAudit
            def images : List StrictBinding.PinnedImage := []
            end BindingAudit

            """;
        Directory.CreateDirectory(root);
        foreach (var (methods, size) in new[] { (3, 1), (0, BindingPageSize(0)) })
        {
            var source = BodiesModuleSource(methods, size);
            if (!source.StartsWith(imports, StringComparison.Ordinal))
                throw new InvalidOperationException("The generated bodies module no longer starts with its imports");
            var path = Path.Combine(root, $"GeneratedBodies{methods}.lean");
            File.WriteAllText(path, stubs.ReplaceLineEndings("\n") + source[imports.Length..]);
            var run = Execute(["lake", "env", "lean", path], cwd: package);
            if (run.Code != 0)
                throw new InvalidOperationException(
                    $"The generated bodies module for {methods} methods does not elaborate: {run.Output}");
        }
        Console.WriteLine("PASS the generated bodies module elaborates, also for no methods");
    }

    /// <summary>
    /// A module stating that every body System.Reflection.Metadata reads is found in the image, composed the way a
    /// generated module composes its pages: one theorem per page of claims, each its own kernel evaluation, and the
    /// whole from `claimsHold_of_pages`. The page lemmas are checked when the module is built.
    /// </summary>
    static string AllBodiesModule(byte[] file, int? claims)
    {
        var identity = StrictBindingFacts.Read(file).Last().Text;
        var read = StrictBindingFacts.Bodies(file);
        // A claim count beyond the bodies the image has repeats them, so the claims can outgrow a fixed image.
        var bodies = Enumerable.Range(0, claims ?? read.Count).Select(index => read[index % read.Count]).ToArray();
        var size = BindingPageSize(bodies.Length);
        // One definition per claim keeps each list literal small enough for the elaborator's recursion limit.
        var parts = bodies.Select(body =>
            $"{{ identity := \"{identity}\", token := 0x{body.Token:x8}, " +
            $"bytes := [{string.Join(", ", body.Bytes)}] }}")
            .Chunk(size).ToArray();
        var defs = string.Concat(parts.Select((part, index) =>
            string.Concat(part.Select((claim, at) =>
                $"def claim{index}_{at} : StrictBinding.BodyClaim := {claim}\n")) +
            $"def claims{index} : List StrictBinding.BodyClaim :=\n  " +
            $"[{string.Join(", ", part.Select((_, at) => $"claim{index}_{at}"))}]\n\n"));
        var joined = Enumerable.Range(0, parts.Length - 1).Reverse().Aggregate($"claims{parts.Length - 1}",
            (rest, index) => $"(claims{index} ++ {rest})");
        var lemmas = string.Concat(parts.Select((_, index) => $"theorem bodiesOf{index} : " +
            $"StrictBinding.ClaimsHold StrictBinding.bodyClaimBound pinned " +
            $"(StrictBinding.claimPage claims {size} {index}) := by\n" +
            "  decide +kernel\n\n"));
        var chain = string.Concat(Enumerable.Range(0, parts.Length).Reverse()
            .Select(index => $"(.succ bodiesOf{index} "));
        return $$"""
            import StrictBinding.Bind

            namespace Scaling

            {{BindingImage.Definitions(file)}}
            def pinned : List StrictBinding.PinnedImage := [{ identity := "{{identity}}", image := image }]

            {{defs}}def claims : List StrictBinding.BodyClaim := {{joined}}

            theorem prepared : StrictBinding.ok (StrictBinding.prepare pinned) = true := by decide +kernel

            {{lemmas}}theorem found : StrictBinding.ClaimsHold StrictBinding.bodyClaimBound pinned claims :=
              StrictBinding.claimsHold_of_pages (size := {{size}}) (count := {{parts.Length}}) prepared
                (by decide +kernel) {{chain}}.zero{{new string(')', parts.Length)}}

            end Scaling
            """;
    }
}
