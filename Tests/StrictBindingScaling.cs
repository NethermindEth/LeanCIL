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

    /// <summary>The most an added metadata page may cost relative to an earlier added page.</summary>
    const double MaximumPerPageGrowth = 1.25;

    /// <summary>The most a check of fixed claims may cost more, as a multiple, at 16 times the TypeDef rows.</summary>
    const double MaximumTableGrowth = 1.15;

    /// <summary>The most a page of chunks with equal ends may cost, as a multiple of one with random ends.</summary>
    const double MaximumEqualTailGrowth = 1.1;

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
        Run(["lake", "build", "StrictBinding.Evidence", "StrictBinding.Sha256"], package,
            progress: "Building the strict binding library");
        CheckGeneratedPagedModulesElaborate(root, package);
        CheckAssemblyBlockScaling(root, package);
        CheckSliceRowsScaling(root, package);
        CheckUserStringScaling(root, package);
        CheckMetadataPageScaling(root, package);
        CheckMetadataRowsModuleScaling(root, package);
        CheckTypeDefinitionScaling(root, package);
        CheckEqualTailPageCost(root, package);
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

    /// <summary>The whole metadata check with one user string grows linearly in its carried bytes.</summary>
    static void CheckUserStringScaling(string root, string package)
    {
        const string report = "#eval show IO Nat from IO.getNumHeartbeats";
        int[] sizes = [1024, 4096, 16384];
        var cases = string.Concat(sizes.Select(size =>
        {
            var characters = size / 2;
            var file = SyntheticUserString(characters);
            var length = 2 * characters + 1;
            int[] prefix = length < 0x4000
                ? [0x80 | (length >> 8), length & 255]
                : [0xC0 | (length >> 24), (length >> 16) & 255, (length >> 8) & 255, length & 255];
            return $$"""
                namespace UserString{{size}}
                {{BindingImage.Definitions(file)}}
                /-- The synthetic image under its assembly identity. -/
                def pinned : StrictBinding.PinnedImage :=
                  { identity := "{{StrictBindingFacts.Identity(file)}}", image := image }
                /-- The independently numbered Assembly block. -/
                def assemblyBlock : CIL.Extraction.AssemblyMetadata :=
                  {{StrictBindingFacts.AssemblyBlock(file)}}
                /-- One UTF-16 user string, including its prefix and terminal byte. -/
                def entry : List Nat := [{{string.Join(", ", prefix)}}] ++
                  (List.replicate {{characters}} [65, 0]).flatten ++ [0]
                /-- Metadata carrying the Assembly block and one user string. -/
                def slice : CIL.Extraction.MetadataSlice :=
                  { assembly := assemblyBlock, userStrings := [(1, entry)] }
                {{report}}
                /-- The synthetic image has a supported container and metadata layout. -/
                theorem prepared : StrictBinding.ok (StrictBinding.prepareOne pinned) = true := by decide +kernel
                {{report}}
                /-- Every carried entry belongs to the synthetic image. -/
                theorem checked :
                    StrictBinding.ok (StrictBinding.prepareOne pinned >>= fun image =>
                      StrictBinding.sliceBound image slice) = true := by
                  decide +kernel
                {{report}}
                #print axioms prepared
                #print axioms checked
                end UserString{{size}}

                """;
        }));
        Directory.CreateDirectory(root);
        var path = Path.Combine(root, "UserStrings.lean");
        File.WriteAllText(path, $"import StrictBinding.Slice\n\n{cases}");
        var measured = RequireGrowth(sizes, CheckHeartbeats(path, package, sizes.Length, "carried user strings"),
            MaximumPerByteGrowth, "user-string metadata check", "byte");
        Console.WriteLine($"PASS the complete metadata check is linear in its user-string bytes ({measured})");
    }

    /// <summary>
    /// Paged proofs of the slice contents, the rows and heaps a method carries without its Assembly block, at 1, 4 and
    /// 16 pages have flat marginal cost per page.
    /// </summary>
    static void CheckMetadataPageScaling(string root, string package)
    {
        const string report = "#eval show IO Nat from IO.getNumHeartbeats";
        const int characters = 512;
        int[] sizes = [1, 4, 16];
        var file = SyntheticUserString(characters);
        var cases = string.Concat(sizes.Select(pages =>
        {
            var lemmas = string.Concat(Enumerable.Range(0, pages).Select(index => $$"""
                /-- The rows and heaps of this page's method metadata are the pinned image's. -/
                theorem metadataPage{{index}} :
                    StrictBinding.ClaimsHold StrictBinding.methodMetadataBound pinned
                    (StrictBinding.claimPage claims 1 {{index}}) := by decide +kernel
                #print axioms metadataPage{{index}}

                """));
            var chain = string.Concat(Enumerable.Range(0, pages).Reverse()
                .Select(index => $"(.succ metadataPage{index} "));
            return $$"""
                namespace Pages{{pages}}
                {{BindingImage.Definitions(file)}}
                /-- The synthetic image under its assembly identity. -/
                def pinned : List StrictBinding.PinnedImage :=
                  [{ identity := "{{StrictBindingFacts.Identity(file)}}", image := image }]
                /-- The independently numbered Assembly block. -/
                def assemblyBlock : CIL.Extraction.AssemblyMetadata :=
                  {{StrictBindingFacts.AssemblyBlock(file)}}
                /-- A two-byte prefix and a 1025-byte UTF-16 payload, including the terminal byte. -/
                def entry : List Nat := [132, 1] ++ (List.replicate {{characters}} [65, 0]).flatten ++ [0]
                /-- Each method carries a complete Assembly block and one user string. -/
                def metadata : CIL.Extraction.MethodMetadata :=
                  { own := { assembly := assemblyBlock, userStrings := [(1, entry)] } }
                /-- One method per page keeps the compared byte count fixed per page. -/
                def claims : List CIL.Extraction.MethodMetadata := List.replicate {{pages}} metadata
                {{report}}
                /-- The pinned image has a supported container and metadata layout. -/
                theorem prepared : StrictBinding.ok (StrictBinding.prepare pinned) = true := by decide +kernel
                {{report}}
                {{lemmas}}
                /-- The pages cover every metadata claim. -/
                theorem checked : StrictBinding.ClaimsHold StrictBinding.methodMetadataBound pinned claims :=
                  StrictBinding.claimsHold_of_pages (size := 1) (count := {{pages}}) prepared
                    (by decide +kernel) {{chain}}.zero{{new string(')', pages)}}
                {{report}}
                #print axioms prepared
                #print axioms checked
                end Pages{{pages}}

                """;
        }));
        Directory.CreateDirectory(root);
        var path = Path.Combine(root, "MetadataPages.lean");
        File.WriteAllText(path, $"import StrictBinding.Evidence\n\n{cases}");
        var measured = RequireGrowth(sizes, CheckHeartbeats(path, package, sizes.Length, "metadata pages"),
            MaximumPerPageGrowth, "metadata page check", "page");
        Console.WriteLine($"PASS the paged metadata contents proof has flat cost per page ({measured})");
    }

    /// <summary>
    /// The pages of the generated metadata rows module, kernel-checked as replay checks them, over synthetic images
    /// whose methods each carry their image's Assembly block and their own MethodDef row, at 318, 1272 and 5088
    /// methods of one image and at 1272 methods split over two, paged as a deep run pages them. The evidence's
    /// metadata list is given directly, and the heartbeats of one preparation are subtracted. A method selects its
    /// image and checks its row once and each distinct block is checked once, so a method may cost at most twice as
    /// much at 5088 methods as at 1272, although the image the preparations decode grows with the methods too, and
    /// at most twice as much over two images as over one.
    /// </summary>
    static void CheckMetadataRowsModuleScaling(string root, string package)
    {
        int[] sizes = [318, 1272, 5088];
        Directory.CreateDirectory(root);
        var heartbeats = sizes.Select(methods => MetadataRowsModuleHeartbeats(root, package, methods, 1)).ToArray();
        var split = MetadataRowsModuleHeartbeats(root, package, sizes[1], 2);
        var measured = string.Join(", ", sizes.Zip(heartbeats, (methods, cost) => $"{cost} heartbeats at {methods}"));
        var perMethod = (double)heartbeats[2] / sizes[2] / ((double)heartbeats[1] / sizes[1]);
        if (heartbeats[1] <= 0 || perMethod > MaximumPerClaimGrowth)
            throw new InvalidOperationException($"The metadata rows module costs {measured}; a method costs " +
                $"{perMethod:F2} times as much at {sizes[2]} methods as at {sizes[1]}");
        var perImage = (double)split / heartbeats[1];
        if (split <= 0 || perImage > MaximumPerClaimGrowth)
            throw new InvalidOperationException($"The metadata rows module costs {split} heartbeats for {sizes[1]} " +
                $"methods over two images and {heartbeats[1]} over one");
        Console.WriteLine($"PASS the metadata rows module is linear in the methods ({measured}; " +
            $"{perMethod:F2} times per method; {split} heartbeats at {sizes[1]} over two images, " +
            $"{perImage:F2} times)");
    }

    /// <summary>
    /// The kernel heartbeats of the generated metadata rows module, above one preparation, for `methods` methods
    /// split evenly over `images` synthetic images, each method carrying its image's Assembly block and its own
    /// MethodDef row.
    /// </summary>
    static long MetadataRowsModuleHeartbeats(string root, string package, int methods, int images)
    {
        const string report = "#eval show IO Nat from IO.getNumHeartbeats";
        const string imports = "import BindingAudit.Images\nimport Extracted\nimport StrictBinding.Evidence\n";
        const string claimsOfEvidence = "(StrictBinding.metadataClaims Extracted.methodEvidence)";
        const string boundEvidence = "StrictBinding.MetadataRowsBound images Extracted.methodEvidence";
        const string bound = "And (StrictBinding.ClaimsHold StrictBinding.assemblyBlockBound images " +
            "(StrictBinding.assemblyBlocks claims))\n" +
            "    (StrictBinding.ClaimsHold StrictBinding.methodMetadataBound images claims)";
        var size = BindingPageSize(methods);
        var source = PagedFactModuleSource(BindingFact.MetadataRows, methods, size).ReplaceLineEndings("\n");
        var pages = BindingPageCount(methods, size);
        // The pages and the distinct-block lemma each name the evidence's metadata list.
        if (!source.StartsWith(imports, StringComparison.Ordinal) ||
            source.Split(claimsOfEvidence).Length != pages + 2 || source.Split(boundEvidence).Length != 2)
            throw new InvalidOperationException("The generated metadata rows module changed its form");
        // Replay checks each lemma in the kernel; elaborating without the option makes the kernel check it here.
        var module = source[imports.Length..].Replace("set_option debug.skipKernelTC true in\n", "")
            .Replace(claimsOfEvidence, "claims", StringComparison.Ordinal)
            .Replace(boundEvidence, bound, StringComparison.Ordinal);
        var perImage = methods / images;
        var files = Enumerable.Range(0, images).Select(image => SyntheticMethods(perImage, "Synthetic" + image))
            .ToArray();
        var definitions = string.Concat(files.Select((file, image) => $$"""
            namespace Image{{image}}
            {{BindingImage.Definitions(file)}}
            def assemblyBlock : CIL.Extraction.AssemblyMetadata :=
              {{StrictBindingFacts.AssemblyBlock(file)}}
            {{string.Concat(Enumerable.Range(1, perImage).Select(row =>
                $"def slice{row} : CIL.Extraction.MetadataSlice :=\n  " +
                StrictBindingFacts.Slice(file, new HashSet<int> { MetadataTokens.GetToken(
                    MetadataTokens.MethodDefinitionHandle(row)) }) +
                $"\ndef method{row} : CIL.Extraction.MethodMetadata := {{ own := slice{row} }}\n"))}}end Image{{image}}

            """));
        // One list per page keeps each list literal within the elaborator's recursion limit.
        var parts = Enumerable.Range(0, images).SelectMany(image => Enumerable.Range(1, perImage)
            .Select(row => $"Image{image}.method{row}")).Chunk(size).ToArray();
        var lists = string.Concat(parts.Select((part, page) =>
            $"def claims{page} : List CIL.Extraction.MethodMetadata :=\n  [{string.Join(", ", part)}]\n"));
        var joined = Enumerable.Range(0, parts.Length - 1).Reverse()
            .Aggregate($"claims{parts.Length - 1}", (rest, page) => $"(claims{page} ++ {rest})");
        var pinned = string.Join(", ", files.Select((file, image) =>
            $"{{ identity := \"{StrictBindingFacts.Identity(file)}\", image := Image{image}.image }}"));
        var name = $"Methods{methods}x{images}";
        var path = Path.Combine(root, $"MetadataRows{methods}x{images}.lean");
        File.WriteAllText(path, $$"""
            import StrictBinding.Evidence

            namespace {{name}}
            {{definitions}}{{lists}}def claims : List CIL.Extraction.MethodMetadata := {{joined}}
            def BindingAudit.images : List StrictBinding.PinnedImage := [{{pinned}}]
            {{report}}
            theorem preparedOnce : StrictBinding.ok (StrictBinding.prepare BindingAudit.images) = true := by
              decide +kernel
            {{report}}
            {{module}}
            {{report}}
            #print axioms BindingAudit.metadataRows
            end {{name}}

            """);
        return CheckHeartbeats(path, package, 1, $"metadata rows of {methods} methods over {images} images")[0];
    }

    /// <summary>A library whose user-string heap holds one repeated UTF-16 string at offset 1.</summary>
    static byte[] SyntheticUserString(int characters)
    {
        var metadata = new MetadataBuilder();
        metadata.AddAssembly(metadata.GetOrAddString("Synthetic"), new Version(1, 2, 3, 4), default, default,
            default, AssemblyHashAlgorithm.Sha1);
        metadata.AddModule(0, metadata.GetOrAddString("Synthetic.dll"), metadata.GetOrAddGuid(Guid.Empty), default,
            default);
        metadata.AddTypeDefinition(default, default, metadata.GetOrAddString("<Module>"), default,
            MetadataTokens.FieldDefinitionHandle(1), MetadataTokens.MethodDefinitionHandle(1));
        var handle = metadata.GetOrAddUserString(new string('A', characters));
        if (MetadataTokens.GetHeapOffset(handle) != 1)
            throw new InvalidOperationException("The synthetic user string must start at heap offset 1.");
        var builder = new ManagedPEBuilder(PEHeaderBuilder.CreateLibraryHeader(), new MetadataRootBuilder(metadata),
            new BlobBuilder());
        var image = new BlobBuilder();
        builder.Serialize(image);
        return image.ToArray();
    }

    /// <summary>
    /// The kernel heartbeats of each case's check above preparing its image, from a module that reports the count
    /// before preparing, after preparing, and after a check that prepares the image again.
    /// </summary>
    static long[] CheckHeartbeats(string path, string package, int cases, string subject)
    {
        var counts = HeartbeatCounts(path, package, 3 * cases, subject);
        return [.. Enumerable.Range(0, cases).Select(index =>
            counts[3 * index + 2] - 2 * counts[3 * index + 1] + counts[3 * index])];
    }

    /// <summary>The heartbeat counts a module reports, of which there must be `reports`, with no sorryAx.</summary>
    static long[] HeartbeatCounts(string path, string package, int reports, string subject)
    {
        // Without the flag the kernel checks on another thread and its heartbeats go uncounted.
        var output = Run(["lake", "env", "lean", "-DElab.async=false", "-M", "8192", path], cwd: package);
        var counts = output.Split('\n').Select(line => line.Trim())
            .Where(line => line.Length > 0 && line.All(char.IsAsciiDigit))
            .Select(line => long.Parse(line, System.Globalization.CultureInfo.InvariantCulture)).ToArray();
        if (counts.Length != reports || output.Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidOperationException($"Unchecked {subject}:\n{output}");
        return counts;
    }

    /// <summary>
    /// The kernel-checked digest proof of a page whose 64 chunks all end in the same 8 bytes costs about what the
    /// proof of the same page with random ends costs. The kernel's caches hash a numeral by its low 64 bits, so
    /// separate chunk numerals that end alike would collide there and make the hash quadratic in the chunks.
    /// </summary>
    static void CheckEqualTailPageCost(string root, string package)
    {
        const int pageBytes = 4096;
        const int chunkBytes = 64;
        const int tailBytes = 8;
        const byte tail = 0xA5;
        const string report = "#eval show IO Nat from IO.getNumHeartbeats\n";
        var distinct = new byte[pageBytes];
        new Random(13).NextBytes(distinct);
        var equal = (byte[])distinct.Clone();
        for (var end = chunkBytes; end <= pageBytes; end += chunkBytes)
            equal.AsSpan(end - tailBytes, tailBytes).Fill(tail);
        (string Name, byte[] Bytes)[] pages = [("RandomEnds", distinct), ("EqualEnds", equal)];
        Directory.CreateDirectory(root);
        var path = Path.Combine(root, "EqualTailPage.lean");
        File.WriteAllText(path, "import StrictBinding.Sha256\nimport CIL.Extraction.FixedDigits\n\n" + report +
            string.Concat(pages.Select(page =>
                $"namespace {page.Name}\n\n{BindingImage.Definitions(page.Bytes)}\n" +
                BindingImage.PagedDigestTheorem(page.Bytes, skipCompileCheck: false) +
                $"end {page.Name}\n\n{report}")));
        var counts = HeartbeatCounts(path, package, pages.Length + 1, "digest proofs of one page");
        var (randomEnds, equalEnds) = (counts[1] - counts[0], counts[2] - counts[1]);
        var measured = $"{equalEnds} heartbeats with equal ends, {randomEnds} with random ends";
        if (randomEnds <= 0 || (double)equalEnds / randomEnds > MaximumEqualTailGrowth)
            throw new InvalidOperationException($"The digest proof of one page costs {measured}");
        Console.WriteLine($"PASS a page whose chunks end alike costs its digest proof what another page costs " +
            $"({measured})");
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
    /// A type definition claim names its row, the NestedClass rows that place it and its base row, so its check reads
    /// a fixed number of cells and entries whatever the size of the tables. Images with 64, 256 and 1024 classes,
    /// half of them nested, beside the types of `SyntheticTypes` are checked against nine claims that
    /// System.Reflection.Metadata reads from them, and the heartbeats of preparing each image are subtracted. The
    /// check at 1024 classes may cost at most `MaximumTableGrowth` times the check at 64. The same images are
    /// checked to have a NestedClass table sorted by its nested type column, which reads every row once: a row added
    /// at the largest size may cost at most `MaximumPerRowGrowth` times a row added at the smaller ones. The
    /// smallest image also rejects claims that each change one part of a claim that holds, a NestedClass row that
    /// repeats its neighbour's type, and a NestedClass table out of order.
    /// </summary>
    static void CheckTypeDefinitionScaling(string root, string package)
    {
        const string report = "#eval show IO Nat from IO.getNumHeartbeats";
        int[] sizes = [64, 256, 1024];
        Run(["lake", "build", "StrictBinding.TypeDefs", "Tests.StrictBinding.Mutation"], package,
            progress: "Building the type definition checks");
        var files = sizes.Select(SyntheticTypes).ToArray();
        var nestedRows = files.Select(NestedTypeRows).ToArray();
        var cases = string.Concat(sizes.Select((size, index) =>
        {
            var file = files[index];
            var identity = StrictBindingFacts.Identity(file);
            var claims = TypeDefinitionClaims(file, identity, nestedRows[index]);
            var rejections = index == 0 ? TypeDefinitionRejections(file, identity, claims, nestedRows[index]) : "";
            return $$"""
                namespace Types{{size}}
                {{BindingImage.Definitions(file)}}
                /-- The synthetic image under its assembly identity. -/
                def pinned : List StrictBinding.PinnedImage := [{ identity := "{{identity}}", image := image }]
                /-- The claimed type definitions, as System.Reflection.Metadata reads them. -/
                def claims : List StrictBinding.TypeDefClaim :=
                  [{{string.Join(",\n   ", claims.Select(claim => claim.Lean))}}]
                {{report}}
                theorem prepared : StrictBinding.ok (StrictBinding.prepare pinned) = true := by decide +kernel
                {{report}}
                theorem checked : StrictBinding.TypeDefsBound pinned claims := by decide +kernel
                {{report}}
                #print axioms checked
                {{rejections}}
                end Types{{size}}

                """;
        }));
        var sorting = string.Concat(sizes.Select((size, index) => $$"""
            namespace Sorted{{size}}
            /-- The NestedClass table of the image is sorted by its nested type column. -/
            def claims : List StrictBinding.SortedClaim := [{ identity := "{{StrictBindingFacts.Identity(files[index])
                }}", table := {{(int)TableIndex.NestedClass}}, key := StrictBinding.nestedClassKey }]
            {{report}}
            theorem prepared : StrictBinding.ok (StrictBinding.prepare Types{{size}}.pinned) = true := by
              decide +kernel
            {{report}}
            theorem checked : StrictBinding.TablesSorted Types{{size}}.pinned claims := by decide +kernel
            {{report}}
            #print axioms checked
            end Sorted{{size}}

            """));
        Directory.CreateDirectory(root);
        var path = Path.Combine(root, "TypeDefs.lean");
        File.WriteAllText(path, $"import StrictBinding.TypeDefs\nimport Tests.StrictBinding.Mutation\n\n{cases}" +
            $"{sorting}{UnsortedNestedClassRejection(files[0])}");
        var measured = CheckHeartbeats(path, package, 2 * sizes.Length, "type definition and sorted table claims");
        long[] checks = measured[..sizes.Length];
        var growth = (double)checks[^1] / checks[0];
        var costs = string.Join(", ", sizes.Zip(checks, (size, cost) => $"{cost} heartbeats at {size} classes"));
        if (checks[0] <= 0 || growth > MaximumTableGrowth)
            throw new InvalidOperationException($"The type definition check costs {costs}; {growth:F2} times as " +
                $"much at {sizes[^1]} classes as at {sizes[0]}");
        Console.WriteLine($"PASS the type definition check reads a fixed part of the tables ({costs}; " +
            $"{growth:F2} times at {sizes[^1] / sizes[0]} times the classes)");
        var sortedCost = RequireGrowth([.. nestedRows.Select(rows => rows.Length)], measured[sizes.Length..],
            MaximumPerRowGrowth, "NestedClass sortedness check", "row");
        Console.WriteLine($"PASS the sortedness check is linear in the NestedClass rows ({sortedCost})");
    }

    /// <summary>The TypeDef rows of the nested types of an image, in ascending order.</summary>
    static int[] NestedTypeRows(byte[] file)
    {
        using var reader = new PEReader(System.Collections.Immutable.ImmutableArray.Create(file));
        var metadata = reader.GetMetadataReader();
        int[] rows = [.. metadata.TypeDefinitions.Where(handle => !metadata.GetTypeDefinition(handle)
            .GetDeclaringType().IsNil).Select(handle => MetadataTokens.GetRowNumber(handle)).Order()];
        if (rows.Length != metadata.GetTableRowCount(TableIndex.NestedClass))
            throw new InvalidOperationException("Each synthetic nested type must own exactly one NestedClass row.");
        return rows;
    }

    /// <summary>
    /// The image with the nested type column of NestedClass row `nestedRow` set to TypeDef row `typeRow`, at the
    /// position System.Reflection.Metadata gives the table.
    /// </summary>
    static byte[] WithNestedType(byte[] file, int nestedRow, int typeRow)
    {
        using var reader = new PEReader(System.Collections.Immutable.ImmutableArray.Create(file));
        var metadata = reader.GetMetadataReader();
        if (metadata.GetTableRowCount(TableIndex.TypeDef) >= 1 << 16)
            throw new InvalidOperationException("The nested type column must be two bytes wide.");
        var offset = reader.PEHeaders.MetadataStartOffset + metadata.GetTableMetadataOffset(TableIndex.NestedClass) +
            (nestedRow - 1) * metadata.GetTableRowSize(TableIndex.NestedClass);
        var changed = (byte[])file.Clone();
        changed[offset] = (byte)typeRow;
        changed[offset + 1] = (byte)(typeRow >> 8);
        return changed;
    }

    /// <summary>
    /// The image with NestedClass row 2 naming TypeDef row 1, below the type row 1 names, is refused as unsorted at
    /// row 2.
    /// </summary>
    static string UnsortedNestedClassRejection(byte[] file)
    {
        var changed = WithNestedType(file, 2, 1);
        var identity = StrictBindingFacts.Identity(changed);
        return $$"""
            namespace Unsorted
            {{BindingImage.Definitions(changed)}}
            theorem rejects_a_nested_class_table_out_of_order : Tests.StrictBinding.failsWith
                (StrictBinding.checkAll StrictBinding.sortedClaimBound
                  [{ identity := "{{identity}}", image := image }]
                  [{ identity := "{{identity}}", table := {{(int)TableIndex.NestedClass}},
                     key := StrictBinding.nestedClassKey }])
                (.unsortedTable {{(int)TableIndex.NestedClass}} 2) = true := by decide +kernel
            #print axioms rejects_a_nested_class_table_out_of_order
            end Unsorted

            """;
    }

    /// <summary>A type definition claim: its row, name, kind and enclosing row, and the claim in Lean.</summary>
    sealed record TypeDefinitionClaim(int Row, string Name, string Kind, int? Enclosing, string Lean);

    /// <summary>
    /// Claims about the first class and the last eight rows of an image from `SyntheticTypes`, with every part read
    /// by System.Reflection.Metadata. A nested type is placed at its NestedClass row and a type at the top level
    /// between the rows that name lower and higher types, given `nestedRows`, the ascending nested type rows.
    /// </summary>
    static TypeDefinitionClaim[] TypeDefinitionClaims(byte[] file, string identity, int[] nestedRows)
    {
        using var reader = new PEReader(System.Collections.Immutable.ImmutableArray.Create(file));
        var metadata = reader.GetMetadataReader();
        var rows = metadata.GetTableRowCount(TableIndex.TypeDef);
        int[] claimed = [2, .. Enumerable.Range(rows - 7, 8)];
        string Bytes(StringHandle text) =>
            "[" + string.Join(", ", System.Text.Encoding.UTF8.GetBytes(metadata.GetString(text))) + "]";
        (string Namespace, string Name) NamesOf(EntityHandle handle) => handle.Kind switch
        {
            HandleKind.TypeDefinition => (metadata.GetString(metadata.GetTypeDefinition((TypeDefinitionHandle)handle)
                .Namespace), metadata.GetString(metadata.GetTypeDefinition((TypeDefinitionHandle)handle).Name)),
            HandleKind.TypeReference => (metadata.GetString(metadata.GetTypeReference((TypeReferenceHandle)handle)
                .Namespace), metadata.GetString(metadata.GetTypeReference((TypeReferenceHandle)handle).Name)),
            _ => ("", "")
        };
        string Ascii(string text) => "[" + string.Join(", ", System.Text.Encoding.UTF8.GetBytes(text)) + "]";
        return [.. claimed.Select(row =>
        {
            var definition = metadata.GetTypeDefinition(MetadataTokens.TypeDefinitionHandle(row));
            var fields = definition.GetFields();
            if (fields.Count == 0)
                throw new InvalidOperationException($"Synthetic TypeDef row {row} must own a field.");
            var first = MetadataTokens.GetRowNumber(fields.First());
            var baseType = definition.BaseType;
            var (baseNamespace, baseName) = baseType.IsNil ? ("", "") : NamesOf(baseType);
            var isInterface = (definition.Attributes & TypeAttributes.Interface) != 0;
            var isEnumItself = (metadata.GetString(definition.Namespace), metadata.GetString(definition.Name)) ==
                ("System", "Enum");
            var kind = isInterface ? "interface"
                : (baseNamespace, baseName) == ("System", "Enum") ? "enum"
                : (baseNamespace, baseName) == ("System", "ValueType") && !isEnumItself ? "valueType"
                : "classType";
            var declaring = definition.GetDeclaringType();
            int? enclosing = declaring.IsNil ? null : MetadataTokens.GetRowNumber(declaring);
            var nesting = enclosing is { } outer ? $".nested {Array.IndexOf(nestedRows, row) + 1} {outer}"
                : $".topLevel {nestedRows.Count(nested => nested < row) + 1}";
            var baseTerm = baseType.IsNil ? ".none"
                : baseType.Kind == HandleKind.TypeSpecification ? $".spec {MetadataTokens.GetToken(baseType)}"
                : $".named {MetadataTokens.GetToken(baseType)} {Ascii(baseNamespace)} {Ascii(baseName)}";
            return new TypeDefinitionClaim(row, metadata.GetString(definition.Name), kind, enclosing,
                $"{{ identity := \"{identity}\", row := {row}, typeNamespace := {Bytes(definition.Namespace)}, " +
                $"typeName := {Bytes(definition.Name)}, nesting := {nesting}, kind := .{kind}, " +
                $"fields := ({first}, {fields.Count}), base := {baseTerm} }}");
        })];
    }

    /// <summary>
    /// Rejections that each change one part of a claim that holds: a nested class claimed at the top level, at
    /// another NestedClass row and inside another row, the first class claimed nested, `System.Enum` claimed between
    /// other NestedClass rows and claimed a value type, the interface claimed a class, the class over a generic
    /// instantiation claimed to extend another TypeSpec row, and the last row claimed to extend another TypeDef.
    /// The image whose NestedClass row before the last names the last row's type too refuses the last nested class.
    /// </summary>
    static string TypeDefinitionRejections(byte[] file, string identity, TypeDefinitionClaim[] claims,
        int[] nestedRows)
    {
        var nested = Array.FindIndex(claims, claim => claim.Name == "Inner");
        var lastNested = Array.FindIndex(claims, claim => claim.Name == "Inner2");
        var face = Array.FindIndex(claims, claim => claim.Kind == "interface");
        var enumItself = Array.FindIndex(claims, claim => claim.Name == "Enum");
        var instantiated = Array.FindIndex(claims, claim => claim.Name == "Numbers");
        var last = claims.Length - 1;
        string Rejects(string name, int index, string change, string part) => $$"""
            theorem {{name}} : Tests.StrictBinding.failsWith (StrictBinding.checkAll
                StrictBinding.typeDefClaimBound pinned
                [{ ({{claims[index].Lean}} : StrictBinding.TypeDefClaim) with {{change}} }])
                (.typeDefMismatch {{claims[index].Row}} .{{part}}) = true := by decide +kernel
            #print axioms {{name}}

            """;
        var nestedRow = Array.IndexOf(nestedRows, claims[nested].Row) + 1;
        var lastRow = Array.IndexOf(nestedRows, claims[lastNested].Row) + 1;
        var duplicated = WithNestedType(file, lastRow - 1, claims[lastNested].Row);
        return Rejects("rejects_a_nested_class_at_the_top_level", nested, $"nesting := .topLevel {nestedRow}",
                "nesting") +
            Rejects("rejects_another_nested_class_row", lastNested,
                $"nesting := .nested {lastRow - 1} {claims[lastNested].Enclosing}", "nesting") +
            Rejects("rejects_another_enclosing_row", nested,
                $"nesting := .nested {nestedRow} {claims[nested].Enclosing + 1}", "nesting") +
            Rejects("rejects_a_top_level_class_claimed_nested", 0, "nesting := .nested 1 2", "nesting") +
            Rejects("rejects_a_bracket_that_does_not_hold", enumItself,
                $"nesting := .topLevel {lastRow + 1}", "nesting") +
            $$"""
            namespace Duplicated
            {{BindingImage.Definitions(duplicated)}}
            /-- NestedClass row {{lastRow - 1}} names TypeDef row {{claims[lastNested].Row}}, as the next row does. -/
            theorem rejects_a_nested_class_with_two_rows : Tests.StrictBinding.failsWith (StrictBinding.checkAll
                StrictBinding.typeDefClaimBound [{ identity := "{{identity}}", image := image }]
                [{{claims[lastNested].Lean}}])
                (.typeDefMismatch {{claims[lastNested].Row}} .nesting) = true := by decide +kernel
            #print axioms rejects_a_nested_class_with_two_rows
            end Duplicated

            """ +
            Rejects("rejects_an_interface_claimed_a_class", face, "kind := .classType", "kind") +
            Rejects("rejects_system_enum_claimed_a_value_type", enumItself, "kind := .valueType", "kind") +
            Rejects("rejects_another_type_spec", instantiated,
                $"base := .spec {MetadataTokens.GetToken(MetadataTokens.TypeSpecificationHandle(2))}", "base") +
            Rejects("rejects_another_base_definition", last,
                $"base := .named {MetadataTokens.GetToken(MetadataTokens.TypeDefinitionHandle(3))} [] []", "base");
    }

    /// <summary>
    /// A library with `count` classes that each own a field and extend `System.Object`, the odd ones nested in the
    /// first, then an enum, a struct, an interface, a class nested in the first class, a `System.Enum` that extends
    /// `System.ValueType`, a second class nested in the first, a class that extends `List&lt;int&gt;` and a class that
    /// extends the first class. Each of the last eight owns one field, and the last owns the final two rows of the
    /// Field table.
    /// </summary>
    static byte[] SyntheticTypes(int count)
    {
        var metadata = new MetadataBuilder();
        metadata.AddAssembly(metadata.GetOrAddString("Synthetic"), new Version(1, 2, 3, 4), default, default, default,
            AssemblyHashAlgorithm.Sha1);
        metadata.AddModule(0, metadata.GetOrAddString("Synthetic.dll"), metadata.GetOrAddGuid(Guid.Empty), default,
            default);
        var runtime = metadata.AddAssemblyReference(metadata.GetOrAddString("System.Runtime"),
            new Version(10, 0, 0, 0), default, default, default, default);
        TypeReferenceHandle SystemType(string name) =>
            metadata.AddTypeReference(runtime, metadata.GetOrAddString("System"), metadata.GetOrAddString(name));
        var objectType = SystemType("Object");
        var enumType = SystemType("Enum");
        var valueType = SystemType("ValueType");
        var signature = new BlobBuilder();
        new BlobEncoder(signature).Field().Type().Int32();
        var fieldSignature = metadata.GetOrAddBlob(signature);
        var listType = metadata.AddTypeReference(runtime, metadata.GetOrAddString("System.Collections.Generic"),
            metadata.GetOrAddString("List`1"));
        var instance = new BlobBuilder();
        new BlobEncoder(instance).TypeSpecificationSignature().GenericInstantiation(listType, 1, false).AddArgument()
            .Int32();
        var listOfInt = metadata.AddTypeSpecification(metadata.GetOrAddBlob(instance));
        var fields = 0;
        var typeNamespace = metadata.GetOrAddString("Synthetic");
        TypeDefinitionHandle Define(TypeAttributes attributes, StringHandle space, string name, EntityHandle baseType,
            int owned)
        {
            var first = MetadataTokens.FieldDefinitionHandle(fields + 1);
            for (var index = 0; index < owned; index++)
                metadata.AddFieldDefinition(FieldAttributes.Public, metadata.GetOrAddString("F" + (fields + index)),
                    fieldSignature);
            fields += owned;
            return metadata.AddTypeDefinition(attributes, space, metadata.GetOrAddString(name), baseType, first,
                MetadataTokens.MethodDefinitionHandle(1));
        }
        metadata.AddTypeDefinition(default, default, metadata.GetOrAddString("<Module>"), default,
            MetadataTokens.FieldDefinitionHandle(1), MetadataTokens.MethodDefinitionHandle(1));
        var firstClass = Define(TypeAttributes.Public, typeNamespace, "C0", objectType, 1);
        for (var index = 1; index < count; index++)
        {
            var odd = index % 2 == 1;
            var defined = Define(odd ? TypeAttributes.NestedPublic : TypeAttributes.Public,
                odd ? default : typeNamespace, "C" + index, objectType, 1);
            if (odd)
                metadata.AddNestedType(defined, firstClass);
        }
        Define(TypeAttributes.Public | TypeAttributes.Sealed, typeNamespace, "Small", enumType, 1);
        Define(TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout, typeNamespace, "Pair",
            valueType, 1);
        Define(TypeAttributes.Public | TypeAttributes.Interface | TypeAttributes.Abstract, typeNamespace, "IShape",
            default, 1);
        var nestedClass = Define(TypeAttributes.NestedPublic, default, "Inner", objectType, 1);
        metadata.AddNestedType(nestedClass, firstClass);
        Define(TypeAttributes.Public | TypeAttributes.Abstract, metadata.GetOrAddString("System"), "Enum", valueType,
            1);
        metadata.AddNestedType(Define(TypeAttributes.NestedPublic, default, "Inner2", objectType, 1), firstClass);
        Define(TypeAttributes.Public, typeNamespace, "Numbers", listOfInt, 1);
        Define(TypeAttributes.Public, typeNamespace, "Derived", firstClass, 2);
        var builder = new ManagedPEBuilder(PEHeaderBuilder.CreateLibraryHeader(), new MetadataRootBuilder(metadata),
            new BlobBuilder());
        var image = new BlobBuilder();
        builder.Serialize(image);
        return image.ToArray();
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
    /// A library named `name` with `count` MethodDef rows without bodies, each named for its row and all with one
    /// signature.
    /// </summary>
    static byte[] SyntheticMethods(int count, string name = "Synthetic")
    {
        var metadata = new MetadataBuilder();
        var assemblyName = metadata.GetOrAddString(name);
        metadata.AddAssembly(assemblyName, new Version(1, 2, 3, 4), default, default, default,
            AssemblyHashAlgorithm.Sha1);
        metadata.AddModule(0, metadata.GetOrAddString(name + ".dll"), metadata.GetOrAddGuid(Guid.Empty), default,
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
    /// Elaborates each paged module the audit generates, also over an extraction with no methods, so a malformed
    /// declaration in the generator fails here and not only in an end-to-end audit.
    /// </summary>
    static void CheckGeneratedPagedModulesElaborate(string root, string package)
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
        foreach (var fact in PagedFacts)
            foreach (var (methods, size) in new[] { (3, 1), (0, BindingPageSize(0)) })
            {
                var source = PagedFactModuleSource(fact, methods, size).ReplaceLineEndings("\n");
                if (!source.StartsWith(imports, StringComparison.Ordinal))
                    throw new InvalidOperationException(
                        $"The generated {fact} module no longer starts with its imports");
                var path = Path.Combine(root, $"Generated{fact}{methods}.lean");
                File.WriteAllText(path, stubs.ReplaceLineEndings("\n") + source[imports.Length..]);
                var run = Execute(["lake", "env", "lean", path], cwd: package);
                if (run.Code != 0)
                    throw new InvalidOperationException(
                        $"The generated {fact} module for {methods} methods does not elaborate: {run.Output}");
            }
        Console.WriteLine("PASS each generated paged module elaborates, also for no methods");
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
            import CIL.Extraction.FixedDigits

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
