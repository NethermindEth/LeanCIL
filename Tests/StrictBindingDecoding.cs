using System.Collections;
using System.Collections.Immutable;
using System.Reflection;
using System.Reflection.Emit;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.RegularExpressions;
using MethodDefinition = Mono.Cecil.MethodDefinition;
using ModuleDefinition = Mono.Cecil.ModuleDefinition;

partial class Program
{
    /// <summary>The checked-in Lean module that holds the fixture image.</summary>
    static string Fixture => At("Tests/StrictBinding/Fixture.lean");

    /// <summary>
    /// The container, table positions, heaps, method body offsets and identity that Lean decodes from an
    /// image, compared line by line with System.Reflection.Metadata on the same bytes: Examples.dll, the
    /// checked-in fixture and the platform reference assembly System.Runtime.
    /// </summary>
    static void CheckBindingDecoding(string root)
    {
        // The checked-in module is what its own image generates, so its expected facts are the reader's.
        var fixtureText = File.ReadAllText(Fixture);
        var fixtureImage = StrictBindingFacts.ReadImage(fixtureText);
        if (StrictBindingFacts.Module(fixtureImage) != fixtureText.ReplaceLineEndings("\n"))
            throw new InvalidOperationException(Fixture + " is not what its image generates; run " +
                "`dotnet run --file Tests/StrictBindingFixture.cs -- --update`.");
        RequireBoundedDigestLemmas();
        (string Name, byte[] Bytes)[] images =
        [
            ("Examples.dll", File.ReadAllBytes(At("Examples/Assembly/bin/Examples.dll"))),
            ("the strict binding fixture", fixtureImage),
            ("the System.Runtime reference assembly", File.ReadAllBytes(PlatformReference()))
        ];
        var package = FixturePackage();
        Run(["lake", "build", "StrictBinding"], package, progress: "Building the strict binding library");
        Directory.CreateDirectory(root);
        RequireLargeDigestToElaborate(root, package);
        for (var index = 0; index < images.Length; index++)
        {
            var (name, bytes) = images[index];
            var path = Path.Combine(root, $"Describe{index}.lean");
            File.WriteAllText(path, DescribeModule(bytes));
            var (code, output, stdout, _) = Execute(["lake", "env", "lean", "--run", path], cwd: package);
            if (code != 0) throw new InvalidOperationException($"Lean could not describe {name}: {output}");
            string[] lean = stdout.ReplaceLineEndings("\n").Split('\n', StringSplitOptions.RemoveEmptyEntries);
            string[] expected = [.. StrictBindingFacts.Read(bytes).Select(fact => fact.Line())];
            var mismatch = Enumerable.Range(0, Math.Min(lean.Length, expected.Length))
                .FirstOrDefault(line => lean[line] != expected[line], -1);
            if (mismatch >= 0 || lean.Length != expected.Length)
                throw new InvalidOperationException($"Lean and System.Reflection.Metadata disagree on {name}: " +
                    $"{lean.Length} and {expected.Length} lines" +
                    (mismatch < 0 ? "" : $"; line {mismatch + 1} is '{lean[mismatch]}' and '{expected[mismatch]}'"));
            Console.WriteLine($"PASS Lean decodes {name} as System.Reflection.Metadata does: {lean.Length} facts");
        }
    }

    /// <summary>
    /// Kernel memory for hashing is bounded by the block count of one lemma, so a generated digest proof states one
    /// lemma per page of 64 chunks, however large the file, and one evaluation of a whole file is refused.
    /// </summary>
    static void RequireBoundedDigestLemmas()
    {
        var file = new byte[3 * 4096 + 100];
        new Random(7).NextBytes(file);
        var proof = BindingImage.PagedDigestTheorem(file, skipCompileCheck: true);
        var definitions = BindingImage.Definitions(file);
        var lemmas = HashLemma().Count(proof);
        var longest = PageChunkCount().Matches(definitions).Max(page => int.Parse(page.Groups[1].Value,
            System.Globalization.CultureInfo.InvariantCulture));
        if (lemmas != 4 || longest > 64)
            throw new InvalidOperationException(
                $"Digest proof is not one lemma per page: {lemmas} lemmas, {longest} chunks");
        try { BindingImage.SingleDigestTheorem(file); }
        catch (ArgumentException)
        {
            Console.WriteLine("PASS digest proofs state one lemma per page of 64 chunks");
            return;
        }
        throw new InvalidOperationException("Whole-file kernel hashing was accepted");
    }

    /// <summary>
    /// A digest proof of a file of 210 pages, about the size of a platform reference assembly, elaborates: the
    /// chain of page lemmas has no term nested more deeply than one level. Only elaboration runs, since replay
    /// costs minutes.
    /// </summary>
    static void RequireLargeDigestToElaborate(string root, string package)
    {
        var file = new byte[210 * 4096 - 17];
        new Random(11).NextBytes(file);
        var path = Path.Combine(root, "LargeDigest.lean");
        File.WriteAllText(path, "import StrictBinding.Sha256\nimport CIL.Extraction.FixedDigits\n\n" +
            "namespace Large\n\n" + BindingImage.Definitions(file) + "\n" +
            BindingImage.PagedDigestTheorem(file, skipCompileCheck: true) + "end Large\n");
        var run = Execute(["lake", "env", "lean", path], cwd: package);
        if (run.Code != 0)
            throw new InvalidOperationException("A digest of 210 pages did not elaborate: " + run.Output);
        Console.WriteLine("PASS a digest proof of 210 pages elaborates");
    }

    /// <summary>
    /// The slices the extractor carries for every method with a body in each selected assembly, with the operand
    /// and local signature tokens of the body, hold the images' rows and heap entries, including user strings.
    /// Lean checks each complete slice in the image its identity pins. Together they carry rows of every table
    /// a slice may carry and at least one omitted-entry marker, so neither is left unchecked.
    /// </summary>
    static void CheckExtractedSlices(string root, string package,
        params (string Selected, string[] References)[] extractions)
    {
        const BindingFlags Internal = BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.Public;
        var extractor = Assembly.LoadFrom(ExtractorPath);
        var pinnedType = extractor.GetType("Nethermind.LeanCIL.PinnedAssemblies", throwOnError: true)!;
        var sourceType = pinnedType.GetNestedType("Source", BindingFlags.NonPublic | BindingFlags.Public)!;
        var slicesType = extractor.GetType("Nethermind.LeanCIL.MetadataSlices", throwOnError: true)!;
        var objectType = extractor.GetType("Nethermind.LeanCIL.ObjectTypes", throwOnError: true)!
            .GetMethod("Is", BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.Public)!;
        HashSet<int> tables = [];
        var markers = 0;
        var userStrings = 0;
        Directory.CreateDirectory(root);
        for (var index = 0; index < extractions.Length; index++)
        {
            var (selected, references) = extractions[index];
            var sources = (IList)Activator.CreateInstance(typeof(List<>).MakeGenericType(sourceType))!;
            foreach (var reference in references) sources.Add(Activator.CreateInstance(sourceType, reference, null)!);
            using var pinned = (IDisposable)Activator.CreateInstance(pinnedType, Internal, null,
                [File.ReadAllBytes(selected), Sha(selected), sources, null], null)!;
            var slices = Activator.CreateInstance(slicesType, pinned)!;
            var modules = ((IEnumerable<ModuleDefinition>)pinnedType.GetProperty("Modules", Internal)!
                .GetValue(pinned)!).ToArray();
            var original = (ModuleDefinition)pinnedType.GetMethod("Original", Internal)!.Invoke(pinned, [modules[0]])!;
            var collect = slicesType.GetMethod("Method", Internal)!;
            var block = slicesType.GetMethod("AssemblyBlock", Internal)!;
            List<string> methods = [];
            foreach (var (token, tokens) in BodyTokens(File.ReadAllBytes(selected)))
            {
                var method = (MethodDefinition)original.LookupToken((int)token);
                // As the extractor decides it for a method's evidence: an instance method of a class.
                var classOwner = method.HasThis && (bool)objectType.Invoke(null, [method.DeclaringType])!;
                var (metadata, _, _) =
                    ((string, string, int[]))collect.Invoke(slices, [method, tokens, classOwner])!;
                methods.Add($"(\"{method.FullName}\", {metadata})");
            }
            string[] paths = [selected, .. references];
            var path = Path.Combine(root, $"Slices{index}.lean");
            File.WriteAllText(path, SlicesModule([.. paths.Select(File.ReadAllBytes)],
                [.. modules.Select(module => (string)block.Invoke(slices, [module])!)], methods));
            var (code, output, stdout, _) = Execute(["lake", "env", "lean", "--run", path], cwd: package);
            string[] lines = stdout.ReplaceLineEndings("\n").Split('\n', StringSplitOptions.RemoveEmptyEntries);
            var refused = lines.Where(line => !line.StartsWith("ok ", StringComparison.Ordinal)).ToArray();
            if (code != 0 || refused.Length != 0 || lines.Length != methods.Count)
                throw new InvalidOperationException($"Lean refused the slices of {Path.GetFileName(selected)}: " +
                    (refused.Length == 0 ? output : string.Join("\n", refused)));
            var counts = lines.Select(line => line.Split(' ')).Select(words =>
                (Slices: int.Parse(words[1]), Rows: int.Parse(words[2]), Markers: int.Parse(words[3]),
                    Tables: words[4].Split(',', StringSplitOptions.RemoveEmptyEntries).Select(int.Parse),
                    UserStrings: int.Parse(words[5]))).ToArray();
            if (counts.Sum(count => count.Rows) == 0)
                throw new InvalidOperationException($"No slice of {Path.GetFileName(selected)} carries a row.");
            tables.UnionWith(counts.SelectMany(count => count.Tables));
            markers += counts.Sum(count => count.Markers);
            userStrings += counts.Sum(count => count.UserStrings);
            Console.WriteLine($"PASS Lean matches the slices of {methods.Count} methods of " +
                $"{Path.GetFileName(selected)} to their images: {counts.Sum(count => count.Slices)} slices, " +
                $"{counts.Sum(count => count.Rows)} rows, {counts.Sum(count => count.Markers)} marker cells, " +
                $"{counts.Sum(count => count.UserStrings)} user strings");
        }
        var missing = CarriedTables.Except(tables).ToArray();
        if (missing.Length != 0 || markers == 0 || userStrings == 0)
            throw new InvalidOperationException("The extracted slices leave unchecked: " +
                string.Join(", ", missing.Select(table => $"table 0x{table:X2}")) +
                (markers == 0 ? " omitted-entry markers" : "") + (userStrings == 0 ? " user strings" : ""));
        Console.WriteLine($"PASS the extracted slices carry rows of all {CarriedTables.Length} tables and " +
            $"{markers} marker cells and {userStrings} user strings");
    }

    /// <summary>The tables whose rows a metadata slice carries.</summary>
    static readonly int[] CarriedTables = [0x01, 0x02, 0x04, 0x06, 0x0A, 0x11, 0x1B, 0x23, 0x29, 0x2A, 0x2B];

    /// <summary>
    /// The MethodDef token of every method with a body, with the tokens its instructions name and its local
    /// signature token, read from the IL bytes as the extractor reads them.
    /// </summary>
    static IEnumerable<(uint Method, uint[] Tokens)> BodyTokens(byte[] file)
    {
        var opcodes = typeof(OpCodes).GetFields(BindingFlags.Public | BindingFlags.Static)
            .Select(field => (OpCode)field.GetValue(null)!).ToDictionary(code => (ushort)code.Value);
        using PEReader pe = new(ImmutableArray.Create(file));
        var reader = pe.GetMetadataReader();
        foreach (var handle in reader.MethodDefinitions)
        {
            var rva = reader.GetMethodDefinition(handle).RelativeVirtualAddress;
            if (rva == 0) continue;
            var body = pe.GetMethodBody(rva);
            var il = body.GetILBytes()!;
            List<uint> tokens = [];
            for (var at = 0; at < il.Length;)
            {
                int value = il[at++];
                if (value == TwoByteOpcode) value = value << 8 | il[at++];
                var operand = opcodes[(ushort)value].OperandType;
                if (operand is OperandType.InlineField or OperandType.InlineMethod or OperandType.InlineSig or
                    OperandType.InlineTok or OperandType.InlineType or OperandType.InlineString)
                    tokens.Add(BitConverter.ToUInt32(il, at));
                at += operand switch
                {
                    OperandType.InlineNone => 0,
                    OperandType.ShortInlineBrTarget or OperandType.ShortInlineI or OperandType.ShortInlineVar => 1,
                    OperandType.InlineVar => 2,
                    OperandType.InlineI8 or OperandType.InlineR => 8,
                    OperandType.InlineSwitch => 4 + 4 * BitConverter.ToInt32(il, at),
                    _ => 4
                };
            }
            if (!body.LocalSignature.IsNil)
                tokens.Add((uint)MetadataTokens.GetToken(body.LocalSignature));
            yield return ((uint)MetadataTokens.GetToken(handle), [.. tokens]);
        }
    }

    // The first byte of a two-byte opcode.
    const int TwoByteOpcode = 0xFE;

    /// <summary>
    /// A program that checks each method's slices against the pinned images and prints, per method, `ok`, its
    /// slice, row and marker cell counts, the tables of its rows and its name, or its name and the audit error.
    /// </summary>
    static string SlicesModule(byte[][] images, string[] blocks, List<string> methods)
    {
        var text = new StringBuilder("import StrictBinding.Slice\n\n");
        for (var index = 0; index < images.Length; index++)
            text.Append($"namespace Image{index}\n\n{BindingImage.Definitions(images[index])}\nend Image{index}\n\n");
        text.Append("open StrictBinding CIL.Extraction\n\ndef images : List PinnedImage :=\n  [");
        text.Append(string.Join(",\n   ", images.Select((image, index) =>
            $"{{ identity := \"{StrictBindingFacts.Identity(image)}\", image := Image{index}.image }}")));
        text.Append("]\n\n");
        for (var index = 0; index < blocks.Length; index++)
            text.Append($"def assembly{index}Metadata : AssemblyMetadata := {blocks[index]}\n\n");
        text.Append("def methods : List (String × MethodMetadata) :=\n  [");
        text.Append(string.Join(",\n   ", methods)).Append("]\n\n");
        text.Append("""
            def checkSlice (prepared : List PreparedImage) (slice : MetadataSlice) : Except AuditError Unit := do
              let image ← located prepared slice.assembly.identity
              StrictBinding.sliceBound image slice

            def markerCells (prepared : List PreparedImage) (slice : MetadataSlice) : Nat :=
              match located prepared slice.assembly.identity with
              | .error _ => 0
              | .ok image => (slice.rows.map fun row =>
                  match image.columnsOf (row.1 / 2 ^ 24) with
                  | none => 0
                  | some columns =>
                    ((rowKeys stringsHeap columns row.2).filter (· == omittedKey (stringWidth image))).length +
                      ((rowKeys blobHeap columns row.2).filter (· == omittedKey (blobWidth image))).length).sum

            def main : IO UInt32 := do
              match prepare images with
              | .error error =>
                IO.eprintln (repr error)
                pure 1
              | .ok prepared =>
                for (name, metadata) in methods do
                  let slices := metadata.own :: metadata.others
                  match slices.forM (checkSlice prepared) with
                  | .ok _ =>
                    let rows := slices.flatMap (·.rows)
                    let tables := (rows.map (·.1 / 2 ^ 24)).eraseDups.map toString
                    let markers := (slices.map (markerCells prepared)).sum
                    let userStrings := (slices.map (fun slice => slice.userStrings.length)).sum
                    IO.println
                      (s!"ok {slices.length} {rows.length} {markers} {",".intercalate tables} " ++
                        s!"{userStrings} {name}")
                  | .error error => IO.println s!"{name}: {repr error}"
                pure 0

            """);
        return text.ToString();
    }

    /// <summary>A program that prints the description of an image the audit decodes, one fact per line.</summary>
    static string DescribeModule(byte[] file) => $$"""
        import StrictBinding.Dump
        import CIL.Extraction.FixedDigits

        namespace StrictDescribe

        {{BindingImage.Definitions(file)}}
        end StrictDescribe

        def main : IO UInt32 := do
          match StrictBinding.describe StrictDescribe.image with
          | .ok lines =>
            lines.forM IO.println
            pure 0
          | .error error =>
            IO.eprintln (repr error)
            pure 1
        """;

    /// <summary>The newest platform reference assembly System.Runtime of the .NET 11 reference pack.</summary>
    static string PlatformReference()
    {
        var runtime = Path.GetFullPath(Path.Combine(RuntimeEnvironment.GetRuntimeDirectory(), "..", "..", ".."));
        var packs = Path.Combine(Environment.GetEnvironmentVariable("DOTNET_ROOT") ?? runtime, "packs",
            "Microsoft.NETCore.App.Ref");
        return Directory.EnumerateDirectories(packs, "11.*")
            .Select(directory => Path.Combine(directory, "ref", "net11.0", "System.Runtime.dll")).Where(File.Exists)
            .OrderByDescending(path => Version.Parse(Path.GetFileName(
                Path.GetDirectoryName(Path.GetDirectoryName(Path.GetDirectoryName(path)))!)))
            .FirstOrDefault() ?? throw new FileNotFoundException("No .NET 11 reference pack under " + packs);
    }

    [GeneratedRegex(@"(?m)^def page\d+ : List Nat := CIL\.Extraction\.fixedDigitsWithin 512 (\d+) ")]
    private static partial Regex PageChunkCount();

    [GeneratedRegex(@"(?m)^set_option debug\.skipKernelTC true in\ntheorem hash\d+ ")]
    private static partial Regex HashLemma();
}
