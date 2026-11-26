using System.Text.Json;
using Nethermind.LeanCIL;

partial class Program
{
    /// <summary>Check callable slots across profiles and the decoded code and links at equal flags.</summary>
    internal static void CheckTemplateBodies(string decoderInputs, string space,
        List<(string Identity, string Left, string Right)> comparisons,
        List<(string Identity, string Left, string Right)> slots)
    {
        using var verifier = new Program();
        var session = verifier.Library(CommonInputs());
        var checks = comparisons.Select(pair =>
            $"MethodBinding.firstCodeOrLinkDifference {pair.Left} {pair.Right}");
        var slotChecks = slots.Select(pair =>
            $"({pair.Left}.localKinds == {pair.Right}.localKinds && {pair.Left}.parameterHomes == {pair.Right}.parameterHomes)");
        const string slotMarker = "template storage ";
        const string marker = "template differences ";
        var query = $"""
            import CIL.MethodBinding
            {decoderInputs}
            #eval IO.println ("{slotMarker}" ++ (Lean.toJson
              ([{string.Join(",\n    ", slotChecks)}] : List Bool)).compress)
            #eval IO.println ("{marker}" ++ (Lean.toJson
              ([{string.Join(",\n    ", checks)}] : List (Option Nat))).compress)
            end {space}
            """;
        var probe = Path.Combine(session, "TemplateComparisons.lean");
        File.WriteAllText(probe, query);
        var output = Run([verifier.LeanExecutable, probe], cwd: session, leanPath: verifier.SessionLeanPath(session));
        var lines = output.Split('\n');
        var slotLine = lines.Single(line => line.StartsWith(slotMarker, StringComparison.Ordinal));
        var sameSlots = JsonSerializer.Deserialize<bool[]>(slotLine[slotMarker.Length..]);
        if (sameSlots is null || sameSlots.Length != slots.Count)
            throw new InvalidDataException("Lean did not compare every callable frame.");
        for (var index = 0; index < sameSlots.Length; index++)
            if (!sameSlots[index])
                throw new InvalidDataException("Template metadata or instruction count differs between profiles: " +
                    slots[index].Identity);
        var line = lines.Single(line => line.StartsWith(marker, StringComparison.Ordinal));
        var differences = JsonSerializer.Deserialize<int?[]>(line[marker.Length..]);
        if (differences is null || differences.Length != comparisons.Count)
            throw new InvalidDataException("Lean did not compare every requested template alternative.");
        for (var index = 0; index < differences.Length; index++)
            if (differences[index] is int pc)
                throw new InvalidDataException("Profiles with identical observed flags emit different " +
                    $"instructions: {comparisons[index].Identity} at pc {pc}");
    }

    /// <summary>
    /// The appended CoreLib rows of a bound extraction as template methods, each with its signature and raw opcodes
    /// from its image definition and the method indices its decoded links name, and the signatures of the image's
    /// getter declarations that follow them in the call table, read from Lean.
    /// </summary>
    internal static (TemplateEmitter.Method[] Rows, string[] Declarations) ImageRowTemplates(string decoderInputs,
        int locals, int count)
    {
        using var verifier = new Program();
        var session = verifier.Library(CommonInputs());
        var rows = Enumerable.Range(0, count).Select(row => $"""
            (((constructorImage.methods[{row}]?).bind fun row => Extraction.spelled? row.1.names.signature),
              ((constructorImage.methods[{row}]?).map fun row => row.2.code.map (·.opcode)).getD [],
              linked method{locals + row}, method{locals + row}.staticSites.isEmpty)
            """);
        const string marker = "image rows ";
        const string declarationMarker = "image declarations ";
        var query = $"""
            import CIL.Runtime.Net11WinX64.RangeConstructor
            import CIL.Extraction.TemplateCode
            namespace ImageRows
            open CIL
            {decoderInputs}
            /-- Every method index a decoded method's links name, including the target of an `ldftn`. -/
            def linked (method : Method) : List Nat :=
              method.links.flatMap fun (_, link) => match link with
                | .address target => [target]
                | other => other.callees
            #eval IO.println ("{marker}" ++ (Lean.toJson
              ([{string.Join(",\n  ", rows)}] : List (Option String × List Nat × List Nat × Bool))).compress)
            #eval IO.println ("{declarationMarker}" ++ (Lean.toJson (constructorImage.getters.map fun getter =>
              Extraction.spelled? getter.names.signature)).compress)
            end ImageRows
            """;
        var probe = Path.Combine(session, "ImageRows.lean");
        File.WriteAllText(probe, query);
        var output = Run([verifier.LeanExecutable, probe], cwd: session, leanPath: verifier.SessionLeanPath(session));
        var lines = output.Split('\n');
        var line = lines.Single(line => line.StartsWith(marker, StringComparison.Ordinal));
        using var document = JsonDocument.Parse(line[marker.Length..]);
        var read = document.RootElement.EnumerateArray().Select((row, index) =>
        {
            // Lean writes a pair as a two-element array, so each row nests its later fields.
            var signature = row[0].GetString() ??
                throw new InvalidDataException($"Image row {index} has no well-formed signature.");
            var opcodes = row[1][0].EnumerateArray().Select(opcode => opcode.GetInt32()).ToArray();
            var linked = row[1][1][0].EnumerateArray().Select(target => target.GetInt32()).Distinct().Order().ToArray();
            if (!row[1][1][1].GetBoolean())
                throw new InvalidDataException("Templates do not support an image row with static field sites: " +
                    signature);
            return new TemplateEmitter.Method(signature, ImageRowFrame, [], opcodes, linked);
        }).ToArray();
        if (read.Length != count) throw new InvalidDataException("Lean did not return every appended image row.");
        var declarations = JsonSerializer.Deserialize<string?[]>(lines.Single(line =>
            line.StartsWith(declarationMarker, StringComparison.Ordinal))[declarationMarker.Length..]);
        if (declarations is null || declarations.Any(signature => signature is null))
            throw new InvalidDataException("Lean did not return a well-formed signature for every image getter.");
        return (read, [.. declarations.OfType<string>()]);
    }

    // An image row's template copies every frame field from its decoded row except the static sites, which are none.
    static readonly FrameMetadata ImageRowFrame = new(false, [], [], [], [], [], "");

    /// <summary>Templates compare and print the same opaque slots as their checked extractions.</summary>
    internal static TemplateEmitter.Method[] TemplateVectorFrames(string source, TemplateEmitter.Method[] methods)
    {
        List<int> vectors = [];
        for (int index = 0; index < methods.Length; index++)
            if (methods[index].Frame.LocalKinds.Any(kind => kind is LocalKind.Vector { Bits: 128 }))
                vectors.Add(index);
        if (vectors.Count == 0) return methods;

        using var verifier = new Program();
        var session = verifier.Library(CommonInputs());
        var expressions = vectors.Select(index => $"Extracted.method{index}.opaqueVectorLocals");
        const string marker = "template vector slots ";
        var query = $"""
            {source}
            #eval IO.println ("{marker}" ++ (Lean.toJson
              ([{string.Join(", ", expressions)}] : List (List Nat))).compress)
            """;
        var probe = Path.Combine(session, "TemplateVectorFrames.lean");
        File.WriteAllText(probe, query);
        var output = Run(["lean", probe], cwd: session, leanPath: verifier.SessionLeanPath(session));
        var result = output.Split('\n').Single(line => line.StartsWith(marker, StringComparison.Ordinal));
        var rows = JsonSerializer.Deserialize<int[][]>(result[marker.Length..]);
        if (rows is null || rows.Length != vectors.Count || rows.Any(row => row is null))
            throw new InvalidDataException("Lean did not return the opaque vector slots of each requested frame.");
        foreach (var (index, row) in vectors.Zip(rows))
        {
            var method = methods[index];
            methods[index] = method with { Frame = method.Frame with { OpaqueVectorLocals = row } };
        }
        return methods;
    }
}
