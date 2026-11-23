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
