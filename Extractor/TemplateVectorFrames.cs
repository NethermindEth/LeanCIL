using System.Text.Json;
using Nethermind.LeanCIL;

partial class Program
{
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
