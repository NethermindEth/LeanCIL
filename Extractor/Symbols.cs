using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Local names and source locations from a matching portable PDB. They only locate: nothing in
// Extracted.lean depends on them, and a missing or mismatched PDB leaves extraction unchanged.
internal static class Symbols
{
    // `module` gains debug information when a matching PDB is read; returns where it came from.
    internal static string? Read(ModuleDefinition module, string assemblyPath, out string? notice)
    {
        notice = null;
        if (!module.HasDebugHeader) return null;
        var entries = module.GetDebugHeader().Entries;
        try
        {
            if (entries.Any(e => e.Directory.Type == ImageDebugType.EmbeddedPortablePdb))
            {
                module.ReadSymbols(new EmbeddedPortablePdbReaderProvider().GetSymbolReader(module, assemblyPath), true);
                return "embedded";
            }
            var pdb = Path.ChangeExtension(assemblyPath, ".pdb");
            if (!entries.Any(e => e.Directory.Type == ImageDebugType.CodeView) || !File.Exists(pdb)) return null;
            var bytes = File.ReadAllBytes(pdb);
            module.ReadSymbols(new PortablePdbReaderProvider().GetSymbolReader(module, new MemoryStream(bytes)), true);
            return Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();
        }
        catch (Exception error) when (error is SymbolsNotMatchingException or BadImageFormatException or InvalidOperationException)
        {
            notice = $"Symbols: not read from {CliPaths.Display(Path.ChangeExtension(assemblyPath, ".pdb"))} ({error.Message})";
            return null;
        }
    }

    static Dictionary<int, int> Pcs(MethodDefinition definition) =>
        definition.Body.Instructions.Select((instruction, pc) => (instruction.Offset, pc)).ToDictionary(p => p.Offset, p => p.pc);

    static IEnumerable<SequencePoint> Points(MethodDefinition definition) =>
        definition.DebugInformation.HasSequencePoints ? definition.DebugInformation.SequencePoints.Where(p => !p.IsHidden) : [];

    // The nearest visible sequence point at or before an IL offset, as `file:line:column`.
    internal static string? Location(MethodDefinition method, int offset, Func<string, string> file)
    {
        var point = Points(MethodSpecialization.Definition(method)).LastOrDefault(p => p.Offset <= offset);
        return point is null ? null : $"{file(point.Document.Url)}:{point.StartLine}:{point.StartColumn}";
    }

    // `InMethod` appends this to instruction errors, whose messages carry Cecil's `IL_xxxx` label.
    internal static string? Locate(MethodDefinition method, string message)
    {
        var label = Regex.Match(message, @"\bIL_([0-9a-f]{4,})\b");
        return label.Success && Location(method, Convert.ToInt32(label.Groups[1].Value, 16), Path.GetFileName) is { } at
            ? "\n  Source: " + at : null;
    }

    static string Quote(string text) => JsonSerializer.Serialize(text);

    internal static string Emit(MethodDefinition[] methods, string origin)
    {
        var definitions = methods.Select(MethodSpecialization.Definition).ToArray();
        // Paths are relative to the documents' common directory, so output does not depend on the build machine.
        var documents = definitions.SelectMany(Points).Select(p => p.Document.Url).Distinct().ToArray();
        var directories = documents.Select(d => d.Split('/', '\\')[..^1]).ToArray();
        var shared = directories.Length == 0 ? 0 : Enumerable.Range(0, directories.Min(d => d.Length))
            .TakeWhile(i => directories.All(d => d[i] == directories[0][i])).Count();
        string Display(string url) => string.Join('/', url.Split('/', '\\').Skip(shared));

        var lean = new StringBuilder();
        lean.AppendLine($"-- Generated from the {(origin == "embedded" ? "embedded portable PDB" : "portable PDB with SHA-256 " + origin)}.");
        lean.AppendLine("-- Names and locations only choose indices for proofs and diagnostics; they are not proof evidence.");
        lean.AppendLine("namespace ExtractedSymbols");
        lean.AppendLine("/-- Per method in program order: `(slot, startPc, endPc, name)`, with `endPc` exclusive. -/");
        lean.AppendLine("def locals : List (List (Nat × Nat × Nat × String)) := [");
        lean.AppendLine(string.Join(",\n", definitions.Select(definition =>
        {
            var pcs = Pcs(definition);
            var count = definition.Body.Instructions.Count;
            var scoped = new List<string>();
            void Visit(ScopeDebugInformation scope)
            {
                if (pcs.TryGetValue(scope.Start.Offset, out var start))
                {
                    var end = scope.End.IsEndOfMethod ? count : pcs.GetValueOrDefault(scope.End.Offset, count);
                    foreach (var variable in scope.Variables.Where(v => !v.IsDebuggerHidden && !string.IsNullOrEmpty(v.Name)))
                        scoped.Add($"({variable.Index}, {start}, {end}, {Quote(variable.Name)})");
                }
                foreach (var inner in scope.Scopes) Visit(inner);
            }
            if (definition.DebugInformation.Scope is { } top) Visit(top);
            return "  [" + string.Join(", ", scoped) + "]";
        })) + "]");
        lean.AppendLine("/-- Per method in program order: `(pc, file, line, column)` for each visible sequence point. -/");
        lean.AppendLine("def points : List (List (Nat × String × Nat × Nat)) := [");
        lean.AppendLine(string.Join(",\n", definitions.Select(definition =>
        {
            var pcs = Pcs(definition);
            return "  [" + string.Join(", ", Points(definition).Where(p => pcs.ContainsKey(p.Offset))
                .Select(p => $"({pcs[p.Offset]}, {Quote(Display(p.Document.Url))}, {p.StartLine}, {p.StartColumn})")) + "]";
        })) + "]");
        lean.AppendLine("end ExtractedSymbols");
        return lean.ToString();
    }
}
