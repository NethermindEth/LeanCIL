using System.Text;
using System.Text.RegularExpressions;

partial class Program
{
    // Each mutation must produce its own expected diagnostic. A different failing case
    // or an error outside the case cannot make a valid mutation appear rejected.
    sealed class RejectedEvidence(string directory)
    {
        readonly List<(string Path, string Source, string Passed, string[] Markers,
            Func<string, bool> Diagnostic)> cases = [];

        public void Add(string path, string passed, params string[] markers) =>
            Add(path, passed, _ => true, markers);

        public void Add(string path, string passed, Func<string, bool> diagnostic, params string[] markers) =>
            cases.Add((Path.GetFullPath(path), File.ReadAllText(path), passed, markers, diagnostic));

        (string Source, List<(int Start, int End)> Ranges) BatchSource()
        {
            var imports = new SortedSet<string>(StringComparer.Ordinal);
            imports.Add("Lean");
            var bodies = new List<string>();
            foreach (var item in cases)
            {
                if (!item.Source.Contains("namespace Extracted\n", StringComparison.Ordinal))
                    throw new InvalidOperationException("Expected generated evidence: " + item.Path);
                bodies.Add(Regex.Replace(item.Source, @"^import[ \t]+([A-Za-z_][A-Za-z0-9_.]*)[ \t]*\r?$",
                    match => { imports.Add(match.Groups[1].Value); return ""; }, RegexOptions.Multiline));
            }
            const string isolation = """
                set_option maxErrors 0
                set_option Elab.async false
                namespace EvidenceRejectionHarness
                open Lean Elab Command
                /-- Check invalid fixtures without letting their declarations or attributes escape. -/
                elab "#isolated_rejection" "{" commands:command* "}" : command => do
                  let saved ← get
                  let mut messages := saved.messages
                  for command in commands do
                    modify ({ · with messages := {} })
                    messages := messages ++
                      (← Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages command)
                  set { saved with messages := messages }
                end EvidenceRejectionHarness
                """ + "\n";
            var source = new StringBuilder(string.Join('\n', imports.Select(module => "import " + module)) +
                "\n" + isolation);
            var ranges = new List<(int Start, int End)>();
            var line = imports.Count + 1 + isolation.Count(character => character == '\n');
            for (var index = 0; index < cases.Count; index++)
            {
                source.Append($"#isolated_rejection {{\nnamespace RejectedCase{index}\n");
                line += 2;
                var start = line;
                source.Append(bodies[index]).Append('\n');
                line += bodies[index].Count(character => character == '\n') + 1;
                ranges.Add((start, line));
                source.Append($"end RejectedCase{index}\n}}\n");
                line += 2;
            }
            return (source.ToString(), ranges);
        }

        public void Check(string? leanPath = null)
        {
            if (cases.Count == 0) return;
            var (source, ranges) = BatchSource();
            Directory.CreateDirectory(directory);
            var path = Path.GetFullPath(Path.Combine(directory, "RejectedBatch.lean"));
            File.WriteAllText(path, source);
            var result = Execute(["lake", "env", "lean", path], cwd: FixturePackage(), leanPath: leanPath);
            var diagnostics = Regex.Matches(result.Output,
                @"(?m)^" + Regex.Escape(path.Replace('\\', '/')) +
                @":(\d+):\d+: (error|warning|information)(?:\([^)\r\n]+\))?:");
            if (diagnostics.Count == 0)
                diagnostics = Regex.Matches(result.Output,
                    @"(?m)^" + Regex.Escape(path) +
                    @":(\d+):\d+: (error|warning|information)(?:\([^)\r\n]+\))?:");
            var starts = ranges.Select(range => range.Start).ToArray();
            var errors = cases.Select(_ => new StringBuilder()).ToArray();
            for (var diagnostic = 0; diagnostic < diagnostics.Count; diagnostic++)
            {
                var match = diagnostics[diagnostic];
                if (match.Groups[2].Value != "error") continue;
                var location = int.Parse(match.Groups[1].Value);
                var index = Array.BinarySearch(starts, location);
                if (index < 0) index = ~index - 1;
                if (index < 0 || location >= ranges[index].End) continue;
                var end = diagnostic + 1 < diagnostics.Count ? diagnostics[diagnostic + 1].Index : result.Output.Length;
                errors[index].Append(result.Output.AsSpan(match.Index, end - match.Index));
            }
            for (var index = 0; index < cases.Count; index++)
            {
                var output = errors[index].ToString();
                if (result.Code == 0 || output.Length == 0 ||
                    cases[index].Markers.Any(marker => !output.Contains(marker, StringComparison.Ordinal)) ||
                    !cases[index].Diagnostic(output))
                    throw new InvalidOperationException(
                        "Expected rejection missing: " + cases[index].Path + "\n" + output);
                if (File.ReadAllText(cases[index].Path) != cases[index].Source)
                    throw new InvalidOperationException("Mutation changed during checking: " + cases[index].Path);
            }
            foreach (var item in cases) Console.WriteLine(item.Passed);
            cases.Clear();
        }
    }
}
