using System.Text;
using System.Text.RegularExpressions;

partial class Program
{
    const string Isolation = """
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

    // The mutated source with `theorem` stated as its own negation, `¬ (statement)`, proved by the kernel: the
    // obligation a mutation breaks is shown false, not merely unprovable by the tactic that proves it when true.
    static string KernelRefutation(string mutated, string theorem, string refutation, bool prefixOnly = false)
    {
        var obligation = SingleLineTheorem.Matches(mutated).FirstOrDefault(match => match.Groups[1].Value == theorem)
            ?? throw new InvalidOperationException("Missing obligation to refute: " + theorem);
        var proof = $"theorem {refutation} : ¬ ({obligation.Groups["statement"].Value}) := by decide +kernel";
        return prefixOnly ? mutated[..obligation.Index] + proof + $"\n#print axioms {refutation}\n"
            : mutated.Replace(obligation.Value, proof);
    }

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
                bodies.Add(RejectedImport.Replace(item.Source,
                    match => { imports.Add(match.Groups[1].Value); return ""; }));
            }
            var source = new StringBuilder(string.Join('\n', imports.Select(module => "import " + module)) +
                "\n" + Isolation);
            var ranges = new List<(int Start, int End)>();
            var line = imports.Count + 1 + Isolation.Count(character => character == '\n');
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
            // Lean caps errors at the command line's maxErrors, not the file's, and drops every later diagnostic.
            var result = Execute(["lake", "env", "lean", "-DmaxErrors=0", path], cwd: FixturePackage(),
                leanPath: leanPath);
            // Lean names the file with either separator.
            var located = LocatedDiagnostic.Matches(result.Output);
            Match[] diagnostics = [.. located.Where(match => match.Groups["file"].Value == path.Replace('\\', '/'))];
            if (diagnostics.Length == 0)
                diagnostics = [.. located.Where(match => match.Groups["file"].Value == path)];
            var starts = ranges.Select(range => range.Start).ToArray();
            var errors = cases.Select(_ => new StringBuilder()).ToArray();
            var sourceLines = source.Split('\n');
            var firstLines = Enumerable.Repeat(int.MaxValue, cases.Count).ToArray();
            var refutable = new string?[cases.Count];
            for (var diagnostic = 0; diagnostic < diagnostics.Length; diagnostic++)
            {
                var match = diagnostics[diagnostic];
                if (match.Groups[2].Value != "error") continue;
                var location = int.Parse(match.Groups[1].Value);
                var index = Array.BinarySearch(starts, location);
                if (index < 0) index = ~index - 1;
                if (index < 0 || location >= ranges[index].End) continue;
                var end = diagnostic + 1 < diagnostics.Length
                    ? diagnostics[diagnostic + 1].Index
                    : result.Output.Length;
                var message = result.Output.AsSpan(match.Index, end - match.Index);
                errors[index].Append(message);
                if (location >= firstLines[index]) continue;
                firstLines[index] = location;
                var theorem = SingleLineTheorem.Match(sourceLines[location - 1]);
                var decidedFalse = message.Contains("proved that the proposition", StringComparison.Ordinal) &&
                    message.Contains("is false", StringComparison.Ordinal);
                refutable[index] = theorem.Success && decidedFalse ? theorem.Groups[1].Value : null;
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
            RefuteSemanticRejections(refutable, leanPath);
            foreach (var item in cases) Console.WriteLine(item.Passed);
            cases.Clear();
        }

        // A rejection the evaluator reports as a decided falsehood must also be refuted by the kernel: the obligation
        // is stated as its negation and proved by `decide +kernel`, so the mutation is shown false, not merely
        // unprovable. Rejections of another kind (a name that no longer resolves, a malformed term) have no negation
        // to prove and are counted, not hidden.
        void RefuteSemanticRejections(string?[] theorems, string? leanPath)
        {
            var refutations = new List<string>();
            var imports = new SortedSet<string>(StringComparer.Ordinal);
            var unrefuted = new List<string>();
            for (var index = 0; index < cases.Count; index++)
            {
                if (theorems[index] is not { } theorem)
                {
                    unrefuted.Add(Path.GetFileName(cases[index].Path));
                    continue;
                }
                var body = RejectedImport.Replace(
                    KernelRefutation(cases[index].Source, theorem, "kernelRefutation", prefixOnly: true),
                    match => { imports.Add(match.Groups[1].Value); return ""; });
                // Only the declarations preceding the failed theorem are premises of its refutation.
                refutations.Add($"#isolated_rejection {{\n{body}\n}}\n");
            }
            if (refutations.Count > 0)
            {
                var path = Path.GetFullPath(Path.Combine(directory, "KernelRefutations.lean"));
                imports.Add("Lean");
                File.WriteAllText(path, string.Join('\n', imports.Select(module => "import " + module)) + "\n" +
                    Isolation + string.Concat(refutations));
                var proved = Execute(["lake", "env", "lean", path], cwd: FixturePackage(), leanPath: leanPath);
                if (proved.Code != 0 || proved.Output.Contains("sorryAx", StringComparison.Ordinal))
                    throw new InvalidOperationException(
                        "The kernel did not refute a mutation the evaluator found false:\n" + proved.Output);
            }
            Console.WriteLine($"PASS kernel refutations of {refutations.Count} decided rejections" +
                (unrefuted.Count == 0 ? "" : $"; {unrefuted.Count} rejections of another kind have none: " +
                    string.Join(", ", unrefuted)));
        }
    }

    [GeneratedRegex(@"^import[ \t]+([A-Za-z_][A-Za-z0-9_.]*)[ \t]*\r?$", RegexOptions.Multiline)]
    private static partial Regex RejectedImport { get; }

    // A theorem stated and proved on one line; a Lean name may end in ?, ! or '.
    [GeneratedRegex(@"(?m)^(?:@\[[^\r\n]*\] )?theorem ([\w?!']+) : " +
        @"(?:(?<statement>[^\r\n]*) := by decide(?: \+kernel)?[ \t]*|(?<statement>[^\r\n]*?) := [^\r\n]*)(?=\r?$)")]
    private static partial Regex SingleLineTheorem { get; }

    [GeneratedRegex(@"(?m)^(?<file>[^\r\n]*?):(\d+):\d+: (error|warning|information)(?:\([^)\r\n]+\))?:")]
    private static partial Regex LocatedDiagnostic { get; }
}
