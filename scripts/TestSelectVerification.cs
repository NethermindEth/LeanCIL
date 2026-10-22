#!/usr/bin/env dotnet
#:property PublishAot=false
#:include VerificationSelection.cs

using System.Diagnostics;
using System.Text.RegularExpressions;

var checks = 0;
var root = VerificationSelection.Root;
string[] All() => VerificationSelection.SuiteInputs().Keys.Order(StringComparer.Ordinal).ToArray();
void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}
void Equal(IEnumerable<string> actual, IEnumerable<string> expected)
{
    Require(actual.SequenceEqual(expected, StringComparer.Ordinal),
        $"Expected [{string.Join(", ", expected)}], got [{string.Join(", ", actual)}]");
}
void Test(string name, Action action)
{
    action();
    checks++;
    Console.WriteLine("PASS " + name);
}

Test("longest-first preserves selection", () =>
{
    var selected = VerificationSelection.Select(["Tests/Loops.cs", "Tests/UnsafeLayouts.cs", "Tests/IntegerMath.cs"]);
    Equal(VerificationSelection.Schedule(selected), ["unsafe", "math", "loops"]);
    Equal(VerificationSelection.Schedule(All()).Order(StringComparer.Ordinal), All());
    Equal(VerificationSelection.Schedule(["loops", "newlongsuite"]), ["newlongsuite", "loops"]);
    Equal(VerificationSelection.Schedule([]), []);
});
Test("measured schedule reduces estimated tail without skipping jobs", () =>
{
    var durations = VerificationSelection.ReadDurations();
    double Makespan(IEnumerable<string> order, int workers)
    {
        var available = new PriorityQueue<double, double>();
        for (var i = 0; i < workers; i++) available.Enqueue(0, 0);
        foreach (var name in order)
        {
            var end = available.Dequeue() + durations[name];
            available.Enqueue(end, end);
        }
        return available.UnorderedItems.Max(item => item.Element);
    }
    Require(Makespan(VerificationSelection.Schedule(All()), 8) < Makespan(All(), 4), "Measured scheduling did not improve the simulated tail");
});
Test("docs only", () => Equal(VerificationSelection.Select(["README.md", "docs/design.md"]), []));
Test("main and manual always full", () =>
{
    foreach (var eventName in new[] { "push", "workflow_dispatch" })
        Equal(VerificationSelection.Select(["README.md"], eventName), All());
});
Test("test entry points", () =>
{
    Equal(VerificationSelection.Select(["Tests/Loops.cs"]), ["loops"]);
    Equal(VerificationSelection.Select(["Tests/SkipInitialization.cs"]), ["unsafe"]);
    Equal(VerificationSelection.Select(["Tests/NullReferences.cs"]), ["unsafe"]);
    foreach (var name in new[] { "BatchVerification", "VerificationCache", "VerificationReuse" })
        Equal(VerificationSelection.Select([$"Tests/{name}.cs"]), ["core"]);
});
Test("proof and transitive imports", () =>
{
    Equal(VerificationSelection.Select(["Examples/Proofs/Countdown.lean"]), ["contracts", "fsharp", "loops"]);
    Equal(VerificationSelection.Select(["Examples/Support.lean"]), All());
    Equal(VerificationSelection.Select(["Tests/UnsafeCallEvidence.lean"]), ["unsafe"]);
});
Test("dynamic proof paths", () =>
{
    Require(VerificationSelection.Select(["Examples/Proofs/Negate64.lean"]).Contains("integer"), "Missing integer proof owner");
    Require(VerificationSelection.Select(["Examples/Proofs/GenericIdentity.lean"]).Contains("contracts"), "Missing generic proof owner");
    Require(VerificationSelection.Select(["Examples/Proofs/ConstructorValue.lean"]).Contains("fsharp"), "Missing F# proof owner");
});
Test("shared unknown and workflow inputs", () =>
{
    foreach (var path in new[] { "CIL/Safety/Memory.lean", "Extractor/UnsafeModels.cs", "global.json",
        "Examples/Assembly/SkipInitialization.cs", "Tests/NewTest.cs", ".github/workflows/verification.yml",
        "scripts/SelectVerification.cs" })
        Equal(VerificationSelection.Select([path]), All());
});
Test("multiple changes and deleted paths", () =>
{
    Equal(VerificationSelection.Select(["README.md", "Tests/Loops.cs", "Tests/Division.cs"]), ["division", "loops"]);
    Equal(VerificationSelection.Select(["Tests/Deleted.cs"]), All());
});
Test("every registered suite has its entry point", () =>
{
    var runner = File.ReadAllText(Path.Combine(root, "scripts/Test.cs"));
    var accepted = Regex.Match(runner, """\["--suite", (.*?)\] =>""").Groups[1].Value;
    var names = Regex.Matches(accepted, @"""([a-z]+)""").Select(match => match.Groups[1].Value)
        .Where(name => name != "all").Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal);
    Equal(names, All());
    foreach (var (suite, inputs) in VerificationSelection.SuiteInputs())
        Require(inputs.Count > 0, "No entry point: " + suite);
});
Test("required gate, all 192 actual Bash status combinations", () =>
{
    var bash = OperatingSystem.IsWindows() ? "C:/Program Files/Git/bin/bash.exe" :
        (Environment.GetEnvironmentVariable("PATH") ?? "").Split(Path.PathSeparator)
            .Select(directory => Path.Combine(directory, "bash")).FirstOrDefault(File.Exists);
    if (bash is null || !File.Exists(bash)) throw new InvalidOperationException("Bash is required to test the actual workflow gate");
    var workflow = File.ReadAllText(Path.Combine(root, ".github/workflows/verification.yml")).ReplaceLineEndings("\n");
    const string marker = "        run: |\n";
    var start = workflow.LastIndexOf(marker, StringComparison.Ordinal);
    Require(start >= 0, "Missing workflow gate");
    var gate = Regex.Replace(workflow[(start + marker.Length)..], @"(?m)^ {10}", "");
    string[] statuses = ["success", "failure", "cancelled", "skipped"];
    foreach (var planned in statuses)
    foreach (var selected in new[] { "true", "false", "" })
    foreach (var prepared in statuses)
    foreach (var result in statuses)
    {
        var command = new ProcessStartInfo(bash)
        {
            UseShellExecute = false, CreateNoWindow = true,
            RedirectStandardOutput = true, RedirectStandardError = true
        };
        foreach (var arg in new[] { "-e", "-c", gate }) command.ArgumentList.Add(arg);
        command.Environment["SELECT_RESULT"] = planned;
        command.Environment["HAS_SUITES"] = selected;
        command.Environment["PREPARE_RESULT"] = prepared;
        command.Environment["SUITES_RESULT"] = result;
        using var process = Process.Start(command) ?? throw new InvalidOperationException("Could not start Bash");
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        var expected = planned == "success" && ((selected, prepared, result) is
            ("true", "success", "success") or ("false", "skipped", "skipped"));
        Require((process.ExitCode == 0) == expected,
            $"Unexpected gate result: {planned}/{selected}/{prepared}/{result}\n{stdout.GetAwaiter().GetResult()}{stderr.GetAwaiter().GetResult()}");
    }
});
Test("same-run certified library binding and observability", () =>
{
    var workflow = File.ReadAllText(Path.Combine(root, ".github/workflows/verification.yml"));
    const string dollar = "$";
    foreach (var text in new[] {
        "needs: [select, prepare]", "needs: [select, prepare, suites]",
        "LEANCIL_CERTIFIED_LIBRARY_SHA256: " + dollar + "{{ needs.prepare.outputs.manifest-sha256 }}",
        "artifact-ids: " + dollar + "{{ needs.prepare.outputs.artifact-id }}",
        "artifact-id: " + dollar + "{{ steps.library-artifact.outputs.artifact-id }}",
        "name: verification-results-" + dollar + "{{ matrix.suite }}-" + dollar + "{{ github.run_attempt }}",
        "include-hidden-files: true", "max-parallel: 8", "artifacts/verification-traces/" })
        Require(workflow.Contains(text, StringComparison.Ordinal), "Missing workflow binding: " + text);
    var name = "name: certified-library-" + dollar + "{{ github.run_id }}-" + dollar + "{{ github.run_attempt }}";
    Require(workflow.Split(name, StringSplitOptions.None).Length == 2, "Producer artifact name must appear exactly once");
});
Console.WriteLine($"All {checks} selection checks passed.");
