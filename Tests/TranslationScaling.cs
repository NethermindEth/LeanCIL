#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include GeneratedEvidence.cs

using System.Text.Json;

// Real compiled C# call graph: each method fits the ordinary budget, while one monolithic elaborator `decide`
// over the whole certificate is refused at once, since only the kernel may evaluate the body and metadata check.
var directory = At("artifacts/TranslationScaling");
var source = Path.Combine(directory, "Assembly");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Scaling.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net11.0</TargetFramework>
<Optimize>true</Optimize></PropertyGroup></Project>
""");
var methods = Enumerable.Range(0, 6).Select(index =>
    $"public static ulong M{index}(ulong x) {{ " +
    string.Join(" ", Enumerable.Range(1, 48).Select(value => $"x = (x + {value}UL) ^ {value + index}UL;")) +
    (index == 0 ? " return M1(x) + M2(x) + M3(x) + M4(x) + M5(x); }" : " return x; }"));
File.WriteAllText(Path.Combine(source, "Scaling.cs"), "public static class Scaling { " + string.Join('\n', methods) + " }");
Run(["dotnet", "build", Path.Combine(source, "Scaling.csproj"), "-c", "Release"]);
var assembly = Path.Combine(source, "bin/Scaling.dll");
var output = Path.Combine(directory, "Extraction");
Run(Extract("extract", assembly, "Scaling", "Scaling::M0(ulong)", output));
var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
if (!extracted.Contains("method5_evidence_validated") || extracted.Contains("set_option maxHeartbeats"))
    throw new InvalidOperationException("Expected six independently checked methods at the default heartbeat budget.");
var start = extracted.IndexOf("theorem translation_valid :", StringComparison.Ordinal);
var end = extracted.IndexOf("@[cil_code] theorem lookup0", start, StringComparison.Ordinal);
var monolithicSource = extracted[..start] +
    "theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts assemblies " +
    "methodEvidence imports program := by decide\n" + extracted[end..];
void RequireElaboratorRefusal(int code, string diagnostic)
{
    var errors = diagnostic.Split('\n').Where(line => line.Contains(": error:", StringComparison.Ordinal)).ToArray();
    if (code == 0 || errors.Length != 1 ||
        !errors[0].Contains("failed to reduce", StringComparison.Ordinal))
        throw new InvalidOperationException(
            "Fixture no longer demonstrates the elaborator refusing the monolithic certificate: " + diagnostic);
}
if (args.Contains("--measure", StringComparer.Ordinal))
{
    var trace = Path.Combine(directory, "Trace-" + Guid.NewGuid().ToString("N"));
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
    Console.WriteLine("Fixed-workload prefix measurements: " + trace);
    Run(["lake", "env", "lean", "-DElab.async=false", Path.Combine(output, "Extracted.lean")], cwd: FixturePackage(),
        progress: "Baseline complete compositional extraction");
    var original = Path.Combine(directory, "FullMonolithic.lean");
    File.WriteAllText(original, monolithicSource);
    var result = Execute(["lake", "env", "lean", "-DElab.async=false", original], cwd: FixturePackage(),
        progress: "Baseline complete monolithic refusal");
    RequireElaboratorRefusal(result.Code, result.Output);
}
var old = Path.Combine(directory, "Monolithic.lean");
// The monolithic decision uses the raw definitions, not the already-proved component lemmas.
// The production consumer below checks the complete unchanged positive certificate once.
File.WriteAllText(old, NarrowEvidence(monolithicSource, "translation_valid"));
var monolithic = Execute(["lake", "env", "lean", "-DElab.async=false", old], cwd: FixturePackage(),
    progress: "Checking monolithic certificate refusal");
RequireElaboratorRefusal(monolithic.Code, monolithic.Output);
Console.WriteLine("PASS six-method compiled fixture: the elaborator refuses the monolithic certificate");

// The kernel decides the monolithic certificate. Its heartbeats and peak memory per added method of the call graph
// may not grow with the number of methods: superlinear growth would make the check unusable on large extractions
// even though only the kernel may run it. Measured: 0.96 in heartbeats, 0.92 in memory.
const double AllowedKernelGrowth = 1.2;
(long Heartbeats, double Gigabytes) KernelCost(int methodCount)
{
    var work = Path.Combine(directory, "Kernel" + methodCount);
    var kernelSource = Path.Combine(work, "Assembly");
    Directory.CreateDirectory(kernelSource);
    File.WriteAllText(Path.Combine(kernelSource, "Scaling.csproj"), File.ReadAllText(Path.Combine(source,
        "Scaling.csproj")));
    var kernelMethods = Enumerable.Range(0, methodCount).Select(index =>
        $"public static ulong M{index}(ulong x) {{ " +
        string.Join(" ", Enumerable.Range(1, 48).Select(value => $"x = (x + {value}UL) ^ {value + index}UL;")) +
        (index == 0 ? " return " + string.Join(" + ", Enumerable.Range(1,
            methodCount - 1).Select(call => $"M{call}(x)")) + "; }"
            : " return x; }"));
    File.WriteAllText(Path.Combine(kernelSource, "Scaling.cs"), "public static class Scaling { " + string.Join('\n',
        kernelMethods) + " }");
    Run(["dotnet", "build", Path.Combine(kernelSource, "Scaling.csproj"), "-c", "Release"]);
    var extraction = Path.Combine(work, "Extraction");
    Run(Extract("extract", Path.Combine(kernelSource, "bin/Scaling.dll"), "Scaling", "Scaling::M0(ulong)",
        extraction));
    var full = File.ReadAllText(Path.Combine(extraction, "Extracted.lean"));
    var from = full.IndexOf("theorem translation_valid :", StringComparison.Ordinal);
    var to = full.IndexOf("@[cil_code] theorem lookup0", from, StringComparison.Ordinal);
    var kernelFile = Path.Combine(work, "Monolithic.lean");
    File.WriteAllText(kernelFile, NarrowEvidence(full[..from] +
        "theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts assemblies " +
        "methodEvidence imports program := by decide +kernel\n" + full[to..], "translation_valid") +
        "\n#eval show IO Nat from IO.getNumHeartbeats\n");
    var (peak, output) = MeasurePeakGigabytes(["lake", "env", "lean", "-DElab.async=false", kernelFile],
        FixturePackage());
    var count = HeartbeatCount().Match(output);
    if (!count.Success) throw new InvalidOperationException("Missing heartbeat count:\n" + output);
    return (long.Parse(count.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture), peak);
}
int[] workloads = [2, 4, 8];
var costs = workloads.Select(count => (Count: count, Cost: KernelCost(count))).ToArray();
foreach (var (count, cost) in costs)
    Console.WriteLine(FormattableString.Invariant(
        $"kernel decide of the {count}-method certificate: {cost.Heartbeats} heartbeats, ") +
        FormattableString.Invariant($"peak {cost.Gigabytes:F2} GB"));
// The cost of a method added from the middle to the largest workload against one added from the smallest to the
// middle; the imports and the fixed part of the certificate cancel. An increment below `floor` counts as `floor`.
double IncrementRatio(Func<(long Heartbeats, double Gigabytes), double> measure, double floor)
{
    double Increment(int from) => Math.Max(measure(costs[from + 1].Cost) - measure(costs[from].Cost), floor) /
        (costs[from + 1].Count - costs[from].Count);
    return Increment(1) / Increment(0);
}
var beatGrowth = IncrementRatio(cost => cost.Heartbeats, 1);
// Peak memory moves by tens of megabytes between runs of one file.
var memoryGrowth = IncrementRatio(cost => cost.Gigabytes, 0.05);
if (beatGrowth > AllowedKernelGrowth || memoryGrowth > AllowedKernelGrowth)
    throw new InvalidOperationException(string.Create(System.Globalization.CultureInfo.InvariantCulture,
        $"A method added to {workloads[1]} methods costs {beatGrowth:F2} times the heartbeats and " +
        $"{memoryGrowth:F2} times the memory of one added to {workloads[0]}; the limit is {AllowedKernelGrowth}."));
Console.WriteLine(FormattableString.Invariant(
    $"PASS the kernel check per added method grows {beatGrowth:F2} times in heartbeats and {memoryGrowth:F2} ") +
    FormattableString.Invariant(
        $"times in memory from {workloads[0]}-{workloads[1]} to {workloads[1]}-{workloads[2]} methods"));

// Peak working set of `lean` on a file in gigabytes, and its output. Lean runs directly with the options between
// `lean` and the file, in the environment `lake env` prints, so the measured process holds the memory everywhere.
static (double Gigabytes, string Output) MeasurePeakGigabytes(string[] command, string cwd,
    string? sourceText = null)
{
    var path = command[^1];
    if (sourceText is not null) File.WriteAllText(path, sourceText);
    var environment = Run(["lake", "env"], cwd: cwd).ReplaceLineEndings("\n").Split('\n')
        .Select(line => line.Split('=', 2)).Where(pair => pair.Length == 2)
        .ToDictionary(pair => pair[0], pair => pair[1]);
    var lean = Path.Combine(environment["LEAN_SYSROOT"], "bin", OperatingSystem.IsWindows() ? "lean.exe" : "lean");
    var info = new System.Diagnostics.ProcessStartInfo(lean) { WorkingDirectory = cwd, UseShellExecute = false,
        RedirectStandardOutput = true, RedirectStandardError = true };
    foreach (var (name, value) in environment) info.Environment[name] = value;
    foreach (var argument in command[3..]) info.ArgumentList.Add(argument);
    using var process = System.Diagnostics.Process.Start(info)!;
    var output = process.StandardOutput.ReadToEndAsync();
    var errors = process.StandardError.ReadToEndAsync();
    long peak = 0;
    while (!process.WaitForExit(200))
    {
        // Lean can exit between the wait and the read; the peak is then the last one read.
        try
        {
            process.Refresh();
            peak = Math.Max(peak, process.PeakWorkingSet64);
        }
        catch (InvalidOperationException) when (process.HasExited) { }
    }
    if (process.ExitCode != 0 || output.Result.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException(
            $"{lean} {path} failed ({process.ExitCode}):\n{output.Result}\n{errors.Result}");
    return (peak / (1024.0 * 1024 * 1024), output.Result);
}
var consumer = Path.Combine(directory, "Consumer");
Directory.CreateDirectory(consumer);
var revision = Run(["git", "rev-parse", "HEAD"]).Trim();
File.WriteAllText(Path.Combine(consumer, "lakefile.toml"),
    $"name = \"scaling\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(consumer, "lean-toolchain"), true);
var proof = Path.Combine(consumer, "Proof.lean");
File.WriteAllText(proof, """
import Extracted
namespace ExampleProof
theorem correctness : CIL.Extraction.TranslationValid Extracted.rawLayouts Extracted.computedLayouts
    Extracted.assemblies Extracted.methodEvidence Extracted.imports Extracted.program :=
  Extracted.translation_valid
#print axioms correctness
end ExampleProof
""");
Run(["lake", "update"], consumer);
Run(["dotnet", ExtractorPath, "verify", output, "--proof", proof, "--proof-root", consumer]);
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (!report.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid") ||
    !report.GetProperty("theoremAudit").GetString()!.Contains("ExampleProof.correctness"))
    throw new InvalidOperationException("Missing independent certificate/theorem audits.");
Console.WriteLine("PASS fresh consumer proof-root verifies the multi-method certificate with kernel replay and restricted axioms");
CheckHeartbeatBudget(Path.Combine(output, "Extracted.lean"));
CheckLayoutTableScaling(extracted);

// The extraction checks within the default heartbeat budget with the kernel counted on the elaborating thread, and
// the budget binds: the same file fails at 100 heartbeats with a deterministic timeout.
void CheckHeartbeatBudget(string extraction)
{
    Run(["lake", "env", "lean", "-DElab.async=false", extraction], cwd: FixturePackage(),
        progress: "Checking the extraction at the default heartbeat budget");
    var starved = Execute(["lake", "env", "lean", "-DElab.async=false", "-DmaxHeartbeats=100", extraction],
        cwd: FixturePackage(), progress: "Checking the extraction at 100 heartbeats");
    if (starved.Code == 0 || !starved.Output.Contains("deterministic", StringComparison.Ordinal) ||
        !starved.Output.Contains("timeout", StringComparison.Ordinal))
        throw new InvalidOperationException("The extraction does not time out at 100 heartbeats: " + starved.Output);
    Console.WriteLine("PASS the extraction checks at the default heartbeat budget and times out at 100");
}

// The emitted header and method layout theorems over chains of nested and of generic structs: kernel heartbeats
// per layout may grow by at most 1.5 times from 64 to 512 layouts, and 512 layouts must check within 8 GiB.
void CheckLayoutTableScaling(string extraction)
{
    const double allowedGrowth = 1.5;
    const int small = 64, large = 512;
    const string report = "#eval show IO Nat from IO.getNumHeartbeats";
    const string axioms = "depends on axioms: [propext, Classical.choice, Quot.sound]";
    string Emitted(string name) => extraction.Split('\n').Select(line => line.TrimEnd('\r'))
        .Single(line => line.StartsWith($"theorem {name} :", StringComparison.Ordinal));
    // Each row is a namespace holding one table and the emitted theorem it measures.
    (string Name, string Namespace, string Theorem)[] rows =
    [
        ("the header check of nested structs", "Nested", Emitted("layouts_validated")),
        ("the header check of generic structs", "Generic", Emitted("layouts_validated")),
        ("a method's check of nested structs", "Nested", Emitted("method0_layouts_validated"))
    ];
    string Table(string space, int count, Func<int, string> raw, Func<int, string> layout) => $$"""
        namespace {{space}}
        def rawLayouts : List Extraction.RawLayout := [
        {{string.Join(",\n", Enumerable.Range(0, count).Select(raw))}}]
        {{string.Join("\n", Enumerable.Range(0, count).Select(index => $"def layout{index} : AggregateLayout := " +
            layout(index)))}}
        def computedLayouts : Array Extraction.ComputedLayout :=
          #[{{string.Join(", ", Enumerable.Range(0, count).Select(index => $"⟨layout{index}, 8⟩"))}}]
        def method0 : Method := { code := [.ret], locals := [], returnsValue := false }
        def method0LayoutUses : List Extraction.LayoutUse := []
        end {{space}}
        """;
    double[] PerLayout(int count)
    {
        // T0 holds a ulong and T(k) holds T(k - 1) and then a byte, so each layout reads the one before it.
        var nested = Table("Nested", count, index =>
            $"  {{ identity := \"T{index}\", explicit := false, packing := 0, declaredSize := 0, fields := [" +
            (index == 0 ? "⟨.unsigned64, none⟩" : $"⟨.aggregate {index - 1}, none⟩, ⟨.unsigned8, none⟩") + "] }",
            index => index == 0 ? "⟨8, [⟨0, 8, false⟩]⟩"
                : $"⟨{8 * (index + 1)}, [⟨0, {8 * index}, true⟩, ⟨{8 * index}, 1, false⟩]⟩");
        // Wrap(k)<Leaf> holds Wrap(k - 1)<Leaf>, so each layout looks up the previous distinct generic owner.
        var generic = Table("Generic", count, index => index == 0
            ? "  { identity := \"Leaf\", explicit := false, packing := 0, declaredSize := 0, " +
                "fields := [⟨.unsigned64, none⟩] }"
            : $"  {{ identity := \"S::Wrap{index}`1<Leaf>\", generic := some {{ owner := .constructor \"S\" " +
                $"\"Wrap{index}`1\", arity := 1, arguments := [.aggregate \"Leaf\" 0], fields := [" +
                (index == 1 ? ".parameter 0" : $".apply (.constructor \"S\" \"Wrap{index - 1}`1\") (.parameter 0)") +
                $"], constraints := [(0, [])] }}, explicit := false, packing := 0, declaredSize := 0, " +
                $"fields := [⟨.aggregate {index - 1}, none⟩] }}",
            index => $"⟨8, [⟨0, 8, {(index > 0 ? "true" : "false")}⟩]⟩");
        var measured = string.Join("\n", rows.Select(row => $"namespace {row.Namespace}\n{row.Theorem}\n" +
            $"end {row.Namespace}\n{report}"));
        var audits = string.Join("\n", rows.Select(row =>
            $"#print axioms {row.Namespace}.{row.Theorem.Split(' ')[1]}"));
        var path = Path.Combine(directory, $"Layouts{count}.lean");
        File.WriteAllText(path, $"""
            import CIL.Extraction.LayoutUses
            open CIL
            {nested}
            {generic}
            {report}
            {measured}
            {audits}
            """ + "\n");
        // Without the flag the kernel checks on another thread and its heartbeats go uncounted.
        var output = Run(["lake", "env", "lean", "-DElab.async=false", "-M", "8192", path], cwd: FixturePackage());
        var counts = output.Split('\n').Select(line => line.Trim())
            .Where(line => line.Length > 0 && line.All(char.IsAsciiDigit))
            .Select(line => long.Parse(line, System.Globalization.CultureInfo.InvariantCulture)).ToArray();
        if (counts.Length != rows.Length + 1 || output.Contains("sorryAx", StringComparison.Ordinal) ||
            rows.Any(row => !output.Contains($"'{row.Namespace}.{row.Theorem.Split(' ')[1]}' {axioms}",
                StringComparison.Ordinal)))
            throw new InvalidOperationException($"Unchecked layout tables of {count} layouts:\n{output}");
        return [.. rows.Select((_, row) => (double)(counts[row + 1] - counts[row]) / count)];
    }
    var smallCosts = PerLayout(small);
    var largeCosts = PerLayout(large);
    for (var row = 0; row < rows.Length; row++)
    {
        var growth = largeCosts[row] / smallCosts[row];
        var measured = FormattableString.Invariant($"{smallCosts[row]:F0} heartbeats per layout at {small}") +
            FormattableString.Invariant($" layouts and {largeCosts[row]:F0} at {large}, {growth:F2} times as many");
        if (growth > allowedGrowth)
            throw new InvalidOperationException(FormattableString.Invariant(
                $"{rows[row].Name} costs {measured}; the limit is {allowedGrowth}."));
        Console.WriteLine($"PASS {rows[row].Name} costs {measured}");
    }
    Console.WriteLine($"PASS {large} nested and {large} generic layouts check within 8 GiB");
}
