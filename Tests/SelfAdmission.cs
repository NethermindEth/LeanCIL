#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include StableNames.cs

using System.Diagnostics;
using System.Text.Json;
using Mono.Cecil;

// Admission of LeanCIL's own assembly under the scalar profile against its baseline of admitted methods.
// Fails on any difference, so a lost admission, an unrecorded gain or a removed method all need review.
const string Usage = "Usage: SelfAdmission.cs [--update] [--baseline baseline.txt] [--assembly assembly.dll] " +
    "[--reuse-report] [--lean-check] [--shard index/count]";
const string Profile = "scalar";
const int ListedBlockers = 10;
const int ListedMethods = 20;
var baselinePath = At("Tests/SelfAdmissionBaseline.txt");
var assemblyPath = ExtractorPath;
bool update = false, reuse = false, leanCheck = false;
(int Index, int Count)? shard = null;
for (var index = 0; index < args.Length; index++)
    switch (args[index])
    {
        case "--update": update = true; break;
        // The gate's own tests compare an existing report with altered baselines.
        case "--reuse-report": reuse = true; break;
        // Elaborates the extraction of every admitted method against CIL; runs weekly in CI across shards.
        case "--lean-check": leanCheck = true; break;
        case "--shard" when index + 1 < args.Length:
            shard = ParseShard(args[++index]);
            break;
        case "--baseline" when index + 1 < args.Length: baselinePath = Path.GetFullPath(args[++index]); break;
        case "--assembly" when index + 1 < args.Length: assemblyPath = Path.GetFullPath(args[++index]); break;
        default: throw new ArgumentException(Usage);
    }
if (shard is not null && !leanCheck)
    throw new ArgumentException("--shard requires --lean-check.\n" + Usage);
var directory = At("artifacts/SelfAdmission");
Directory.CreateDirectory(directory);

// Every metadata method, constructors and compiler-generated members included, under one profile.
string[] signatures;
using (var module = ModuleDefinition.ReadModule(assemblyPath))
{
    var configuration = module.Assembly.CustomAttributes
        .FirstOrDefault(attribute => attribute.AttributeType.FullName ==
            "System.Reflection.AssemblyConfigurationAttribute")
        ?.ConstructorArguments.FirstOrDefault().Value as string;
    if (configuration != "Release")
        throw new InvalidDataException(
            $"SelfAdmission requires a Release build of {assemblyPath}, found configuration " +
            $"'{configuration ?? "(none)"}'. Rebuild with `dotnet build Extractor/Extractor.csproj -c Release`.");
    signatures = module.GetTypes().SelectMany(type => type.Methods).Select(method => method.FullName)
        .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
}
var manifest = Path.Combine(directory, "manifest.json");
if (!reuse)
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        entries = signatures.Select(signature => new { signature, profile = Profile })
    }));
var report = Path.Combine(directory, "blockers.json");
var timer = Stopwatch.StartNew();
if (!reuse) Run(["dotnet", ExtractorPath, "blockers", assemblyPath, "--manifest", manifest, "--output", report]);
var elapsed = timer.Elapsed.TotalSeconds;

using var document = JsonDocument.Parse(File.ReadAllText(report));
var current = new SortedDictionary<string, char>(StringComparer.Ordinal);
foreach (var entry in document.RootElement.GetProperty("entries").EnumerateArray())
    current[entry.GetProperty("signature").GetString()!] = entry.GetProperty("status").GetString() switch
    {
        "admitted" => 'A', "blocked" => 'B', "notChecked" => 'N',
        var status => throw new InvalidDataException("Unexpected admission status: " + status)
    };
if (current.Count != signatures.Length)
    throw new InvalidDataException($"Report has {current.Count} entries for {signatures.Length} methods.");
if (leanCheck) CheckAdmittedInLean(current.Where(pair => pair.Value == 'A').Select(pair => pair.Key).ToArray());

// The baseline lists admitted methods only; whether a non-admitted method is new does not matter. A
// generated method counts toward its source method, so renumbering by unrelated edits changes nothing.
var admitted = current.Where(pair => pair.Value == 'A').Select(pair => StableNames.Of(pair.Key))
    .Order(StringComparer.Ordinal).ToArray();
if (update) File.WriteAllText(baselinePath, string.Concat(admitted.Select(method => method + "\n")));
var baseline = StableNames.Counts(File.ReadAllLines(baselinePath).Where(line => line.Length != 0)
    .Select(StableNames.Of));
var admittedCounts = StableNames.Counts(admitted);
var presentCounts = StableNames.Counts(current.Keys.Select(StableNames.Of));
int CountIn(Dictionary<string, int> counts, string name) => counts.GetValueOrDefault(name);
// A name shared by several methods counts each one, so losing or gaining one of them still shows.
var lost = baseline.SelectMany(pair => Enumerable.Repeat(pair.Key, Math.Max(0,
        Math.Min(pair.Value, CountIn(presentCounts, pair.Key)) - CountIn(admittedCounts, pair.Key))))
    .Order(StringComparer.Ordinal).ToArray();
var removed = baseline.SelectMany(pair => Enumerable.Repeat(pair.Key,
        Math.Max(0, pair.Value - CountIn(presentCounts, pair.Key))))
    .Order(StringComparer.Ordinal).ToArray();
var gained = admittedCounts.SelectMany(pair => Enumerable.Repeat(pair.Key,
        Math.Max(0, pair.Value - CountIn(baseline, pair.Key))))
    .Order(StringComparer.Ordinal).ToArray();

int Count(char status) => current.Values.Count(value => value == status);
var blockers = document.RootElement.GetProperty("blockers").EnumerateArray().ToArray();
var summary = new List<string>
{
    "# Self-admission of Nethermind.LeanCIL.dll", "",
    $"Admission under the `{Profile}` profile; nothing here is proved. Gated on regressions only; gains and removed methods are reported.", "",
    "| Methods | Admitted | Blocked | Not checked | Distinct blockers | Seconds |",
    "| ---: | ---: | ---: | ---: | ---: | ---: |",
    $"| {current.Count} | {Count('A')} | {Count('B')} | {Count('N')} | {blockers.Length} | {elapsed:F1} |", "",
    $"Since the baseline: {lost.Length} lost, {gained.Length} gained, " +
        $"{removed.Length} admitted methods removed.", ""
};
void List(string heading, IEnumerable<string> methods)
{
    var listed = methods.ToArray();
    if (listed.Length == 0) return;
    summary.Add(heading);
    summary.AddRange(listed.Take(ListedMethods).Select(method => "- `" + method + "`"));
    if (listed.Length > ListedMethods) summary.Add($"- and {listed.Length - ListedMethods} more");
    summary.Add("");
}
List("Lost admissions:", lost);
List("Gained admissions:", gained);
List("Removed admitted methods:", removed);
summary.Add("| Blocker | Entries | Sites |");
summary.Add("| --- | ---: | ---: |");
summary.AddRange(blockers.Take(ListedBlockers).Select(blocker =>
    $"| {blocker.GetProperty("construct").GetString()!.Replace("|", "\\|")} | " +
    $"{blocker.GetProperty("entries").GetArrayLength()} | {blocker.GetProperty("sites").GetArrayLength()} |"));
// A reused report checks an altered baseline, so it must not replace the real scan's summary.
File.WriteAllLines(Path.Combine(directory, reuse ? "summary-check.md" : "summary.md"), summary);
if (Environment.GetEnvironmentVariable("GITHUB_STEP_SUMMARY") is { Length: > 0 } stepSummary && !reuse)
    File.AppendAllLines(stepSummary, summary);
Console.WriteLine(string.Join('\n', summary));
if (lost.Length != 0)
    throw new InvalidOperationException($"Methods admitted in {baselinePath} are no longer admitted:\n" +
        string.Join('\n', lost) + "\nSee " + report + " for their blockers.");
if (gained.Length != 0 || removed.Length != 0)
    Console.WriteLine($"NOTE {baselinePath}: {gained.Length} admissions gained and " +
        $"{removed.Length} removed methods (refresh with `dotnet run --file Tests/SelfAdmission.cs -- --update`).");
Console.WriteLine($"PASS self-admission: {Count('A')} of {current.Count} methods admitted with no regressions");

(int Index, int Count) ParseShard(string value)
{
    var parts = value.Split('/');
    if (parts.Length != 2 || !int.TryParse(parts[0], out var index) || !int.TryParse(parts[1], out var count) ||
        count < 1 || index < 1 || index > count)
        throw new ArgumentException($"Invalid --shard value '{value}'; expected 1-based index/count.");
    return (index, count);
}

// Extracts each admitted method alone and elaborates it against the certified CIL library; an admission
// the Lean checks refuse is a drift between the extractor and the checker, so any refusal fails.
void CheckAdmittedInLean(string[] methods)
{
    var selected = shard is { } slice
        ? methods.Where((_, index) => index % slice.Count == slice.Index - 1).ToArray()
        : methods;
    var label = shard is { } active ? $"shard {active.Index}/{active.Count}" : "all methods";
    using var verification = new Program();
    var leanPath = verification.CheckoutLeanPath();
    var root = Path.Combine(directory, "lean");
    if (Directory.Exists(root)) Directory.Delete(root, recursive: true);
    var refusals = new System.Collections.Concurrent.ConcurrentBag<(string Method, string Reason)>();
    var finished = 0;
    var clock = Stopwatch.StartNew();
    // Each elaboration peaks near 1 GB, so a quarter of the cores bounds memory as well as time.
    var options = new ParallelOptions { MaxDegreeOfParallelism = Math.Max(1, Environment.ProcessorCount / 4) };
    Parallel.ForEach(selected.Index(), options, entry =>
    {
        var output = Path.Combine(root, entry.Index.ToString(System.Globalization.CultureInfo.InvariantCulture));
        var result = Execute(["dotnet", ExtractorPath, "extract", assemblyPath, entry.Item, output, Profile]);
        if (result.Code == 0)
            result = Execute([verification.LeanExecutable, "--root=" + output, Path.Combine(output, "Extracted.lean")],
                leanPath: leanPath);
        if (result.Code == 0 && !result.Output.Contains("sorryAx", StringComparison.Ordinal))
            Directory.Delete(output, recursive: true);
        else
            refusals.Add((entry.Item, result.Output.Split('\n').FirstOrDefault(line => line.Contains(": error: ",
                StringComparison.Ordinal))?.Trim() ?? result.Output.Split('\n')[0].Trim()));
        if (Interlocked.Increment(ref finished) % 100 == 0)
            Console.WriteLine($"Lean check ({label}): {finished} of {selected.Length} in " +
                $"{clock.Elapsed.TotalMinutes:F0} min");
    });
    var refused = refusals.OrderBy(refusal => refusal.Method, StringComparer.Ordinal).ToArray();
    var refusalsPath = Path.Combine(directory, "lean-refusals.txt");
    if (refused.Length == 0) File.Delete(refusalsPath);
    else File.WriteAllLines(refusalsPath, refused.Select(refusal => $"{refusal.Method}\t{refusal.Reason}"));
    var leanSummary = new List<string>
    {
        $"## Self-admission Lean check ({label})", "",
        "| Checked | Admitted total | Refused | Minutes |",
        "| ---: | ---: | ---: | ---: |",
        $"| {selected.Length} | {methods.Length} | {refused.Length} | {clock.Elapsed.TotalMinutes:F1} |", ""
    };
    if (refused.Length != 0)
    {
        leanSummary.Add("Refused methods:");
        leanSummary.Add("");
        leanSummary.Add("| Method | Lean diagnostic |");
        leanSummary.Add("| --- | --- |");
        leanSummary.AddRange(refused.Select(refusal =>
            $"| `{refusal.Method.Replace("|", "\\|")}` | `{refusal.Reason.Replace("|", "\\|")}` |"));
        leanSummary.Add("");
    }
    File.WriteAllLines(Path.Combine(directory, "lean-check-summary.md"), leanSummary);
    if (Environment.GetEnvironmentVariable("GITHUB_STEP_SUMMARY") is { Length: > 0 } stepSummaryFile && !reuse)
        File.AppendAllLines(stepSummaryFile, leanSummary);
    foreach (var (method, reason) in refused) Console.WriteLine($"REFUSED {method}\n  {reason}");
    if (refused.Length != 0)
        throw new InvalidOperationException(
            $"Lean refuses {refused.Length} of {selected.Length} admitted methods ({label}).");
    Console.WriteLine($"PASS Lean check ({label}): {selected.Length} admitted methods elaborate, " +
        $"{clock.Elapsed.TotalMinutes:F0} min");
}
