#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Diagnostics;
using System.Text.Json;
using Mono.Cecil;

// Admission of LeanCIL's own assembly under the scalar profile, gated on admitted methods only.
// Fails only when a method admitted in the baseline still exists and is no longer admitted.
const string Usage = "Usage: SelfAdmission.cs [--update] [--baseline baseline.tsv] [--reuse-report]";
const string Profile = "scalar";
const int ListedBlockers = 10;
const int ListedMethods = 20;
var baselinePath = At("Tests/SelfAdmissionBaseline.tsv");
bool update = false, reuse = false;
for (var index = 0; index < args.Length; index++)
    switch (args[index])
    {
        case "--update": update = true; break;
        // The gate's own tests compare an existing report with altered baselines.
        case "--reuse-report": reuse = true; break;
        case "--baseline" when index + 1 < args.Length: baselinePath = Path.GetFullPath(args[++index]); break;
        default: throw new ArgumentException(Usage);
    }
var directory = At("artifacts/SelfAdmission");
Directory.CreateDirectory(directory);

// Every metadata method, constructors and compiler-generated members included, under one profile.
string[] signatures;
using (var module = ModuleDefinition.ReadModule(ExtractorPath))
    signatures = module.GetTypes().SelectMany(type => type.Methods).Select(method => method.FullName)
        .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
var manifest = Path.Combine(directory, "manifest.json");
if (!reuse)
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        entries = signatures.Select(signature => new { signature, profile = Profile })
    }));
var report = Path.Combine(directory, "blockers.json");
var timer = Stopwatch.StartNew();
if (!reuse) Run(["dotnet", ExtractorPath, "blockers", ExtractorPath, "--manifest", manifest, "--output", report]);
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
string[] Lines(IDictionary<string, char> statuses) =>
    ["status\tmethod", .. statuses.Select(pair => $"{pair.Value}\t{pair.Key}")];
if (update) File.WriteAllText(baselinePath, string.Join('\n', Lines(current)) + "\n");

var baseline = File.ReadAllLines(baselinePath).Skip(1).Select(line => line.Split('\t', 2))
    .ToDictionary(fields => fields[1], fields => fields[0][0], StringComparer.Ordinal);
bool Admitted(IDictionary<string, char> statuses, string method) =>
    statuses.TryGetValue(method, out var status) && status == 'A';
var lost = baseline.Keys.Where(method => Admitted(baseline, method) && current.ContainsKey(method) &&
    !Admitted(current, method)).ToArray();
var gained = current.Keys.Where(method => baseline.ContainsKey(method) && !Admitted(baseline, method) &&
    Admitted(current, method)).ToArray();
var added = current.Keys.Where(method => !baseline.ContainsKey(method)).ToArray();
var removed = baseline.Keys.Where(method => !current.ContainsKey(method)).Order(StringComparer.Ordinal).ToArray();
var reclassified = current.Keys.Count(method => baseline.TryGetValue(method, out var status) &&
    status != current[method] && !Admitted(baseline, method) && !Admitted(current, method));

int Count(char status) => current.Values.Count(value => value == status);
var blockers = document.RootElement.GetProperty("blockers").EnumerateArray().ToArray();
var summary = new List<string>
{
    "# Self-admission of Nethermind.LeanCIL.dll", "",
    $"Admission under the `{Profile}` profile; nothing here is proved. Gated on lost admissions only.", "",
    "| Methods | Admitted | Blocked | Not checked | Distinct blockers | Seconds |",
    "| ---: | ---: | ---: | ---: | ---: | ---: |",
    $"| {current.Count} | {Count('A')} | {Count('B')} | {Count('N')} | {blockers.Length} | {elapsed:F1} |", "",
    $"Since the baseline: {lost.Length} lost, {gained.Length} gained, {added.Length} added " +
        $"({added.Count(method => Admitted(current, method))} admitted), {removed.Length} removed " +
        $"({removed.Count(method => Admitted(baseline, method))} admitted), " +
        $"{reclassified} moved between blocked and not checked.", ""
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
List("Lost admissions (fail):", lost);
List("Gained admissions (record with `--update`):", gained);
List("Added and admitted:", added.Where(method => Admitted(current, method)));
List("Removed admitted methods:", removed.Where(method => Admitted(baseline, method)));
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
Console.WriteLine($"PASS self-admission: {Count('A')} of {current.Count} methods admitted, none lost");
