#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Diagnostics;
using System.Text.Json;
using Mono.Cecil;

// Admission of LeanCIL's own assembly under the scalar profile, gated on admitted methods only.
// Fails only when a method admitted in the baseline still exists and is no longer admitted.
const string Usage = "Usage: SelfAdmission.cs [--update] [--baseline baseline.txt] [--reuse-report]";
const string Profile = "scalar";
const int ListedBlockers = 10;
const int ListedMethods = 20;
var baselinePath = At("Tests/SelfAdmissionBaseline.txt");
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
// The baseline lists admitted methods only; whether a non-admitted method is new does not matter.
var admitted = current.Where(pair => pair.Value == 'A').Select(pair => pair.Key).ToArray();
if (update) File.WriteAllText(baselinePath, string.Concat(admitted.Select(method => method + "\n")));
var baseline = File.ReadAllLines(baselinePath).Where(line => line.Length != 0)
    .ToHashSet(StringComparer.Ordinal);
var lost = baseline.Where(method => current.TryGetValue(method, out var status) && status != 'A')
    .Order(StringComparer.Ordinal).ToArray();
var removed = baseline.Where(method => !current.ContainsKey(method)).Order(StringComparer.Ordinal).ToArray();
var gained = admitted.Where(method => !baseline.Contains(method)).ToArray();

int Count(char status) => current.Values.Count(value => value == status);
var blockers = document.RootElement.GetProperty("blockers").EnumerateArray().ToArray();
var summary = new List<string>
{
    "# Self-admission of Nethermind.LeanCIL.dll", "",
    $"Admission under the `{Profile}` profile; nothing here is proved. Gated on lost admissions only.", "",
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
List("Lost admissions (fail):", lost);
List("Gained admissions (record with `--update`):", gained);
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
Console.WriteLine($"PASS self-admission: {Count('A')} of {current.Count} methods admitted, none lost");
