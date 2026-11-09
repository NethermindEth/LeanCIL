#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Diagnostics;
using System.Text.Json;
using System.Text.RegularExpressions;
using Mono.Cecil;

// Admission of LeanCIL's own assembly under the scalar profile against its baseline of admitted methods.
// Fails on any difference, so a lost admission, an unrecorded gain or a removed method all need review.
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
    $"Admission under the `{Profile}` profile; nothing here is proved. Gated on an exact match with the baseline.", "",
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
// A stale baseline stops guarding the methods it omits, so unrecorded gains and removals fail too.
if (gained.Length != 0 || removed.Length != 0)
    throw new InvalidOperationException($"{baselinePath} is stale: {gained.Length} admissions gained and " +
        $"{removed.Length} admitted methods removed. Review them, then record the scan with " +
        "`dotnet run --file Tests/SelfAdmission.cs -- --update`.");
Console.WriteLine($"PASS self-admission: {Count('A')} of {current.Count} methods admitted, matching the baseline");

/// <summary>
/// The baseline's names: a method written in source, or the source method a generated one belongs to.
/// </summary>
static partial class StableNames
{
    /// <summary>
    /// <paramref name="signature"/> itself for a method written in source. A compiler-generated method
    /// (closure, lambda, local function, iterator or async state machine) is named by the source method
    /// it was generated for, since the compiler numbers it by positions that shift with unrelated edits.
    /// Generated top-level types share one name, as their numbers count across the assembly.
    /// </summary>
    internal static string Of(string signature)
    {
        if (signature.EndsWith(Generated, StringComparison.Ordinal)) return signature;
        var member = signature[(signature.IndexOf(' ', StringComparison.Ordinal) + 1)..];
        var separator = member.IndexOf("::", StringComparison.Ordinal);
        var declaring = member[..separator];
        if (declaring.StartsWith('<')) return GeneratedTypes;
        var nested = declaring.IndexOf("/<", StringComparison.Ordinal);
        var method = member[(separator + 2)..];
        if (nested < 0 && !method.StartsWith('<')) return signature;
        var outer = nested < 0 ? declaring : declaring[..nested];
        var source = SourceName().Match((nested < 0 ? "" : declaring[nested..]) + "::" + method).Groups["name"].Value;
        return source.Length == 0 ? $"{outer} closure classes{Generated}" : $"{outer}::{source}{Generated}";
    }

    /// <summary>The suffix of every name that stands for compiler-generated methods.</summary>
    const string Generated = " (compiler-generated)";

    /// <summary>The one name of every method of a compiler-generated top-level type.</summary>
    const string GeneratedTypes = "top-level types" + Generated;

    /// <summary>How many times each name occurs.</summary>
    internal static Dictionary<string, int> Counts(IEnumerable<string> names) =>
        names.GroupBy(name => name, StringComparer.Ordinal)
            .ToDictionary(group => group.Key, group => group.Count(), StringComparer.Ordinal);

    // The first nonempty bracketed name, which the compiler sets to the method it generated code for;
    // a closure class's own constructor has none and counts toward its outer type's closure classes.
    [GeneratedRegex(@"<(?<name>[^<>]+)>")]
    private static partial Regex SourceName();
}