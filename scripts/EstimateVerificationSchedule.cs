#!/usr/bin/env dotnet
#:property PublishAot=false
#:include VerificationSelection.cs
#:include Documentation.cs
#:include ExportVerificationSuites.cs
#:include VerificationSuites.cs

using System.Globalization;
using System.Runtime.CompilerServices;
using System.Text.Json;

// Compare queue schedules without running or skipping verification suites.
// With --jobs, print the jobs a full run is packed into and what they are estimated to take.
static string Source([CallerFilePath] string path = "") => path;
using var measured = JsonDocument.Parse(File.ReadAllText(Path.Combine(
    Path.GetDirectoryName(Source())!, "verification-durations.json")));
var durations = measured.RootElement.GetProperty("seconds").EnumerateObject()
    .ToDictionary(property => property.Name, property => property.Value.GetDouble(), StringComparer.Ordinal);
if (durations.Count == 0 || durations.Values.Any(value => !double.IsFinite(value) || value <= 0))
    throw new InvalidDataException("Suite durations must be positive numbers");
var alphabetical = durations.Keys.Order(StringComparer.Ordinal).ToArray();
var longest = alphabetical.OrderByDescending(name => durations[name]).ToArray();

double Elapsed(IEnumerable<string> order, int workers)
{
    var available = new PriorityQueue<double, double>();
    for (var i = 0; i < workers; i++) available.Enqueue(0, 0);
    foreach (var suite in order)
    {
        var finish = available.Dequeue() + durations[suite];
        available.Enqueue(finish, finish);
    }
    return available.UnorderedItems.Max(item => item.Element);
}

if (args.Contains("--jobs"))
{
    // Measured across one run: checkout, toolchain, library and tool restores, and uploads of a job.
    const double setupSeconds = 52;
    const int runners = 8;
    var jobs = VerificationSelection.Groups(alphabetical).Select(group =>
        (group.Suite, group.Suites, Seconds: group.Suites.Sum(suite => durations[suite]) + setupSeconds)).ToArray();
    string Minutes(double seconds) => (seconds / 60).ToString("F1", CultureInfo.InvariantCulture);
    Console.WriteLine("| Job | Suites | Estimated minutes |\n| --- | --- | ---: |");
    foreach (var job in jobs)
        Console.WriteLine($"| {job.Suite} | {string.Join(" ", job.Suites)} | {Minutes(job.Seconds)} |");
    var free = new PriorityQueue<double, double>();
    for (var i = 0; i < runners; i++) free.Enqueue(0, 0);
    foreach (var job in jobs)
    {
        var finish = free.Dequeue() + job.Seconds;
        free.Enqueue(finish, finish);
    }
    var wall = free.UnorderedItems.Max(item => item.Element);
    Console.WriteLine($"\n{jobs.Length} jobs for {durations.Count} suites: " +
        $"{Minutes(jobs.Sum(job => job.Seconds))} job-minutes, of which {Minutes(jobs.Length * setupSeconds)} " +
        $"setup; {Minutes(wall)} minutes on {runners} runners. One job per suite would spend " +
        $"{Minutes(durations.Count * setupSeconds)} on setup.");
    return;
}
var estimates = new Dictionary<string, double> { ["alphabetical4"] = Elapsed(alphabetical, 4) };
foreach (var workers in new[] { 4, 8, 12 }) estimates["longestFirst" + workers] = Elapsed(longest, workers);
Console.WriteLine(JsonSerializer.Serialize(new
{
    measurementRun = measured.RootElement.GetProperty("workflowRun").GetString(),
    assumptions = "Fixed measured job durations; immediate dispatch when a worker is free. " +
        "Excludes the new preparation job, artifact transfer, runner queueing and library-reuse savings. " +
        "This is a scheduling estimate, not a measured optimized workflow run.",
    suiteCount = durations.Count,
    totalMeasuredJobSeconds = durations.Values.Sum(),
    estimatedSeconds = estimates,
    order = longest
}, new JsonSerializerOptions { WriteIndented = true }));
