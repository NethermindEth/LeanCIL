#!/usr/bin/env dotnet
#:property PublishAot=false
#:include VerificationSelection.cs
#:include Documentation.cs
#:include ExportVerificationSuites.cs
#:include VerificationSuites.cs

using System.Globalization;
using System.Text.Json;

// Compare queue schedules without running or skipping verification suites.
// With --jobs, print the jobs a full run is packed into and what they are estimated to take.
var measured = VerificationSelection.ReadDurations();
var manual = new HashSet<string>(VerificationSuites.ManualSuites, StringComparer.Ordinal);
var durations = measured.Suites.Where(pair => !manual.Contains(pair.Key))
    .ToDictionary(pair => pair.Key, pair => pair.Value, StringComparer.Ordinal);
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
    var setupSeconds = measured.SetupSeconds;
    const int runners = VerificationSelection.Runners;
    var jobs = VerificationSelection.Groups(alphabetical).Select(group =>
        (group.Suite, group.Suites, Seconds: group.Suites.Sum(suite => durations[suite]) + setupSeconds +
            (group.Libraries ? measured.LibrarySeconds : 0))).ToArray();
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
        $"{Minutes(durations.Count * setupSeconds)} on setup. Includes library and per-suite proof measurements.");
    return;
}
var estimates = new Dictionary<string, double> { ["alphabetical4"] = Elapsed(alphabetical, 4) };
foreach (var workers in new[] { 4, 8, 12 }) estimates["longestFirst" + workers] = Elapsed(longest, workers);
Console.WriteLine(JsonSerializer.Serialize(new
{
    measurementRun = measured.WorkflowRun,
    assumptions = "One job per suite with immediate dispatch. Includes verified-output measurements. " +
        "Excludes shared library measurement, job setup and preparation.",
    suiteCount = durations.Count,
    totalMeasuredJobSeconds = durations.Values.Sum(),
    estimatedSeconds = estimates,
    order = longest
}, new JsonSerializerOptions { WriteIndented = true }));
