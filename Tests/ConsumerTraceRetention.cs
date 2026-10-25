#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ConsumerTraceDirectory.cs
#:include ../scripts/VerificationTimings.cs

var root = Path.Combine(Path.GetTempPath(), "LeanCIL-TraceRetention-" + Guid.NewGuid().ToString("N"));
var savedTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
try
{
    var parent = Path.Combine(root, "verification-traces");
    var fallback = Path.Combine(root, "artifacts");
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", parent);
    var consumer = ConsumerTraceDirectory.Create(fallback, "ConsumerTrace");
    var otherConsumer = ConsumerTraceDirectory.Create(fallback, "ConsumerTrace");
    if (consumer == otherConsumer || Path.GetDirectoryName(consumer) != parent || Directory.Exists(fallback))
        throw new InvalidOperationException("Consumer traces must be isolated beneath the configured parent.");

    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", consumer);
    var progress = ConsumerTraceDirectory.Create(fallback, "ConsumerProgressTrace");
    WriteStage(consumer, "consumer");
    WriteStage(progress, "progress");
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", parent);
    if (Directory.GetFiles(consumer, "*.jsonl").Length != 1)
        throw new InvalidOperationException("Progress traces must not enter consumer-local assertions.");
    var records = VerificationTimings.Collect(parent);
    if (records.Count != 2 || records.Select(record => record["stage"]!.GetValue<string>()).Distinct().Count() != 2)
        throw new InvalidOperationException("The artifact collector must retain each child stage exactly once.");
    foreach (var record in records)
    {
        var trace = Path.Combine(parent, record["traceFile"]!.GetValue<string>());
        var transcript = Path.Combine(Path.GetDirectoryName(trace)!, record["transcript"]!.GetValue<string>());
        if (File.ReadAllText(transcript) != record["stage"]!.GetValue<string>())
            throw new InvalidOperationException("Retained transcripts must resolve relative to their trace file.");
    }
    if (!VerificationTimings.Markdown(VerificationTimings.Summarize(records), records.Count)
        .Contains("Durations are inclusive:", StringComparison.Ordinal))
        throw new InvalidOperationException("The summary must explain overlapping parent and child timings.");

    foreach (var configuredRoot in new string?[] { null, " " })
    {
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", configuredRoot);
        var local = ConsumerTraceDirectory.Create(fallback, "ConsumerTrace");
        if (Path.GetDirectoryName(local) != fallback)
            throw new InvalidOperationException("Standalone tests must retain traces under their fallback root.");
    }
    Console.WriteLine("PASS consumer trace isolation, retention, transcript paths and inclusive collection");
}
finally
{
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", savedTrace);
    if (Directory.Exists(root)) Directory.Delete(root, true);
}

static void WriteStage(string directory, string stage)
{
    File.WriteAllText(Path.Combine(directory, "stage.log"), stage);
    File.WriteAllText(Path.Combine(directory, "stage.jsonl"), System.Text.Json.JsonSerializer.Serialize(new
    {
        stage, suite = "consumer", durationSeconds = 1, exitCode = 0,
        command = new[] { "fixture" }, transcript = "stage.log"
    }) + "\n");
}
