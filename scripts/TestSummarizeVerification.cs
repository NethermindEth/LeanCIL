#!/usr/bin/env dotnet
#:property PublishAot=false
#:include VerificationTimings.cs

using System.Text.Json.Nodes;

static JsonObject Record(string stage = "Proof", double seconds = 2, int exitCode = 0, string suite = "loops") => new()
{
    ["stage"] = stage, ["durationSeconds"] = seconds, ["exitCode"] = exitCode,
    ["suite"] = suite, ["transcript"] = "command.log", ["command"] = new JsonArray("lean", "Proof.lean")
};

static void Require(bool condition)
{
    if (!condition) throw new InvalidOperationException("Timing regression failed");
}

var directory = Path.Combine(Path.GetTempPath(), "leancil-timings-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(directory);
try
{
    var path = Path.Combine(directory, "stages.jsonl");
    var first = Record();
    first["futureProperty"] = new JsonObject { ["nested"] = new JsonArray(1, "preserved") };
    File.WriteAllText(path, string.Join('\n', new[] { first, Record(seconds: 3, exitCode: 1), Record(suite: "core") }.Select(record => record.ToJsonString())));
    var records = VerificationTimings.Collect(directory);
    Require(records.Count == 3 && records.All(record => JsonNode.DeepEquals(record["command"], new JsonArray("lean", "Proof.lean"))));
    Require(records[1]["traceLine"]!.GetValue<int>() == 2 && JsonNode.DeepEquals(records[0]["futureProperty"], first["futureProperty"]));
    var groups = VerificationTimings.Summarize(records);
    Require(groups[0].Suite == "loops" && groups[0].DurationSeconds == 5 && groups[0].Failures == 1);
    VerificationTimings.Run(["--root", directory, "--output", Path.Combine(directory, "summary.json"), "--markdown", Path.Combine(directory, "summary.md")]);
    var saved = JsonNode.Parse(File.ReadAllText(Path.Combine(directory, "summary.json")))!;
    Require(saved["stages"]![0]!["stage"]!.GetValue<string>() == "Proof" && JsonNode.DeepEquals(saved["records"]![0]!["futureProperty"], first["futureProperty"]));
    Console.WriteLine("PASS preserves all records and aggregates by suite and stage");

    var report = VerificationTimings.Markdown(VerificationTimings.Summarize([Record("Suite loops", 20), Record("Proof", 10)]), 2);
    Require(report.Contains("overlap") && report.Contains("must not be added") && report.Contains("intentionally rejected"));
    Console.WriteLine("PASS nested stages do not claim wall time");

    Require(VerificationTimings.Markdown([], 0).Contains("No completed stage timings"));
    Console.WriteLine("PASS missing stages are not reported as success");

    foreach (var value in new[] { "{", Record(seconds: -1).ToJsonString(), Record().ToJsonString().Replace("\"durationSeconds\":2", "\"durationSeconds\":NaN"),
        Record().ToJsonString().Replace("\"durationSeconds\":2", "\"durationSeconds\":true"), "{\"stage\":\"Proof\"}", "[]", "null" })
    {
        File.WriteAllText(path, value);
        var rejected = false;
        try { VerificationTimings.Collect(directory); }
        catch (FormatException error) when (error.Message.Contains("stages.jsonl:1")) { rejected = true; }
        Require(rejected);
    }
    Console.WriteLine("PASS corrupt and invalid records fail explicitly");

    groups = VerificationTimings.Summarize(Enumerable.Range(0, 40).Select(index => Record(stage: $"Proof {index}")));
    Require(groups.Count == 40 && VerificationTimings.Markdown(groups, 40).Split("| loops |").Length - 1 == 20);
    Console.WriteLine("PASS summary is bounded without dropping structured stages");
    Console.WriteLine("All 5 timing summary checks passed.");
}
finally
{
    Directory.Delete(directory, true);
}
