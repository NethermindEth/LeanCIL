#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include ../scripts/CoreExamples.cs

using System.Diagnostics;
using System.Text.Json;
using System.Text.RegularExpressions;

if (args is ["--check-existing", var existing])
{
    using var checker = new Program();
    var assembly = At("Examples/Assembly/bin/Examples.dll");
    foreach (var (name, entry) in CoreExampleSignatures)
        checker.Verify(assembly, "Examples", entry, At($"Examples/Proofs/{name}.lean"),
            Path.Combine(existing, name), check: true);
    var output = Path.Combine(existing, "Add");
    void Reject(string proof)
    {
        try { checker.Verify(assembly, "Examples", CoreExampleSignatures["Add"], proof, output, check: true); }
        catch (InvalidOperationException error) when (error.Message.Contains("Stale verification report")) { return; }
        throw new InvalidOperationException("Changed batch input was accepted");
    }
    Reject(At("Examples/Proofs/Choose.lean"));
    var batch = Path.Combine(output, "Batch.lean");
    var original = File.ReadAllBytes(batch);
    try
    {
        File.AppendAllText(batch, "\n-- changed batch source\n");
        Reject(At("Examples/Proofs/Add.lean"));
    }
    finally { File.WriteAllBytes(batch, original); }
    checker.Verify(assembly, "Examples", CoreExampleSignatures["Add"], At("Examples/Proofs/Add.lean"), output, check: true);
    Console.WriteLine("PASS all ten reports retain independent proof identity and reject changed batch source");
    return;
}
if (args is not ([] or ["--separate"]))
    throw new ArgumentException("Usage: CoreExamples.cs [--separate | --check-existing <directory>]");
var separate = args.Length > 0;
var directory = At("artifacts/CoreExamples-" + Guid.NewGuid().ToString("N"));
var trace = Path.Combine(directory, "trace");
Directory.CreateDirectory(trace);
Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
using var verification = new Program();
var timer = Stopwatch.StartNew();
verification.VerifyCoreExamples(directory, message => Console.WriteLine("PASS " + message), separate);
timer.Stop();
var records = Directory.GetFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
    .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
var modules = CoreExampleSignatures.Keys.SelectMany(name =>
    Regex.Matches(File.ReadAllText(At($"Examples/Proofs/{name}.lean")), @"(?m)^import\s+(\S+)")
        .Select(match => match.Groups[1].Value)).Distinct().ToArray();
var builds = records.Where(record => record.GetProperty("command")[0].GetString() == "lake" &&
    record.GetProperty("command")[1].GetString() == "build").ToArray();
var builtModules = builds.SelectMany(record => Regex.Matches(File.ReadAllText(Path.Combine(trace,
        record.GetProperty("transcript").GetString()!)), @"\bBuilt ([A-Za-z_][A-Za-z0-9_.]*)")
    .Select(match => match.Groups[1].Value)).ToArray();
var audits = records.Count(record => record.GetProperty("command").GetArrayLength() == 3 &&
    record.GetProperty("command")[0].GetString()!.Contains("leancil-audit") &&
    !record.GetProperty("command")[1].GetString()!.StartsWith("--", StringComparison.Ordinal));
var replayProcesses = records.Count(record =>
    record.GetProperty("stage").GetString()!.Contains("kernel replay", StringComparison.OrdinalIgnoreCase));
var measurement = new
{
    separate, seconds = timer.Elapsed.TotalSeconds, fixtures = CoreExampleSignatures.Count,
    uniqueProofContents = CoreExampleSignatures.Keys.Select(name => Sha(At($"Examples/Proofs/{name}.lean")))
        .Distinct().Count(),
    uniqueExtractionContents = CoreExampleSignatures.Keys.Select(name => Sha(Path.Combine(directory, name, "Extracted.lean")))
        .Distinct().Count(),
    distinctProofImports = modules, buildProcesses = builds.Length, builtModules, audits, replayProcesses
};
File.WriteAllText(Path.Combine(directory, "timings.json"), JsonSerializer.Serialize(measurement, Json));
Console.WriteLine(JsonSerializer.Serialize(measurement));
Console.WriteLine("Measurements: " + directory);
