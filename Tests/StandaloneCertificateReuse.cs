#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ConsumerTraceDirectory.cs

using System.Diagnostics;
using System.Text.Json;

var measureOnly = args.Contains("--measure", StringComparer.Ordinal);
var cli = new[] { "dotnet", args.FirstOrDefault(value => value != "--measure") ?? ExtractorPath };
var directory = At("artifacts/StandaloneCertificateReuse-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(directory);
Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", Path.Combine(directory, "Cache"));
var output = Path.Combine(directory, "Extraction");
var proof = Path.Combine(directory, "Proof.lean");
File.WriteAllText(proof, """
import Extracted
namespace ExampleProof
/-- The emitted program satisfies its complete translation evidence. -/
theorem correctness : CIL.Extraction.TranslationValid Extracted.rawLayouts Extracted.computedLayouts
    Extracted.methodEvidence Extracted.imports Extracted.program := Extracted.translation_valid
#print axioms correctness
end ExampleProof
""");
var trace = ConsumerTraceDirectory.Create(directory, "Trace");
Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
var measurements = new List<object>();
void Extract(string profile) => Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"),
    "Arithmetic::Add(ulong,ulong)", output, profile]);
void Verify(string label, int expectedCompilations, params string[] options)
{
    var previous = Directory.GetFiles(trace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    var timer = Stopwatch.StartNew();
    Run([.. cli, "verify", output, "--proof", proof, .. options]);
    timer.Stop();
    var stages = Directory.EnumerateFiles(trace, "*.jsonl").Where(path => !previous.Contains(path))
        .SelectMany(File.ReadLines).Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
    var compilations = stages.Where(stage =>
        stage.GetProperty("stage").GetString()!.StartsWith("Checking Extracted:", StringComparison.Ordinal) ||
        stage.GetProperty("stage").GetString()!.StartsWith("Checking ExtractionAudit:", StringComparison.Ordinal) ||
        stage.GetProperty("stage").GetString()!.StartsWith("Checking Proof:", StringComparison.Ordinal)).ToArray();
    if (!measureOnly && compilations.Length != expectedCompilations)
        throw new InvalidOperationException("Unexpected standalone elaboration count: " + label);
    var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
    var certificate = report.GetProperty("extractionAudit").GetString()!;
    if (!certificate.Contains("Extracted.translation_valid", StringComparison.Ordinal) &&
        !(measureOnly && certificate.Contains("ExtractionAudit.valid", StringComparison.Ordinal)))
        throw new InvalidOperationException("Missing exact extraction certificate audit: " + label);
    var replays = stages.Where(stage => stage.GetProperty("stage").GetString() ==
        "Joint kernel replay of consumer proof and dependencies").ToArray();
    if (expectedCompilations > 0 && replays.Length == 0)
        throw new InvalidOperationException("Missing independent kernel replay: " + label);
    measurements.Add(new { label, seconds = timer.Elapsed.TotalSeconds,
        frontendProcesses = compilations.Length,
        frontendSeconds = compilations.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()) });
    Console.WriteLine((measureOnly ? "MEASURE" : "PASS") + " standalone certificate " + label);
}
Extract("scalar");
Verify("initial", 2);
Verify("unchanged", 0);
File.AppendAllText(proof, "\n-- Proof-only edit must retain the extraction certificate.\n");
Verify("proof-edit", 1);
Extract("x64-v3");
Verify("changed-extraction", 2);
Verify("fresh", 2, "--fresh");
File.WriteAllText(Path.Combine(directory, "timings.json"), JsonSerializer.Serialize(measurements, Json));
Console.WriteLine("Measurements: " + Path.Combine(directory, "timings.json"));
