#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ConsumerTraceDirectory.cs

using System.Diagnostics;
using System.Text.Json;

var measureOnly = args.Contains("--measure", StringComparer.Ordinal);
var cli = new[] { "dotnet", args.FirstOrDefault(value => value != "--measure") ?? ExtractorPath };
var directory = At("artifacts/ConsumerCertificateReuse-" + Guid.NewGuid().ToString("N"));
var previousCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR") ??
    Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL", "libraries");
var isolatedCache = Path.Combine(directory, "Cache");
Directory.CreateDirectory(isolatedCache);
using (var setup = new Program())
{
    var (key, _) = setup.LibraryIdentity(CommonInputs());
    var candidate = Path.Combine(previousCache, key);
    // Copy only this framework/toolchain entry; the CLI still authenticates it normally.
    if (Directory.Exists(candidate)) CopyTree(candidate, Path.Combine(isolatedCache, key));
}
Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", isolatedCache);
var package = Path.Combine(directory, "Package");
Directory.CreateDirectory(package);
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
var revision = Run(["git", "rev-parse", "HEAD"]).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"certificate-reuse\"\n[[require]]\nname = \"leancil\"\ngit = " +
    JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " + JsonSerializer.Serialize(revision) + "\n");
Run(["lake", "update"], package);
var output = Path.Combine(directory, "Extraction");
var proof = Path.Combine(package, "Proof.lean");
File.WriteAllText(proof, """
import Extracted
namespace ExampleProof
/-- The extracted program satisfies its translation evidence. -/
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
void Verify(string label, bool expectedBuild)
{
    // Each invocation has a distinct proof source, so a whole-result receipt cannot satisfy it.
    File.AppendAllText(proof, "\n-- " + label + "\n");
    var previous = Directory.GetFiles(trace, "*.jsonl").ToHashSet(StringComparer.Ordinal);
    var timer = Stopwatch.StartNew();
    Run([.. cli, "verify", output, "--proof", proof, "--proof-root", package]);
    timer.Stop();
    var stages = Directory.EnumerateFiles(trace, "*.jsonl").Where(path => !previous.Contains(path))
        .SelectMany(File.ReadLines).Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
    string Transcript(JsonElement stage) => File.ReadAllText(Path.Combine(trace,
        stage.GetProperty("transcript").GetString()!));
    var certificate = stages.Single(stage =>
        stage.GetProperty("stage").GetString() == "Checking consumer extraction certificate");
    var certificateBuild = Transcript(certificate);
    var built = System.Text.RegularExpressions.Regex.IsMatch(certificateBuild, @"\bBuilt Extracted(?:\s|$)");
    var auditBuilt = System.Text.RegularExpressions.Regex.IsMatch(certificateBuild,
        @"\bBuilt ExtractionAudit(?:\s|$)");
    var replay = stages.Where(stage => stage.GetProperty("stage").GetString() is
        "Kernel replay of consumer proof and dependencies" or "Joint kernel replay of consumer proof and dependencies")
        .ToArray();
    var replayed = replay.SelectMany(stage => Transcript(stage).Split('\n').Where(line => line.StartsWith('{')))
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line).GetProperty("module").GetString()).ToArray();
    if ((!measureOnly && (built != expectedBuild || auditBuilt != expectedBuild)) || !replayed.Contains("Extracted") ||
        !replayed.Contains("ExtractionAudit") || !replayed.Contains("LeanCILProof"))
        throw new InvalidOperationException("Certificate build/replay mismatch: " + label);
    var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
    if (!report.GetProperty("extractionAudit").GetString()!.Contains("ExtractionAudit.valid") ||
        report.GetProperty("libraryBuild").GetString() == "consumer-proof-cache")
        throw new InvalidOperationException("Missing fresh certificate audit: " + label);
    measurements.Add(new { label, seconds = timer.Elapsed.TotalSeconds, built, auditBuilt,
        certificateSeconds = certificate.GetProperty("durationSeconds").GetDouble(),
        replaySeconds = replay.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()), replayed });
    Console.WriteLine((measureOnly ? "MEASURE" : "PASS") + " consumer certificate " + label);
}
Extract("scalar");
Verify("initial", expectedBuild: true);
Verify("unchanged", expectedBuild: false);
var corrupted = 0;
Directory.CreateDirectory(SuccessCacheRoot);
foreach (var generation in Directory.EnumerateDirectories(SuccessCacheRoot))
{
    var files = Path.Combine(generation, "files");
    if (!File.Exists(Path.Combine(files, "leancil-support.json"))) continue;
    var artifacts = Directory.GetFiles(files, "Extracted.olean", SearchOption.AllDirectories);
    if (artifacts.Length == 0) continue;
    foreach (var artifact in artifacts) File.AppendAllText(artifact, "corrupted certificate");
    // Updating the untrusted hashes cannot renew the producer's HMAC.
    File.WriteAllBytes(Path.Combine(generation, "receipt.json"),
        JsonSerializer.SerializeToUtf8Bytes(CacheFiles(files)));
    corrupted++;
}
if (!measureOnly && corrupted == 0) throw new InvalidOperationException("No certified extraction artifact to corrupt.");
Verify("self-rehashed-corruption", expectedBuild: true);
Extract("x64-v3");
Verify("changed-extraction", expectedBuild: true);
File.AppendAllText(Path.Combine(output, "Extracted.lean"), "\n-- changed after certification\n");
var tampered = Execute([.. cli, "verify", output, "--proof", proof, "--proof-root", package]);
if (tampered.Code != 1 || !tampered.Output.Contains("differs from regenerated CIL", StringComparison.Ordinal) ||
    File.Exists(Path.Combine(output, "verified.json")))
    throw new InvalidOperationException("Cached certificate bypassed extraction regeneration: " + tampered.Output);
Console.WriteLine("PASS cached certificate cannot bypass generated-source tampering rejection");
File.WriteAllText(Path.Combine(directory, "timings.json"), JsonSerializer.Serialize(measurements, Json));
Console.WriteLine("Measurements: " + Path.Combine(directory, "timings.json"));
