#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ConsumerTraceDirectory.cs

using System.Diagnostics;
using System.Text.Json;
using System.Text.RegularExpressions;

var measure = args.Contains("--measure", StringComparer.Ordinal);
var cli = new[] { "dotnet", args.FirstOrDefault(argument => argument != "--measure") ?? ExtractorPath };
var directory = At("artifacts/ConsumerComponents-" + Guid.NewGuid().ToString("N"));
var assemblyRoot = Path.Combine(directory, "Assembly");
var package = Path.Combine(directory, "Package");
Directory.CreateDirectory(assemblyRoot);
Directory.CreateDirectory(package);
File.WriteAllText(Path.Combine(assemblyRoot, "Components.csproj"), """
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
</Project>
""");
File.WriteAllText(Path.Combine(assemblyRoot, "Methods.cs"), """
public static class Methods
{
    public static ulong First(ulong value) => Helper(value) + 1;
    public static ulong Second(ulong value) => Helper(value) + 2;
    public static ulong Third(ulong value) => Helper(value) + 3;
    public static ulong Fourth(ulong value) => Helper(value) + 4;
    public static ulong Helper(ulong value)
    {
        BODY
        return value;
    }
}
""".Replace("BODY", string.Join("\n", Enumerable.Range(1, 24).Select(index =>
    "value = unchecked((value + " + index + "UL) ^ (value >> 3));")), StringComparison.Ordinal));
Run(["dotnet", "build", assemblyRoot, "-c", "Release", "-o", Path.Combine(assemblyRoot, "output")]);
var assembly = Path.Combine(assemblyRoot, "output/Components.dll");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"component-reuse\"\n[[require]]\nname = \"leancil\"\ngit = " +
    JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " +
    JsonSerializer.Serialize(Run(["git", "rev-parse", "HEAD"]).Trim()) + "\n");
Run(["lake", "update"], package);
var proof = Path.Combine(package, "Proof.lean");
File.WriteAllText(proof, """
import Extracted
namespace ExampleProof
/-- Every method and connection in this extraction satisfies the translation validator. -/
theorem correctness : CIL.Extraction.TranslationValid Extracted.rawLayouts Extracted.computedLayouts
    Extracted.methodEvidence Extracted.imports Extracted.program := Extracted.translation_valid
#print axioms correctness
end ExampleProof
""");
var requests = new[] { "First", "Second", "Third", "Fourth" }.Select(method =>
{
    var output = Path.Combine(directory, method);
    Run([.. cli, "extract", assembly, "Methods::" + method + "(ulong)", output]);
    return new { output, proof, theorem = "ExampleProof.correctness" };
}).ToArray();
var first = SplitExtractionComponents(File.ReadAllText(Path.Combine(requests[0].output, "Extracted.lean")));
var second = SplitExtractionComponents(File.ReadAllText(Path.Combine(requests[1].output, "Extracted.lean")));
var reused = first.Sources.Keys.Intersect(second.Sources.Keys).ToArray();
if (first.Sources.Count != 3 || reused.Length != 2)
    throw new Exception("Expected independent shared profile/layout and helper components.");
var plans = requests.Select(request => SplitExtractionComponents(
        File.ReadAllText(Path.Combine(request.output, "Extracted.lean"))))
    .Select(plan => SharedExtractionComponents(plan, reused.ToHashSet(StringComparer.Ordinal))).ToArray();
var sourceBytes = requests.Sum(request => new FileInfo(Path.Combine(request.output, "Extracted.lean")).Length);
var factoredBytes = plans.Sum(plan => (long)System.Text.Encoding.UTF8.GetByteCount(plan.Aggregate)) +
    plans.SelectMany(plan => plan.Sources).DistinctBy(pair => pair.Key)
        .Sum(pair => (long)System.Text.Encoding.UTF8.GetByteCount(pair.Value));
var original = File.ReadAllText(Path.Combine(requests[0].output, "Extracted.lean"));
var changedProfile = SplitExtractionComponents(original
    .Replace("nativeWidth := 64", "nativeWidth := 32", StringComparison.Ordinal));
if (changedProfile.Sources.Keys.Intersect(first.Sources.Keys).Any())
    throw new Exception("A changed header retained dependent component identities.");
var helperStart = original.IndexOf("def method1Signature", StringComparison.Ordinal);
var changedHelper = SplitExtractionComponents(original[..helperStart] + original[helperStart..]
    .Replace(".add", ".sub", StringComparison.Ordinal));
if (changedHelper.Sources.Keys.Intersect(first.Sources.Keys).Count() != 2)
    throw new Exception("A changed helper did not invalidate exactly its checked component.");
var changedCall = SplitExtractionComponents(original.Replace(".call 1 1", ".call 0 1", StringComparison.Ordinal));
if (changedCall.Sources.Keys.Intersect(first.Sources.Keys).Count() != 2 || changedCall.InputHash == first.InputHash)
    throw new Exception("A changed callee connection retained the caller component or input identity.");
var saved = new[] { "LEANCIL_DISABLE_SUCCESS_CACHE", "LEANCIL_TRACE_DIRECTORY" }
    .ToDictionary(name => name, Environment.GetEnvironmentVariable);
try
{
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
    // A supplied library is already prepared; the batch authenticates it and verifies every request.
    if (string.IsNullOrWhiteSpace(Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY")))
        Run([.. cli, "verify", requests[0].output, "--proof", proof, "--proof-root", package]);
    var trace = ConsumerTraceDirectory.Create(directory, "Trace");
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
    var manifest = Path.Combine(directory, "batch.json");
    File.WriteAllText(manifest, JsonSerializer.Serialize(new { schema = 1, proofRoot = package, requests }));
    var timer = Stopwatch.StartNew();
    Run([.. cli, "verify-batch", manifest, "--parallel", "1"]);
    timer.Stop();
    var stages = Directory.GetFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
    string Transcript(JsonElement stage) => File.ReadAllText(Path.Combine(trace,
        stage.GetProperty("transcript").GetString()!));
    var certificates = stages.Where(stage => stage.GetProperty("stage").GetString() ==
        "Checking consumer extraction certificate").ToArray();
    var replays = stages.Where(stage => stage.GetProperty("stage").GetString() is
        "Kernel replay of consumer proof and dependencies" or
        "Joint kernel replay of consumer proof and dependencies").ToArray();
    var replayed = replays.SelectMany(stage => Transcript(stage).Split('\n').Where(line => line.StartsWith('{')))
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line).GetProperty("module").GetString()).ToArray();
    var builds = certificates.SelectMany(stage => Regex.Matches(Transcript(stage),
        @"\bBuilt (LeanCILComponent_[a-f0-9]+)(?:\s|$)").Select(match => match.Groups[1].Value)).ToArray();
    if (!measure && (reused.Any(module => builds.Count(name => name == module) != 1 ||
            replayed.Count(name => name == module) != 1) || replayed.Count(name => name == "Extracted") != 4 ||
            replayed.Contains("ExtractionAudit")))
        throw new Exception("Components did not compile/replay once while all complete certificates were checked.");
    File.WriteAllText(Path.Combine(directory, "timings.json"), JsonSerializer.Serialize(new
    {
        seconds = timer.Elapsed.TotalSeconds,
        certificateSeconds = certificates.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()),
        replaySeconds = replays.Sum(stage => stage.GetProperty("durationSeconds").GetDouble()),
        reused, builds, replayed,
        sourceBytes, factoredBytes
    }, Json));
    if (!measure)
    {
        // A matching module name in consumer sources cannot supply a generated component.
        var shadow = Path.Combine(package, reused[0] + ".lean");
        File.WriteAllText(shadow, "axiom forged : False\n");
        try
        {
            var result = Execute([.. cli, "verify-batch", manifest, "--parallel", "1"]);
            if (result.Code == 0 || !result.Output.Contains("shadows a consumer source", StringComparison.Ordinal) ||
                File.Exists(Path.Combine(requests[0].output, "verified.json")))
                throw new Exception("A shadowed extraction component was not rejected without a certificate.");
        }
        finally { File.Delete(shadow); }
    }
    Console.WriteLine("PASS checked extraction component reuse: " + directory);
}
finally
{
    foreach (var (name, value) in saved) Environment.SetEnvironmentVariable(name, value);
}
