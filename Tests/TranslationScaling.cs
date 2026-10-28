#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include GeneratedEvidence.cs

using System.Text.Json;

// Real compiled C# call graph: each method fits the ordinary budget, while the
// former monolithic translation proof repeats all six validators and times out.
var directory = At("artifacts/TranslationScaling");
var source = Path.Combine(directory, "Assembly");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Scaling.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
""");
var methods = Enumerable.Range(0, 6).Select(index =>
    $"public static ulong M{index}(ulong x) {{ " +
    string.Join(" ", Enumerable.Range(1, 48).Select(value => $"x = (x + {value}UL) ^ {value + index}UL;")) +
    (index == 0 ? " return M1(x) + M2(x) + M3(x) + M4(x) + M5(x); }" : " return x; }"));
File.WriteAllText(Path.Combine(source, "Scaling.cs"), "public static class Scaling { " + string.Join('\n', methods) + " }");
Run(["dotnet", "build", Path.Combine(source, "Scaling.csproj"), "-c", "Release"]);
var assembly = Path.Combine(source, "bin/Scaling.dll");
var output = Path.Combine(directory, "Extraction");
Run(Extract("extract", assembly, "Scaling", "Scaling::M0(ulong)", output));
var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
if (!extracted.Contains("method5_evidence_validated") || extracted.Contains("set_option maxHeartbeats"))
    throw new InvalidOperationException("Expected six independently checked methods at the default heartbeat budget.");
var start = extracted.IndexOf("theorem translation_valid :", StringComparison.Ordinal);
var end = extracted.IndexOf("@[cil_code] theorem lookup0", start, StringComparison.Ordinal);
var monolithicSource = extracted[..start] +
    "theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts " +
    "methodEvidence imports program := by decide\n" + extracted[end..];
void RequireHeartbeatRejection(int code, string diagnostic)
{
    var errors = diagnostic.Split('\n').Where(line => line.Contains(": error:", StringComparison.Ordinal)).ToArray();
    if (code == 0 || errors.Length != 1 ||
        !errors[0].Contains("maximum number of heartbeats", StringComparison.Ordinal))
        throw new InvalidOperationException(
            "Fixture no longer demonstrates the original default-budget failure: " + diagnostic);
}
if (args.Contains("--measure", StringComparer.Ordinal))
{
    var trace = Path.Combine(directory, "Trace-" + Guid.NewGuid().ToString("N"));
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
    Console.WriteLine("Fixed-workload prefix measurements: " + trace);
    Run(["lake", "env", "lean", Path.Combine(output, "Extracted.lean")], cwd: FixturePackage(),
        progress: "Baseline complete compositional extraction");
    var original = Path.Combine(directory, "FullMonolithic.lean");
    File.WriteAllText(original, monolithicSource);
    var result = Execute(["lake", "env", "lean", original], cwd: FixturePackage(), progress: "Baseline complete monolithic rejection");
    RequireHeartbeatRejection(result.Code, result.Output);
}
var old = Path.Combine(directory, "Monolithic.lean");
// The monolithic decision uses the raw definitions, not the already-proved component lemmas.
// The production consumer below checks the complete unchanged positive certificate once.
File.WriteAllText(old, NarrowEvidence(monolithicSource, "translation_valid"));
var monolithic = Execute(["lake", "env", "lean", old], cwd: FixturePackage(),
    progress: "Checking monolithic certificate rejection");
RequireHeartbeatRejection(monolithic.Code, monolithic.Output);
Console.WriteLine("PASS six-method compiled fixture exceeds the monolithic default budget");

var consumer = Path.Combine(directory, "Consumer");
Directory.CreateDirectory(consumer);
var revision = Run(["git", "rev-parse", "HEAD"]).Trim();
File.WriteAllText(Path.Combine(consumer, "lakefile.toml"),
    $"name = \"scaling\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(consumer, "lean-toolchain"), true);
var proof = Path.Combine(consumer, "Proof.lean");
File.WriteAllText(proof, """
import Extracted
namespace ExampleProof
theorem correctness : CIL.Extraction.TranslationValid Extracted.rawLayouts Extracted.computedLayouts
    Extracted.methodEvidence Extracted.imports Extracted.program := Extracted.translation_valid
#print axioms correctness
end ExampleProof
""");
Run(["lake", "update"], consumer);
Run(["dotnet", ExtractorPath, "verify", output, "--proof", proof, "--proof-root", consumer]);
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (!report.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid") ||
    !report.GetProperty("theoremAudit").GetString()!.Contains("ExampleProof.correctness"))
    throw new InvalidOperationException("Missing independent certificate/theorem audits.");
Console.WriteLine("PASS fresh consumer proof-root verifies the multi-method certificate with kernel replay and restricted axioms");
