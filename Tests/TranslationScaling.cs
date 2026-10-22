#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

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
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution"]);
var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
if (!extracted.Contains("method5_evidence_validated") || extracted.Contains("set_option maxHeartbeats"))
    throw new InvalidOperationException("Expected six independently checked methods at the default heartbeat budget.");
Run(["lake", "env", "lean", Path.Combine(output, "Extracted.lean")]);
var start = extracted.IndexOf("theorem translation_valid :", StringComparison.Ordinal);
var end = extracted.IndexOf("@[cil_code] theorem lookup0", start, StringComparison.Ordinal);
var old = Path.Combine(directory, "Monolithic.lean");
File.WriteAllText(old, extracted[..start] + "theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts methodEvidence imports program := by decide\n" + extracted[end..]);
var monolithic = Execute(["lake", "env", "lean", old]);
if (monolithic.Code == 0 || !monolithic.Output.Contains("maximum number of heartbeats"))
    throw new InvalidOperationException("Fixture no longer demonstrates the original default-budget failure: " + monolithic.Output);
Console.WriteLine("PASS six-method compiled fixture exceeds monolithic budget and passes compositional checking");

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
end ExampleProof
""");
Run(["lake", "update"], consumer);
Run(["dotnet", ExtractorPath, "verify", output, "--proof", proof, "--proof-root", consumer]);
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (!report.GetProperty("extractionAudit").GetString()!.Contains("ExtractionAudit.valid") ||
    !report.GetProperty("theoremAudit").GetString()!.Contains("ExampleProof.correctness"))
    throw new InvalidOperationException("Missing independent certificate/theorem audits.");
Console.WriteLine("PASS fresh consumer proof-root verifies the multi-method certificate with kernel replay and restricted axioms");
