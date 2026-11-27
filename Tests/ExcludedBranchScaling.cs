#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include GeneratedEvidence.cs

using System.Text.Json;

// A long branch excluded by the scalar profile leaves hundreds of pruned sites. Per-site
// indexed lookups made the generated parameter and feature checks exceed the default budget.
var directory = At("artifacts/ExcludedBranchScaling");
var source = Path.Combine(directory, "Assembly");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Excluded.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net11.0</TargetFramework>
<Optimize>true</Optimize></PropertyGroup></Project>
""");
File.WriteAllText(Path.Combine(source, "Excluded.cs"),
    "public static class Excluded { public static ulong Accumulate(ulong x, ulong y) { " +
    "if (System.Runtime.Intrinsics.X86.Avx2.IsSupported) { ulong word = x; " +
    string.Concat(Enumerable.Repeat("word = word * y + x; ", 200)) + "return word; } return x + y; } }");
Run(["dotnet", "build", Path.Combine(source, "Excluded.csproj"), "-c", "Release"]);
var assembly = Path.Combine(source, "bin/Excluded.dll");
var output = Path.Combine(directory, "Extraction");
Run(Extract("extract", assembly, "Excluded", "Excluded::Accumulate(ulong,ulong)", output));
var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));

string[] Reachability(string source)
{
    const string prefix = "def method0Reachable : List Bool := [";
    var mask = source.Split('\n').Single(line => line.StartsWith(prefix, StringComparison.Ordinal)).TrimEnd();
    return mask[prefix.Length..^1].Split(", ");
}
var reachable = Reachability(extracted);
var closed = ClosedBody(extracted, 0).Literal;
var excluded = reachable.Count(live => live == "false");
if (excluded < 700 || extracted.Contains("set_option maxHeartbeats"))
    throw new InvalidOperationException($"Expected a large excluded branch checked at the default budget; found {excluded} excluded sites.");
const string featureObligation = "method0_features_validated";
const string parameterObligation = "method0_parameters_validated";
var controls =
    CheckedEvidenceControl(extracted, NarrowEvidence(extracted, featureObligation), [featureObligation], 0) +
    CheckedEvidenceControl(extracted, NarrowEvidence(extracted, parameterObligation), [parameterObligation], 1);

// Live under AVX2, the same branch is reachable; elaborator `decide` exceeded the budget on bodies this long.
var liveOutput = Path.Combine(directory, "Live");
Run(Extract("extract", assembly, "Excluded", "Excluded::Accumulate(ulong,ulong)", liveOutput, "x64-v3"));
var liveExtracted = File.ReadAllText(Path.Combine(liveOutput, "Extracted.lean"));
var liveSites = Reachability(liveExtracted).Count(site => site == "true");
if (liveSites < 800 || liveExtracted.Contains("set_option maxHeartbeats"))
    throw new InvalidOperationException($"Expected a long live branch checked at the default budget; found {liveSites} live sites.");
Run(["lake", "env", "lean", Path.Combine(liveOutput, "Extracted.lean")], cwd: FixturePackage());
Console.WriteLine($"PASS {liveSites} live sites validate at the default heartbeat budget");

// Each validator must still reach and reject a forged claim at the last pruned site it checks. A decoded method
// decodes the mask it is given, so a pinned run decodes the extracted mask and keeps its holes.
void Reject(string name, string validator, string obligation, Func<int, bool> site, bool pinnedCode = false)
{
    var live = (string[])reachable.Clone();
    var pc = Enumerable.Range(0, live.Length).Last(i => live[i] == "false" && site(i));
    live[pc] = "true";
    // The method has no locals, so the forged state is well shaped and only the check at the claimed site rejects it.
    if (!closed.Contains("], locals := [], initLocals", StringComparison.Ordinal))
        throw new InvalidOperationException(
            "The excluded-branch method has locals; the forged state may be badly shaped.");
    var tampered = Path.Combine(directory, name + ".lean");
    const string statePrefix = "def method0FeatureStates : Extraction.FeatureCertificate := ";
    var originalMask = extracted.Split('\n').Single(line => line.StartsWith("def method0Reachable ",
        StringComparison.Ordinal));
    var originalStates = extracted.Split('\n').Single(line => line.StartsWith(statePrefix, StringComparison.Ordinal));
    var changed = extracted.Replace(originalMask, $"def method0Reachable : List Bool := [{string.Join(", ", live)}]",
        StringComparison.Ordinal).Replace(originalStates,
            statePrefix + $"({originalStates[statePrefix.Length..].TrimEnd()} : Extraction.FeatureCertificate)" +
            $".set {pc} (some {{ stack := [], locals := [] }})", StringComparison.Ordinal);
    if (pinnedCode)
    {
        var decoder = DecodedDefinition(changed, 0);
        if (!decoder.Success) throw new InvalidOperationException("The excluded-branch method is not decoded.");
        changed = changed.Replace(decoder.Value, $"""
            {originalMask.Replace("def method0Reachable ", "def method0ExtractedReachable ", StringComparison.Ordinal)}
            {decoder.Value.Replace(" method0Reachable ", " method0ExtractedReachable ", StringComparison.Ordinal)}
            """, StringComparison.Ordinal);
    }
    File.WriteAllText(tampered, NarrowEvidence(changed, obligation));
    var rejected = Execute(["lake", "env", "lean", tampered], cwd: FixturePackage());
    if (rejected.Code == 0 || !rejected.Output.Contains($"Extraction.{validator} ", StringComparison.Ordinal) ||
        !rejected.Output.Contains("is false", StringComparison.Ordinal))
        throw new InvalidOperationException($"{validator} accepted pruned site {pc} claimed reachable:\n" + rejected.Output);
    Console.WriteLine($"PASS {validator} rejects pruned site {pc} claimed reachable");
}
var argumentCode = extracted.Split('\n').Single(l => l.StartsWith("def method0RawArguments ", StringComparison.Ordinal));
var operations = argumentCode[(argumentCode.LastIndexOf("code := [", StringComparison.Ordinal) + 9)..argumentCode.LastIndexOf(']')].Split(", ");
bool ArgumentLoad(int pc) => operations[pc].StartsWith(".load", StringComparison.Ordinal);
Reject("ForgedFeatureSite", "FeatureFlowValid", featureObligation, _ => true);
// Code decoded from the forged mask loads the argument there, so the feature flow refuses the site.
Reject("ForgedArgumentFeatures", "FeatureFlowValid", featureObligation, ArgumentLoad);
Reject("ForgedArgumentSite", "ParameterHomesValid", parameterObligation, ArgumentLoad, pinnedCode: true);

var consumer = Path.Combine(directory, "Consumer");
Directory.CreateDirectory(consumer);
var revision = Run(["git", "rev-parse", "HEAD"]).Trim();
File.WriteAllText(Path.Combine(consumer, "lakefile.toml"),
    $"name = \"excluded\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(consumer, "lean-toolchain"), true);
var proof = Path.Combine(consumer, "Proof.lean");
File.WriteAllText(proof, """
import Extracted
#guard Extracted.method0FeatureStates.length == Extracted.method0Reachable.length
namespace ExampleProof
def empty : CIL.Safety.Memory := { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }
-- Only this user proof's `rfl` needs depth to reach the scalar path ~800 instructions in; generated evidence keeps the defaults.
set_option maxRecDepth 4096 in
theorem correctness :
    (CIL.Safety.invoke Extracted.program 16 0 [.scalar (.i64 2), .scalar (.i64 3)] empty).map Prod.snd =
      .ok [.scalar (.i64 5)] := by rfl
end ExampleProof
""" + "\n" + controls);
Run(["lake", "update"], consumer);
// This fresh certificate build also checks the scalar positive at the default heartbeat budget.
// The consumer's independent replay includes both narrowed controls and the complete certificate.
Run(["dotnet", ExtractorPath, "verify", output, "--proof", proof, "--proof-root", consumer],
    environment: new Dictionary<string, string> { ["LEANCIL_DISABLE_SUCCESS_CACHE"] = "true" });
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (!report.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid") ||
    !report.GetProperty("theoremAudit").GetString()!.Contains("ExampleProof.correctness"))
    throw new InvalidOperationException("Missing independent certificate/theorem audits.");
Console.WriteLine($"PASS {excluded} excluded sites validate at the default heartbeat budget");
Console.WriteLine("PASS fresh consumer proof-root verifies the scalar path past the excluded branch");
