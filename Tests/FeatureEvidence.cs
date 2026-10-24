#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/RuntimeProfileValidation.cs

using System.Text.RegularExpressions;
using System.Reflection;
using System.Text.Json;
using System.Text.Json.Nodes;

using var verification = new Program();
var output = At("artifacts/FeatureEvidence");
Directory.CreateDirectory(output);
// Exercise the production validator and both old-name and custom-profile migration paths.
var profileType = Assembly.LoadFrom(ExtractorPath).GetType("Nethermind.LeanCIL.FeatureProfile", throwOnError: true)!;
var selectProfile = profileType.GetMethod("Select", BindingFlags.Static | BindingFlags.NonPublic)!;
object SelectProfile(string name) => selectProfile.Invoke(null, [name])!;
var jsonOptions = new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.CamelCase };
var sharedCases = RuntimeProfileValidation.Observations(
    Directory.GetFiles(At("docs/evidence/runtime-profiles"), "*.json")).ToList();
foreach (var name in new[] { "scalar", "x64-sse2", "x64-sse42", "x64-v3", "x64-v4", "arm64-advsimd" })
    sharedCases.Add((JsonSerializer.Serialize(SelectProfile(name), jsonOptions), true));
foreach (var name in new[] { "x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1",
    "x64-bmi2", "x64-vector256", "x64-sse41", "arm64-armbase" })
{
    try { _ = SelectProfile(name); throw new InvalidOperationException("Retired profile accepted: " + name); }
    catch (TargetInvocationException exception) when (exception.InnerException is ArgumentException invalidProfile &&
        invalidProfile.Message.Contains("Retired execution profile", StringComparison.Ordinal)) { }
}
foreach (var (name, flag, value, accepted) in new[]
{
    ("x64-v3", "bmi1", false, false), ("x64-v3", "bmi2", false, false),
    ("x64-v3", "vector256Accelerated", false, true), ("x64-v3", "vector128Accelerated", false, false),
    ("x64-sse42", "sse42", false, false), ("x64-sse42", "vector256Accelerated", true, false),
    ("x64-v4", "avx512FVL", false, false), ("x64-v4", "avx512DQ", false, false),
    ("x64-v4", "avx512DQVL", false, false), ("arm64-advsimd", "advSimd", false, false),
    ("arm64-advsimd", "vector128Accelerated", false, false), ("arm64-advsimd", "vector256Accelerated", true, false)
})
{
    var profile = JsonSerializer.SerializeToNode(SelectProfile(name), jsonOptions)!;
    profile[flag] = JsonValue.Create(value);
    sharedCases.Add((profile.ToJsonString(), accepted));
    var profilePath = Path.Combine(output, $"{name}-{flag}.json");
    File.WriteAllText(profilePath, profile.ToJsonString());
    try
    {
        _ = SelectProfile("@" + profilePath);
        if (!accepted) throw new InvalidOperationException("Split runtime group accepted: " + profilePath);
    }
    catch (TargetInvocationException exception) when (!accepted && exception.InnerException is InvalidDataException) { }
}
Console.WriteLine("PASS runtime profile groups, retired profiles and reduced vector width");
Run(["lake", "build", "CIL.Extraction.Features", "CIL.SymbolicExecution", "CIL.Safety.Execution"]);
var sharedEvidence = Path.Combine(output, "RuntimeProfiles.lean");
RuntimeProfileValidation.Check(sharedCases, ExtractorPath, sharedEvidence);
Run(["lake", "env", "lean", sharedEvidence]);
Run(["lake", "env", "lean", "Tests/FeatureEvidence.lean"]);
var assembly = At("Examples/Assembly/bin/Examples.dll");
var folder = Path.Combine(output, "CompiledLoop");
Run(Extract("extract", assembly, "Examples", "Loops::FeatureCountdown(uint)", folder, "scalar"));
var path = Path.Combine(folder, "Extracted.lean");
Run(["lake", "env", "lean", path]);
var baseline = File.ReadAllText(path);

void Reject(string name, string mutated)
{
    if (mutated == baseline) throw new InvalidOperationException("Feature mutation did not change source: " + name);
    var target = Path.Combine(output, name + ".lean");
    File.WriteAllText(target, mutated);
    var result = Execute(["lake", "env", "lean", target]);
    if (result.Code == 0 || !result.Output.Contains("decide"))
        throw new InvalidOperationException("Feature certificate mutation was not rejected: " + name + "\n" + result.Output);
    Console.WriteLine("PASS feature certificate rejects " + name);
}

string MutateState(string source, string update) => Regex.Replace(source,
    @"(?m)^(def method0FeatureStates : Extraction.FeatureCertificate := )([^\r\n]+)",
    match => match.Groups[1].Value + "(" + match.Groups[2].Value + ")." + update);

// Keep instruction lookup lemmas in sync with each output mutation. Failure must
// come from independently checking extraction evidence, rather than a stale rfl.
Reject("wrong-feature", baseline.Replace(".feature .avx2", ".feature .sse2"));
Reject("wrong-branch", baseline.Replace(".brzero 10", ".brzero 11"));
Reject("forged-constant", baseline.Replace("stack := [some (BitVec.ofInt 32 (0))]", "stack := [some (BitVec.ofInt 32 (1))]"));
Reject("malformed-entry", MutateState(baseline, "set 0 (some { stack := [none], locals := [none] })"));
Reject("false-pruned-successor", MutateState(baseline, "set 10 none"));
Reject("omitted-states", MutateState(baseline, "take 17"));
var unsupported = Execute(Extract("extract", assembly, "Examples", "Loops::FeatureCountdown(uint)",
    Path.Combine(output, "EnabledUnsupported"), "x64-v3"));
if (unsupported.Code == 0 || !unsupported.Output.Contains("Unsupported instruction"))
    throw new InvalidOperationException("Enabled feature failed to expose unsupported array code: " + unsupported.Output);
// X86Base.X64 and Vector128 getters decide their branches from the profile alone.
foreach (var (profile, flags) in new[] { ("scalar", 0), ("x64-v3", 3), ("arm64-advsimd", 2), ("x64-sse42", 3) })
{
    var capabilities = Path.Combine(output, "Capabilities-" + profile);
    Directory.CreateDirectory(capabilities);
    var proof = Path.Combine(capabilities, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        $"  (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd = .ok [.scalar (.i32 {flags})] := rfl\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", "Capabilities::Flags()", proof, Path.Combine(capabilities, "Verified"), profile);
    Console.WriteLine($"PASS Capabilities::Flags under {profile} returns {flags}");
}
// A custom profile names the rule it breaks.
var noBase = Path.Combine(output, "bmi2-without-x86base.json");
File.WriteAllText(noBase, """
    { "name": "bmi2-only", "architecture": "x64", "nativeWidth": 64, "littleEndian": true, "advSimd": false, "sse2": false,
      "ssse3": false, "sse42": false, "avx": false, "avx2": false, "avx512F": false, "avx512FVL": false, "bmi1": false,
      "sse41": false, "avx512DQ": false, "avx512DQVL": false, "bmi2": true, "armBase64": false, "vector256Accelerated": false,
      "x86Base64": false, "vector128Accelerated": false }
    """);
var invalid = Execute(Extract("extract", assembly, "Examples", "Capabilities::Flags()", Path.Combine(output, "Reject-profile"), "@" + noBase));
if (invalid.Code == 0 || !invalid.Output.Contains("bmi2-only: x86 ISA flags require x86Base64"))
    throw new InvalidOperationException("Profile without X86Base64 was not rejected by name: " + invalid.Output);
Console.WriteLine("PASS x86 ISA flags without X86Base64 rejected with the rule");
Console.WriteLine("PASS raw feature analysis, join/backedge weakening, local eligibility, switches and emitted-code binding");
