#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;

using var verification = new Program();
var output = At("artifacts/FeatureEvidence");
Directory.CreateDirectory(output);
Run(["lake", "build", "CIL.Extraction.Features", "CIL.SymbolicExecution", "CIL.Safety.Execution"]);
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
    Path.Combine(output, "EnabledUnsupported"), "x64-avx2"));
if (unsupported.Code == 0 || !unsupported.Output.Contains("Unsupported instruction"))
    throw new InvalidOperationException("Enabled feature failed to expose unsupported array code: " + unsupported.Output);
// X86Base.X64 and Vector128 getters decide their branches from the profile alone.
foreach (var (profile, flags) in new[] { ("scalar", 0), ("x64-bmi2", 1), ("arm64-advsimd", 2), ("x64-sse42", 3) })
{
    var capabilities = Path.Combine(output, "Capabilities-" + profile);
    Directory.CreateDirectory(capabilities);
    var proof = Path.Combine(capabilities, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        $"  (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd = .ok [.scalar (.i32 {flags})] := rfl\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", "Capabilities::Flags()", proof, Path.Combine(capabilities, "Verified"), profile);
    Console.WriteLine($"PASS Capabilities::Flags under {profile} returns {flags}");
}
Console.WriteLine("PASS raw feature analysis, join/backedge weakening, local eligibility, switches and emitted-code binding");
