#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

// A long branch excluded by the scalar profile leaves hundreds of pruned sites. Per-site
// indexed lookups made the generated parameter and feature checks exceed the default budget.
var directory = At("artifacts/ExcludedBranchScaling");
var source = Path.Combine(directory, "Assembly");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Excluded.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
""");
File.WriteAllText(Path.Combine(source, "Excluded.cs"),
    "public static class Excluded { public static ulong Accumulate(ulong x, ulong y) { " +
    "if (System.Runtime.Intrinsics.X86.Avx2.IsSupported) { ulong word = x; " +
    string.Concat(Enumerable.Repeat("word = word * y + x; ", 200)) + "return word; } return x + y; } }");
Run(["dotnet", "build", Path.Combine(source, "Excluded.csproj"), "-c", "Release"]);
var assembly = Path.Combine(source, "bin/Excluded.dll");
var output = Path.Combine(directory, "Extraction");
Run(Extract("extract", assembly, "Excluded", "Excluded::Accumulate(ulong,ulong)", output));
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution"]);
var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));

// Split a generated Lean list literal at its top-level commas.
List<string> Entries(string name)
{
    var line = extracted.Split('\n').Single(l => l.StartsWith($"def {name} ", StringComparison.Ordinal));
    var body = line[(line.IndexOf(":= [", StringComparison.Ordinal) + 4)..line.LastIndexOf(']')];
    var entries = new List<string>();
    int depth = 0, start = 0;
    for (var i = 0; i < body.Length; i++)
    {
        if (body[i] is '[' or '{' or '(') depth++;
        else if (body[i] is ']' or '}' or ')') depth--;
        else if (body[i] == ',' && depth == 0) { entries.Add(body[start..i].Trim()); start = i + 1; }
    }
    entries.Add(body[start..].Trim());
    return entries;
}
var reachable = Entries("method0Reachable");
var states = Entries("method0FeatureStates");
var excluded = reachable.Count(live => live == "false");
if (excluded < 700 || states.Count != reachable.Count || extracted.Contains("set_option maxHeartbeats"))
    throw new InvalidOperationException($"Expected a large excluded branch checked at the default budget; found {excluded} excluded sites.");
Run(["lake", "env", "lean", Path.Combine(output, "Extracted.lean")]);
Console.WriteLine($"PASS {excluded} excluded sites validate at the default heartbeat budget");

// Each validator must still reach and reject a forged claim at the last pruned site it checks.
void Reject(string name, string validator, Func<int, bool> site, bool forgeState)
{
    var live = Entries("method0Reachable");
    var facts = Entries("method0FeatureStates");
    var pc = Enumerable.Range(0, live.Count).Last(i => live[i] == "false" && site(i));
    live[pc] = "true";
    if (forgeState) facts[pc] = "some { stack := [], locals := [] }";
    var tampered = Path.Combine(directory, name + ".lean");
    File.WriteAllText(tampered, string.Join('\n', extracted.Split('\n').Select(line =>
        line.StartsWith("def method0Reachable ", StringComparison.Ordinal) ? $"def method0Reachable : List Bool := [{string.Join(", ", live)}]" :
        line.StartsWith("def method0FeatureStates ", StringComparison.Ordinal) ? $"def method0FeatureStates : Extraction.FeatureCertificate := [{string.Join(", ", facts)}]" :
        line)));
    var rejected = Execute(["lake", "env", "lean", tampered]);
    if (rejected.Code == 0 || !rejected.Output.Contains($"Extraction.{validator} ", StringComparison.Ordinal))
        throw new InvalidOperationException($"{validator} accepted pruned site {pc} claimed reachable:\n" + rejected.Output);
    Console.WriteLine($"PASS {validator} rejects pruned site {pc} claimed reachable");
}
var argumentCode = extracted.Split('\n').Single(l => l.StartsWith("def method0RawArguments ", StringComparison.Ordinal));
var operations = argumentCode[(argumentCode.LastIndexOf("code := [", StringComparison.Ordinal) + 9)..argumentCode.LastIndexOf(']')].Split(", ");
Reject("ForgedFeatureSite", "FeatureFlowValid", _ => true, forgeState: true);
Reject("ForgedArgumentSite", "ParameterHomesValid", pc => operations[pc].StartsWith(".load", StringComparison.Ordinal), forgeState: true);

var consumer = Path.Combine(directory, "Consumer");
Directory.CreateDirectory(consumer);
var revision = Run(["git", "rev-parse", "HEAD"]).Trim();
File.WriteAllText(Path.Combine(consumer, "lakefile.toml"),
    $"name = \"excluded\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(consumer, "lean-toolchain"), true);
var proof = Path.Combine(consumer, "Proof.lean");
File.WriteAllText(proof, """
import Extracted
namespace ExampleProof
def empty : CIL.Safety.Memory := { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }
-- Only this user proof's `rfl` needs depth to reach the scalar path ~800 instructions in; generated evidence keeps the defaults.
set_option maxRecDepth 4096 in
theorem correctness :
    (CIL.Safety.invoke Extracted.program 16 0 [.scalar (.i64 2), .scalar (.i64 3)] empty).map Prod.snd =
      .ok [.scalar (.i64 5)] := by rfl
end ExampleProof
""");
Run(["lake", "update"], consumer);
Run(["dotnet", ExtractorPath, "verify", output, "--proof", proof, "--proof-root", consumer]);
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (!report.GetProperty("extractionAudit").GetString()!.Contains("ExtractionAudit.valid") ||
    !report.GetProperty("theoremAudit").GetString()!.Contains("ExampleProof.correctness"))
    throw new InvalidOperationException("Missing independent certificate/theorem audits.");
Console.WriteLine("PASS fresh consumer proof-root verifies the scalar path past the excluded branch");
