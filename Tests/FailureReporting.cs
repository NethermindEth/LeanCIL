#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

// failed.json classifies each failure, points at the obligation in the user's file and never
// reports an unproved goal as a disproved contract; only a verified `Not (contract.Holds ...)` is.
var cli = new[] { "dotnet", ExtractorPath };
var root = Path.GetFullPath(At("artifacts/FailureReporting"));
var package = Path.Combine(root, "Package");
Directory.CreateDirectory(Path.Combine(package, "Client"));
Directory.CreateDirectory(Path.Combine(package, "Proofs"));
const string Selector = "Calls::Root(ulong&,ulong&)";
const string RootSignature = "System.Void Contracts.Calls::Root(System.UInt64&,System.UInt64&)";

string Build(string name, string helpers)
{
    var source = Path.Combine(root, name);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Contracts.csproj"), """
    <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
    """);
    File.WriteAllText(Path.Combine(source, "Contracts.cs"), "namespace Contracts; public static class Calls { " + helpers +
        "public static void Root(ref ulong r, in ulong b) { AddTo(in r, in b, out r); r = Mix(r, b); } }");
    Run(["dotnet", "build", Path.Combine(source, "Contracts.csproj"), "-c", "Release"]);
    return Path.Combine(source, "bin/Contracts.dll");
}
// Mix is off by one; AddTo is correct unless `res` aliases `b`, which the contract permits.
var arithmetic = Build("Arithmetic",
    "public static ulong Mix(ulong x, ulong y) => x * 3 + y + 1; " +
    "public static void AddTo(in ulong a, in ulong b, out ulong res) => res = a + b; ");
var aliasing = Build("Aliasing",
    "public static ulong Mix(ulong x, ulong y) => x * 3 + y; " +
    "public static void AddTo(in ulong a, in ulong b, out ulong res) { res = a; res += b; } ");

const string Contracts = """
import Extracted
import CIL.MethodIdentity
import CIL.Safety.MethodContract
import CIL.Safety.WordMemory
import CIL.Safety.WordFootprint

open CIL.Safety
namespace Client

bind_method root rootBody := "System.Void Contracts.Calls::Root(System.UInt64&,System.UInt64&)"
bind_callee mix mixBody := "System.UInt64 Contracts.Calls::Mix(System.UInt64,System.UInt64)" from rootBody
bind_callee addTo addBody := "System.Void Contracts.Calls::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)" from rootBody

def mixContract : MethodContract (CIL.W64 × CIL.W64) CIL.W64 where
  args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
  results v := [.scalar (.i64 v)]
  pre _ _ := True
  footprint _ := []
  post input _ _ v := v = input.1 * 3 + input.2

structure AddInput where
  a : Reference
  b : Reference
  res : Reference
  x : CIL.W64
  y : CIL.W64

/-- `res` may overlap either input arbitrarily. -/
def addContract : MethodContract AddInput where
  args input := [.reference (.address input.a), .reference (.address input.b), .reference (.address input.res)]
  pre input m := read m input.a 8 1 = .ok (numberBytes input.x.toNat 8) ∧
    read m input.b 8 1 = .ok (numberBytes input.y.toNat 8) ∧ access m input.res 8 1 true = .ok ()
  footprint input := [(input.res, 8)]
  post input _ final values := values = [] ∧ read final input.res 8 1 = .ok (numberBytes (input.x + input.y).toNat 8)

end Client
""";
const string Header = "import Client.Contracts\n\nopen CIL.Safety Client\nnamespace ExampleProof\n\n";
const string MixHolds = """
theorem correctness : mixContract.Holds Extracted.program mix := by
  rintro ⟨x, y⟩ m -
  dsimp only [mixContract]
  refine ⟨8, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
  cil_checked_steps
""";
const string AddHolds = """
theorem correctness : addContract.Holds Extracted.program addTo := by
  rintro ⟨a, b, res, x, y⟩ m ⟨readA, readB, writable⟩
  dsimp only [addContract] at *
  have length : (numberBytes (x + y).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨stored, wrote⟩ := write_succeeds (bytes := numberBytes (x + y).toNat 8) (by simpa only [length] using writable)
  have readback := write_readback _ _ _ _ _ wrote
  rw [length] at readback
  have store : storeValue m (.address res) (.i64 (x + y)) = .ok stored := by
    simp only [storeValue, referenceAt, checkedAt, wrote, Except.mapError, Bind.bind, Except.bind]
  have fa := access_reference_valid _ _ _ _ _ (read_access readA)
  have fb := access_reference_valid _ _ _ _ _ (read_access readB)
  have fr := access_reference_valid _ _ _ _ _ writable
  have la := load_word64_of_read readA
  have lb := load_word64_of_read readB
  refine ⟨9, stored, [], ?_, Confined.write wrote (by simp [numberBytes]), _, rfl, rfl, readback⟩
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    fa, fb, fr, la, lb, store, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
""";
const string Refutation = """
def empty : Memory := { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }

/-- This build returns `Mix(0, 0) = 1`; the contract requires `0 * 3 + 0`. -/
theorem correctness : ¬ mixContract.Holds Extracted.program mix := by
  intro holds
  obtain ⟨_, final, values, ran, -, out, encoded, wrong⟩ := holds (0, 0) empty trivial
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (invoke_ok_unique ran (rfl : invoke Extracted.program 16 mix
    (mixContract.args (0, 0)) empty = .ok _))
  simp only [mixContract] at encoded wrong
  subst wrong
  simp at encoded
""";
File.WriteAllText(Path.Combine(package, "Client", "Contracts.lean"), Contracts);
string Proof(string name, string body)
{
    var path = Path.Combine(package, "Proofs", name + ".lean");
    File.WriteAllText(path, Header + body + "\nend ExampleProof\n");
    return path;
}
var unsolved = Proof("Unsolved", MixHolds);
var heartbeat = Proof("Heartbeat", "set_option maxHeartbeats 1 in\n" + AddHolds);
var refuted = Proof("Refuted", Refutation);
var added = Proof("Added", AddHolds);
// 1-based lines of the theorem, as Lean reports them.
(int First, int Last) Lines(string proof)
{
    var lines = File.ReadAllLines(proof);
    return (Array.FindIndex(lines, line => line.StartsWith("theorem correctness", StringComparison.Ordinal) ||
            line.StartsWith("set_option maxHeartbeats", StringComparison.Ordinal)) + 1,
        Array.FindLastIndex(lines, line => line.Length > 0 && line != "end ExampleProof") + 1);
}

var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    $"name = \"failures\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n[[lean_lib]]\nname = \"Client\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"), true);
Run(["lake", "update"], package);

string Extraction(string name, string assembly)
{
    var output = Path.Combine(root, "Out", name);
    Run([.. cli, "extract", assembly, Selector, output]);
    return output;
}
var outputs = new Dictionary<string, string>
{
    ["Unsolved"] = Extraction("Unsolved", arithmetic),
    ["Heartbeat"] = Extraction("Heartbeat", arithmetic),
    ["Refuted"] = Extraction("Refuted", arithmetic),
    ["Added"] = Extraction("Added", arithmetic),
    ["Aliased"] = Extraction("Aliased", aliasing)
};
// Extracted from one build, then the DLL is replaced by another build with the same methods.
var staleAssembly = Path.Combine(root, "Stale", "Contracts.dll");
Directory.CreateDirectory(Path.GetDirectoryName(staleAssembly)!);
File.Copy(aliasing, staleAssembly, true);
outputs["Stale"] = Extraction("Stale", staleAssembly);
var extractedSha = Sha(staleAssembly);
File.Copy(arithmetic, staleAssembly, true);
// Stale results from an earlier run must be replaced, whichever way this one goes.
foreach (var output in outputs.Values)
{
    File.WriteAllText(Path.Combine(output, "verified.json"), "stale success");
    File.WriteAllText(Path.Combine(output, "failed.json"), "stale failure");
}

JsonElement Failure(string output) => JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "failed.json")));
string? Text(JsonElement report, string name) => report.GetProperty(name).ValueKind == JsonValueKind.Null ? null : report.GetProperty(name).GetString();
int? Number(JsonElement report, string name) => report.GetProperty(name).ValueKind == JsonValueKind.Null ? null : report.GetProperty(name).GetInt32();
void Located(string name, JsonElement report, string kind, string proof, string? resource = null)
{
    var (first, last) = Lines(proof);
    var line = Number(report, "line");
    var obligations = report.GetProperty("diagnostics").EnumerateArray().ToArray();
    if (Text(report, "kind") != kind || Text(report, "resource") != resource || Text(report, "file") != proof ||
        line is not int at || at < first || at > last || Number(report, "column") is null ||
        obligations.Length == 0 || Text(obligations[0], "kind") != kind || Text(obligations[0], "file") != proof ||
        Text(obligations[0], "module") != "Proofs." + Path.GetFileNameWithoutExtension(proof) ||
        Text(report, "module") != "Proofs." + Path.GetFileNameWithoutExtension(proof) ||
        report.GetProperty("method").GetProperty("entry").GetString() != RootSignature ||
        !report.GetProperty("message").GetString()!.Contains(obligations[0].GetProperty("message").GetString()!, StringComparison.Ordinal))
        throw new InvalidOperationException($"Unexpected {name} failure report (expected {kind} in lines {first}-{last} of {proof}):\n{report}");
}
void Rerun(JsonElement report, string output, string proof, string? proofRoot)
{
    string[] expected = ["leancil", "verify", output, "--proof", proof, "--theorem", "ExampleProof.correctness",
        .. proofRoot is null ? Array.Empty<string>() : ["--proof-root", proofRoot]];
    if (!report.GetProperty("rerun").EnumerateArray().Select(item => item.GetString()).SequenceEqual(expected))
        throw new InvalidOperationException("Unexpected rerun command: " + report.GetProperty("rerun"));
}

// A single verification outside a consumer package locates the obligation in the user's proof, not the temporary copy.
var single = Path.Combine(root, "Out", "Single");
Run([.. cli, "extract", arithmetic, Selector, single]);
File.WriteAllText(Path.Combine(single, "verified.json"), "stale success");
var singleProof = Path.Combine(root, "Single.lean");
File.WriteAllText(singleProof, Contracts.Replace("namespace Client", "namespace ExampleProof").Replace("end Client", "") +
    "\nset_option maxHeartbeats 1 in\n" + AddHolds + "\nend ExampleProof\n");
var singleRun = Execute([.. cli, "verify", single, "--proof", singleProof]);
if (singleRun.Code != 1 || File.Exists(Path.Combine(single, "verified.json")))
    throw new InvalidOperationException("Expected the heartbeat limit to fail and remove the stale certificate:\n" + singleRun.Output);
var singleReport = Failure(single);
var singleLines = Lines(singleProof);
if (Text(singleReport, "kind") != "resource-limit" || Text(singleReport, "resource") != "heartbeats" || Text(singleReport, "module") != "Proof" ||
    Text(singleReport, "file") != singleProof || Number(singleReport, "line") is not int singleLine ||
    singleLine < singleLines.First || singleLine > singleLines.Last || Text(singleReport, "stage") != "proof checking")
    throw new InvalidOperationException("Unexpected single failure report:\n" + singleReport);
Rerun(singleReport, single, singleProof, null);
Console.WriteLine("PASS a single heartbeat limit is a resource limit located in the user's proof and removes the stale certificate");

var manifest = Path.Combine(root, "Batch.json");
var resultsPath = Path.Combine(root, "BatchResults.json");
var cases = new (string Name, string Proof)[]
{
    ("Unsolved", unsolved), ("Heartbeat", heartbeat), ("Refuted", refuted), ("Added", added), ("Aliased", added), ("Stale", added)
};
File.WriteAllText(manifest, JsonSerializer.Serialize(new
{
    schema = 1, proofRoot = package,
    requests = cases.Select(item => new { output = outputs[item.Name], proof = item.Proof, theorem = "ExampleProof.correctness" }).ToArray()
}));
var batch = Execute([.. cli, "verify-batch", manifest, "--results", resultsPath]);
var results = JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText(resultsPath))!;
var statuses = results.Select(item => item.GetProperty("status").GetString()).ToArray();
if (batch.Code != 1 || !statuses.SequenceEqual(["failed", "failed", "verified", "verified", "failed", "failed"]))
    throw new InvalidOperationException("Unexpected batch outcomes: " + string.Join(", ", statuses) + "\n" + batch.Output);
for (var i = 0; i < cases.Length; i++)
{
    var output = outputs[cases[i].Name];
    var failure = results[i].GetProperty("failure");
    if (cases[i].Name == "Added")
    {
        if (failure.ValueKind != JsonValueKind.Null || File.Exists(Path.Combine(output, "failed.json")) || !File.Exists(Path.Combine(output, "verified.json")))
            throw new InvalidOperationException("A positive success must remove the stale failure and keep only its certificate.");
        continue;
    }
    // The batch result and the per-output file carry the same report.
    if (!JsonElement.DeepEquals(failure, Failure(output)))
        throw new InvalidOperationException($"{cases[i].Name}: results and failed.json differ");
    Rerun(failure, output, cases[i].Proof, package);
    if (cases[i].Name != "Refuted" && File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException($"{cases[i].Name}: a failure left the stale certificate");
}
Located("arithmetic bug", results[0].GetProperty("failure"), "unsolved-goal", unsolved);
Located("heartbeat limit", results[1].GetProperty("failure"), "resource-limit", heartbeat, "heartbeats");
Located("aliasing precondition", results[4].GetProperty("failure"), "unsolved-goal", added);
Console.WriteLine("PASS an arithmetic bug and an unproved aliasing precondition are unsolved goals, and a heartbeat limit a resource limit, located in the user's proofs");

var refutation = results[2].GetProperty("failure");
var (refutedLine, _) = Lines(refuted);
if (Text(refutation, "kind") != "refutation" || Text(refutation, "file") != refuted || Number(refutation, "line") != refutedLine ||
    Number(refutation, "column") != "theorem ".Length || !File.Exists(Path.Combine(outputs["Refuted"], "verified.json")) ||
    results.Where((_, i) => i != 2).Any(item => item.GetProperty("failure") is { ValueKind: JsonValueKind.Object } other &&
        Text(other, "kind") == "refutation"))
    throw new InvalidOperationException("Only the verified refutation may be reported as one:\n" + refutation);
Console.WriteLine("PASS only the verified refutation is reported as a disproved contract, at its theorem, beside its certificate");

var stale = results[5].GetProperty("failure");
if (Text(stale, "kind") != "stale-input" || Text(stale, "stage") != "extraction integrity" || Text(stale, "file") is not null ||
    stale.GetProperty("diagnostics").GetArrayLength() != 0 || stale.GetProperty("method").GetProperty("entry").GetString() != RootSignature ||
    stale.GetProperty("method").GetProperty("assemblySha256").GetString() != extractedSha ||
    !stale.GetProperty("message").GetString()!.Contains("assembly has changed since extraction", StringComparison.Ordinal))
    throw new InvalidOperationException("Unexpected stale assembly report:\n" + stale);
Console.WriteLine("PASS a replaced assembly is a stale input naming the extracted method and its recorded assembly");
