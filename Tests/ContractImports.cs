#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;
using Mono.Cecil.Cil;

string fixture = At("Tests/ContractImports");
string directory = At("artifacts/ContractImports");
Directory.CreateDirectory(directory);
Run(["dotnet", "build", Path.Combine(fixture, "App/App.csproj"), "-c", "Release"]);
string originalApp = Path.Combine(fixture, "App/bin/ImportFixture.App.dll");
string originalLibrary = Path.Combine(fixture, "Lib/bin/ImportFixture.Lib.dll");
string app = Path.Combine(directory, "ImportFixture.App.dll");
string library = Path.Combine(directory, "ImportFixture.Lib.dll");
string sidecar = Path.Combine(directory, "ImportFixture.Lib.leancil.contracts");
string output = Path.Combine(directory, "extraction");
const string interfaceModule = "PublishedImportContract";
string expectedHash = "";
string expectedInterfaceHash = "";
JsonObject contract = null!;
string[] cli = ["dotnet", ExtractorPath];
string[] Command(string method = "Entry", bool includeImport = true, params string[] extra) =>
    [.. cli, "extract", app, "ImportFixture.Application::" + method + "(ulong)", output,
        .. includeImport ? new[] { "--import", sidecar, "--import-sha256", "ImportFixture.Lib=" + expectedHash, "--import-interface-sha256", "ImportFixture.Lib=" + expectedInterfaceHash } : [], .. extra];

void Reject(string[] command, string diagnostic)
{
    (int Code, string Output, string Stdout, string Stderr) result = Execute(command);
    if (result.Code != 1 || !result.Output.Contains(diagnostic, StringComparison.Ordinal))
        throw new InvalidOperationException("Expected " + diagnostic + ": " + result.Output);
}

string InterfaceDigest(JsonObject value)
{
    JsonObject descriptor = new();
    foreach (string field in new[] { "schema", "semanticsVersion", "formatVersion", "frameworkKey", "assemblyIdentity", "targetFramework", "interfaceModules", "exports", "dependencies" })
        descriptor[field] = value[field]!.DeepClone();
    return ContentKey(descriptor.ToJsonString());
}

void Save(bool bind = true, bool updatePin = true)
{
    if (bind)
    {
        contract["interfaceDigest"] = InterfaceDigest(contract);
        foreach (JsonNode? certification in contract["certifications"]!.AsArray())
            if (certification is JsonObject record)
                record["interfaceDigest"] = contract["interfaceDigest"]!.DeepClone();
    }
    if (updatePin) expectedInterfaceHash = contract["interfaceDigest"]!.GetValue<string>();
    File.WriteAllText(sidecar, contract.ToJsonString());
}

using Program interfaceVerification = new();
string interfaceLibrary = interfaceVerification.Library(Inputs(At("CIL.lean")));
string headerMarker = Path.Combine(directory, "header-command-executed");
File.Delete(headerMarker);
var headerSources = new SortedDictionary<string, string>(StringComparer.Ordinal)
{
    ["Comments"] = "/- outer /- nested -/ -/ import Alpha\n-- comment\nimport Beta.Gamma\n",
    ["Module"] = "module\npublic import Alpha\npublic meta import Beta.Gamma\nimport all Private\n",
    ["Prelude"] = "prelude\nimport Alpha\n",
    ["Source"] = "import Lean\nrun_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile " +
        JsonSerializer.Serialize(headerMarker) + " \"executed\"\n"
};
var parsedHeaders = interfaceVerification.ContractModuleImports(directory, headerSources);
if (!parsedHeaders["Comments"].SequenceEqual(["Alpha", "Beta.Gamma"]) ||
    !parsedHeaders["Module"].SequenceEqual(["Alpha", "Beta.Gamma", "Private"]) ||
    !parsedHeaders["Prelude"].SequenceEqual(["Alpha"]) ||
    !parsedHeaders["Source"].SequenceEqual(["Lean"]) || File.Exists(headerMarker))
    throw new InvalidOperationException("Contract header parsing changed imports or executed source commands.");
Exception? malformedHeader = null;
try { interfaceVerification.ContractModuleImports(directory, new() { ["Invalid"] = "import\n" }); }
catch (InvalidOperationException error) { malformedHeader = error; }
if (malformedHeader is null || !malformedHeader.Message.Contains("Invalid contract interface import header"))
    throw new InvalidOperationException("Malformed contract header was not rejected by Lean's parser.");
Run([interfaceVerification.LeanExecutable, At("Tests/ContractClosure.lean")],
    leanPath: interfaceVerification.SessionLeanPath(interfaceLibrary),
    streamOutput: true, progress: "Canonical contract closure tests");
string interfaceProbe = Path.Combine(directory, "interface-probe");
Directory.CreateDirectory(interfaceProbe);
string interfaceSource = File.ReadAllText(Path.Combine(fixture, "ImportFixture.lean"));
File.WriteAllText(Path.Combine(interfaceProbe, interfaceModule + ".lean"), interfaceSource);
string interfaceLeanPath = interfaceProbe + Path.PathSeparator + Path.Combine(interfaceLibrary, ".lake/build/lib/lean");
Run([interfaceVerification.LeanExecutable, "--root=" + interfaceProbe, "-o", Path.Combine(interfaceProbe, interfaceModule + ".olean"),
    Path.Combine(interfaceProbe, interfaceModule + ".lean")], leanPath: interfaceLeanPath);
string closureProbe = Path.Combine(interfaceProbe, "Closure.lean");
File.WriteAllText(closureProbe, "import CIL.Interface.Closure\nimport " + interfaceModule + "\n#leancil_contract_closure ImportFixture.addOne\n");
string closureOutput = Run([interfaceVerification.LeanExecutable, closureProbe], leanPath: interfaceLeanPath);
string closureLine = closureOutput.Split('\n').Single(line => line.Contains("\"canonical\"", StringComparison.Ordinal));
JsonElement closureRecord = JsonSerializer.Deserialize<JsonElement>(closureLine[closureLine.IndexOf('{')..]);
string closureDigest = ContentKey(closureRecord.GetProperty("canonical").GetString()!);

void Reset()
{
    Directory.CreateDirectory(output);
    File.Delete(Path.Combine(output, "verification.json"));
    File.Copy(originalApp, app, true);
    File.Copy(originalLibrary, library, true);
    expectedHash = Sha(library);
    using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(library)));
    contract = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture, "Lib.leancil.contracts")))!.AsObject();
    IEnumerable<string> sources = Directory.EnumerateFiles(At("CIL"), "*.lean", SearchOption.AllDirectories)
        .Append(At("CIL.lean")).Append(At("lean-toolchain"));
    contract["frameworkKey"] = ContentKey(string.Join("\n", sources.Select(path => (Name: Path.GetRelativePath(Root, path).Replace('\\', '/'), Path: path))
        .OrderBy(item => item.Name, StringComparer.Ordinal).Select(item => item.Name + "=" + Sha(item.Path))));
    contract["assemblyIdentity"] = module.Assembly.Name.FullName;
    contract["mvid"] = module.Mvid.ToString();
    contract["implementationSha256"] = expectedHash;
    contract["interfaceModules"]![0]!["name"] = interfaceModule;
    contract["interfaceModules"]![0]!["source"] = interfaceSource;
    contract["exports"]![0]!["closureDigest"] = closureDigest;
    contract["certifications"]![0]!["closureDigest"] = closureDigest;
    contract["fullVerificationLocator"] = Path.Combine(directory, "deleted-library-proofs");
    contract["exports"]![0]!["identity"] = module.Assembly.Name.FullName + "::System.UInt64 ImportFixture.Library::AddOne(System.UInt64)";
    contract["certifications"]![0]!["identity"] = contract["exports"]![0]!["identity"]!.DeepClone();
    contract["certifications"]![0]!["implementationSha256"] = expectedHash;
    Save();
}

void MutateLibrary(Action<ModuleDefinition> mutation)
{
    using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(library)));
    mutation(module);
    module.Write(library);
    expectedHash = Sha(library);
    contract["implementationSha256"] = expectedHash;
    contract["certifications"]![0]!["implementationSha256"] = expectedHash;
    Save();
}

void CheckInterfaceReuse()
{
    Reset();
    contract["exports"]![0]!["profiles"]!.AsArray().Add("x64-v3");
    JsonObject certification = contract["certifications"]![0]!.DeepClone().AsObject();
    certification["profile"] = "x64-v3";
    contract["certifications"]!.AsArray().Add(certification);
    Save();
    string reuseRoot = Path.Combine(directory, "interface-reuse-" + Guid.NewGuid().ToString("N"));
    string reusePackage = Path.Combine(reuseRoot, "Package");
    Directory.CreateDirectory(reusePackage);
    File.Copy(At("lean-toolchain"), Path.Combine(reusePackage, "lean-toolchain"));
    string revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
    File.WriteAllText(Path.Combine(reusePackage, "lakefile.toml"),
        "name = \"interface_reuse\"\n[[require]]\nname = \"leancil\"\ngit = " +
        JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " + JsonSerializer.Serialize(revision) + "\n");
    Run(["lake", "update"], reusePackage);
    string proof = Path.Combine(reusePackage, "Proof.lean");
    File.Copy(Path.Combine(fixture, "Caller.lean"), proof);
    var requests = new[] { "scalar", "x64-v3" }.Select(profile =>
    {
        string extraction = Path.Combine(reuseRoot, profile);
        string[] command = Command(extra: [profile]);
        command[5] = extraction;
        Run(command);
        return new { output = extraction, proof, theorem = "ExampleProof.correctness" };
    }).ToArray();
    string manifest = Path.Combine(reuseRoot, "batch.json");
    File.WriteAllText(manifest, JsonSerializer.Serialize(new { schema = 1, proofRoot = reusePackage, requests }));
    string trace = Path.Combine(reuseRoot, "trace");
    string? priorTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
    try
    {
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
        Run([.. cli, "verify-batch", manifest, "--fresh"]);
    }
    finally { Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", priorTrace); }
    JsonElement[] records = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
    string Transcript(JsonElement record) => File.ReadAllText(Path.Combine(trace,
        record.GetProperty("transcript").GetString()!));
    JsonElement[] builds = records.Where(record => record.GetProperty("stage").GetString() ==
        "Compiling published contract interfaces").ToArray();
    int compiled = builds.Sum(record => System.Text.RegularExpressions.Regex.Matches(Transcript(record),
        @"\bBuilt " + interfaceModule + @"(?:\s|$)").Count);
    int replayed = records.Where(record => record.GetProperty("exitCode").GetInt32() == 0 &&
            record.GetProperty("stage").GetString()!.Contains("kernel replay", StringComparison.OrdinalIgnoreCase))
        .SelectMany(record => Transcript(record).Split('\n').Where(line => line.StartsWith('{')))
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
        .Count(record => record.TryGetProperty("module", out JsonElement module) && module.GetString() == interfaceModule);
    if (builds.Length != 2 || compiled != 1 || replayed < 2)
        throw new InvalidOperationException($"Interface reuse mismatch: {builds.Length} checks, {compiled} builds, {replayed} replays.");
    Console.WriteLine("PASS identical published interfaces compile once across fresh extraction groups and replay independently");
    Reset();
}

if (args.Contains("--interface-reuse-only", StringComparer.Ordinal))
{
    CheckInterfaceReuse();
    return;
}

Reset();
File.Delete(sidecar);
Reject(Command(includeImport: false), "Next: supply --import");
Save();
Reject([.. cli, "extract", app, "ImportFixture.Application::Entry(ulong)", output, "--import", sidecar], "independently supplied SHA-256");
Run(Command(includeImport: false, extra: ["--import-sha256", "ImportFixture.Lib=" + expectedHash, "--import-interface-sha256", "ImportFixture.Lib=" + expectedInterfaceHash]));
string marker = Path.Combine(directory, "interface-code-executed");
File.Delete(marker);
contract["interfaceModules"]![0]!["source"] = contract["interfaceModules"]![0]!["source"]!.GetValue<string>() +
    "\nrun_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile " + JsonSerializer.Serialize(marker) + " \"executed\"\n";
Save(updatePin: false);
Reject(Command(), "Import interface SHA-256 mismatch");
if (File.Exists(marker)) throw new InvalidOperationException("Unpinned interface executed before rejection.");
Reset();
Reject([.. cli, "extract", app, "ImportFixture.Application::Entry(ulong)", output, "--import", sidecar,
    "--import-sha256", "ImportFixture.Lib=" + expectedHash], "independently supplied interface digest");
string alternate = Path.Combine(directory, "alternate-implementation.dll");
File.Copy(library, alternate, true);
Run(Command(extra: ["--import-implementation", "ImportFixture.Lib=" + alternate]));
Run([.. cli, "check", output]);
Run(Command());
Run([.. cli, "check", output]);
JsonElement identity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
foreach (string path in identity.GetProperty("imports").EnumerateArray()
    .SelectMany(binding => new[] { binding.GetProperty("implementationPath").GetString()!, binding.GetProperty("sidecarPath").GetString()! })
    .Append(identity.GetProperty("assemblyPath").GetString()!))
    if (path.Contains('\\') || Path.IsPathRooted(path))
        throw new InvalidOperationException("Extraction paths must be portable and relative: " + path);
string identityPath = Path.Combine(output, "identity.json");
string currentIdentity = File.ReadAllText(identityPath);
JsonObject oldIdentity = JsonNode.Parse(currentIdentity)!.AsObject();
oldIdentity["schema"] = 2;
File.WriteAllText(identityPath, oldIdentity.ToJsonString());
Reject([.. cli, "check", output], "Unsupported extraction manifest schema; run leancil extract again.");
File.WriteAllText(identityPath, currentIdentity);
string generated = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
if (identity.GetProperty("schema").GetInt32() != 3 || identity.GetProperty("imports").GetArrayLength() != 1 ||
    !generated.Contains(".call 1 1", StringComparison.Ordinal) || generated.Contains(expectedHash, StringComparison.Ordinal) ||
    !File.ReadAllText(Path.Combine(output, "ExtractedImports.lean")).Contains("@_root_.CIL.Safety.MethodContract.Holds _ _ _root_.ImportFixture.addOne linked 1", StringComparison.Ordinal))
    throw new InvalidOperationException("Import slot, conditional contract or implementation-independent extraction missing.");
string deletedProofs = Path.Combine(directory, "deleted-library-proofs");
Directory.CreateDirectory(deletedProofs);
File.WriteAllText(Path.Combine(deletedProofs, "LibraryProof.lean"), "not supplied to the consumer");
Directory.Delete(deletedProofs, true);
string freshCache = Path.Combine(directory, "empty-cache-" + Guid.NewGuid().ToString("N"));
string trace = Path.Combine(directory, "fresh-trace-" + Guid.NewGuid().ToString("N"));
string? savedCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
string? savedTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
string verified;
try
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", freshCache);
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
    verified = Run([.. cli, "verify", output, "--proof", Path.Combine(fixture, "Caller.lean"), "--fresh"]);
}
finally
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", savedCache);
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", savedTrace);
}
JsonElement[] stages = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
    .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
if (stages.Any(stage => stage.GetProperty("command").EnumerateArray().Any(argument =>
        argument.GetString()!.StartsWith(deletedProofs, StringComparison.Ordinal))) ||
    stages.Any(stage => stage.GetProperty("command").EnumerateArray().Any(argument => argument.GetString() == "extract")))
    throw new InvalidOperationException("Fresh caller verification obtained library implementation proofs or extracted Lib.");
if (!stages.Where(stage => stage.GetProperty("exitCode").GetInt32() == 0 &&
        stage.GetProperty("stage").GetString()!.Contains("Kernel replay", StringComparison.Ordinal))
    .SelectMany(stage => File.ReadLines(Path.Combine(trace, stage.GetProperty("transcript").GetString()!)))
    .Where(line => line.StartsWith('{'))
    .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
    .Any(record => record.TryGetProperty("module", out JsonElement module) &&
        module.GetString() == interfaceModule))
    throw new InvalidOperationException("Fresh caller verification did not independently replay the published interface declarations.");
if (!verified.Contains("Conditional verification: assumes _root_.CIL.Safety.MethodContract.Holds _root_.ImportFixture.addOne linked 1", StringComparison.Ordinal))
    throw new InvalidOperationException("Verification did not disclose imported contract premises.");
JsonElement report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (report.GetProperty("schema").GetInt32() != 4 || report.GetProperty("contractImports").GetArrayLength() != 1 ||
    report.GetProperty("imports")[0].GetProperty("acceptedVia").GetString() != "published-certification" ||
    !report.GetProperty("imports")[0].GetProperty("deploymentObligation").GetString()!.Contains("exact implementation bytes", StringComparison.Ordinal))
    throw new InvalidOperationException("Verification report omitted imported contract premises.");
// No pinned digest covers certification text, so the report must not present it as authenticated.
if (!report.GetProperty("imports")[0].TryGetProperty("certificationAuthenticated", out JsonElement authenticated) || authenticated.GetBoolean() ||
    !report.GetProperty("imports")[0].TryGetProperty("sidecarSha256", out JsonElement sidecarDigest) || sidecarDigest.GetString() != Sha(sidecar) ||
    !verified.Contains("Published certification (unauthenticated sidecar record, sidecar SHA-256 " + Sha(sidecar) + ")", StringComparison.Ordinal))
    throw new InvalidOperationException("Verification presented unpinned certification text without its sidecar provenance: " + verified);

string replacementInterface = interfaceSource.Replace("output = input + 1", "output = input + 2", StringComparison.Ordinal);
string SubstitutionProof(string sourceFolder, string artifactPath, string markerPath)
{
    string replacementCommand = """
open Lean Elab Command in
run_cmd do
  let folder := SOURCE_FOLDER
  let source := folder / INTERFACE_SOURCE
  let artifact := folder / ARTIFACT_PATH
  let original ← IO.FS.readFile source
  try
    IO.FS.writeFile source REPLACEMENT_SOURCE
    let compiled ← IO.Process.output {
      cmd := LEAN_EXECUTABLE
      args := #["--root=" ++ folder.toString, "-o", artifact.toString, source.toString] }
    if compiled.exitCode != 0 then
      throwError "Interface substitution compile failed: {compiled.stdout} {compiled.stderr}"
  finally
    IO.FS.writeFile source original
  IO.FS.writeFile SUBSTITUTION_MARKER "replaced"

""".Replace("REPLACEMENT_SOURCE", JsonSerializer.Serialize(replacementInterface), StringComparison.Ordinal)
    .Replace("LEAN_EXECUTABLE", JsonSerializer.Serialize(interfaceVerification.LeanExecutable), StringComparison.Ordinal)
    .Replace("SUBSTITUTION_MARKER", JsonSerializer.Serialize(markerPath), StringComparison.Ordinal)
    .Replace("SOURCE_FOLDER", sourceFolder, StringComparison.Ordinal)
    .Replace("ARTIFACT_PATH", JsonSerializer.Serialize(artifactPath), StringComparison.Ordinal)
    .Replace("INTERFACE_SOURCE", JsonSerializer.Serialize(interfaceModule + ".lean"), StringComparison.Ordinal);
    return "import Lean\n" + File.ReadAllText(Path.Combine(fixture, "Caller.lean"))
        .Replace("namespace ExampleProof", replacementCommand + "namespace ExampleProof", StringComparison.Ordinal);
}
void RejectSubstitution(string proofPath, string sourceFolder, string artifactPath, params string[] options)
{
    string substitutionMarker = Path.Combine(directory, "interface-substitution-" + Guid.NewGuid().ToString("N"));
    string originalProof = SubstitutionProof(sourceFolder, artifactPath, substitutionMarker);
    File.WriteAllText(proofPath, originalProof);
    (int Code, string Output, string Stdout, string Stderr) substitution = Execute([.. cli, "verify", output, "--proof", proofPath, "--fresh", .. options]);
    if (substitution.Code != 1 || !substitution.Output.Contains("Published contract interface artifacts changed after their closure audit", StringComparison.Ordinal) ||
        !File.Exists(substitutionMarker) || File.Exists(Path.Combine(output, "verified.json")) ||
        File.ReadAllText(Path.Combine(output, interfaceModule + ".lean")) != interfaceSource || File.ReadAllText(proofPath) != originalProof)
        throw new InvalidOperationException("An elaborator replaced audited interface artifacts without rejection, or changed original sources: " + substitution.Output);
}
RejectSubstitution(Path.Combine(directory, "SubstitutedInterface.lean"),
    "(System.FilePath.mk (← getFileName)).parent.getD \".\"", interfaceModule + ".olean");
Console.WriteLine("PASS single-file verification rejects elaborator substitution of audited interface artifacts with unchanged sources");

string originalInterface = contract["interfaceModules"]![0]!["source"]!.GetValue<string>();
string selectedProof = Path.Combine(directory, "SelectedCaller.lean");
string selectedProofSource = File.ReadAllText(Path.Combine(fixture, "Caller.lean"));
File.WriteAllText(selectedProof, selectedProofSource);
string substitutedSourceMarker = Path.Combine(directory, "proof-source-substitution");
File.Delete(substitutedSourceMarker);
string weakerProof = """
import ExtractedImports
namespace ExampleProof
theorem correctness : CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold (fun _ => True) := by
  intro linked links imported
  trivial
#print axioms correctness
end ExampleProof
""";
contract["interfaceModules"]![0]!["source"] = "import Lean\n" + originalInterface + $$"""

open Lean Elab Command in
run_cmd do
  let folder := (System.FilePath.mk (<- getFileName)).parent.getD "."
  IO.FS.writeFile (folder / "Proof.lean") {{JsonSerializer.Serialize(weakerProof)}}
  IO.FS.writeFile {{JsonSerializer.Serialize(substitutedSourceMarker)}} "rewritten"
""";
Save();
Run(Command());
string sourceAttackCache = Path.Combine(directory, "proof-source-cache-" + Guid.NewGuid().ToString("N"));
string? previousSourceAttackCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
try
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", sourceAttackCache);
    (int Code, string Output, string Stdout, string Stderr) sourceAttack =
        Execute([.. cli, "verify", output, "--proof", selectedProof]);
    bool proofReceipt = Directory.Exists(sourceAttackCache) && Directory.EnumerateFiles(sourceAttackCache, "receipt.json", SearchOption.AllDirectories)
        .Any(path => JsonSerializer.Deserialize<Dictionary<string, string>>(File.ReadAllText(path))!.Keys
            .Any(name => name.StartsWith("Proof.olean", StringComparison.Ordinal)));
    if (sourceAttack.Code != 1 ||
        !sourceAttack.Output.Contains("Proof sources changed during verification: Proof.lean", StringComparison.Ordinal) ||
        !File.Exists(substitutedSourceMarker) || File.ReadAllText(selectedProof) != selectedProofSource ||
        File.Exists(Path.Combine(output, "verified.json")) || proofReceipt)
        throw new InvalidOperationException("A pinned interface substituted the selected proof source or left a report or proof receipt: " + sourceAttack.Output);
}
finally
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", previousSourceAttackCache);
    Reset();
}
Console.WriteLine("PASS pinned interface proof-source substitution rejects with unchanged original proof and no report or proof receipt");
Run(Command());
contract["interfaceModules"]![0]!["source"] = "  /- outer /- nested -/ -/ import ZContractBase\n" +
    originalInterface + "\nexample : ZContractHeader.token = 7 := rfl\n";
contract["interfaceModules"]!.AsArray().Add(new JsonObject
{
    ["name"] = "ZContractBase",
    ["source"] = """
module
  public /- outer /- nested -/ -/ import ZContractData
  public meta /- outer /- nested -/ -/ import ZContractMeta

public section
def ZContractHeader.token : Nat := ZContractHeader.data
meta def ZContractHeader.metaToken : Nat := ZContractHeader.metaData
"""
});
contract["interfaceModules"]!.AsArray().Add(new JsonObject
{
    ["name"] = "ZContractData",
    ["source"] = "module\npublic section\ndef ZContractHeader.data : Nat := 7\n"
});
contract["interfaceModules"]!.AsArray().Add(new JsonObject
{
    ["name"] = "ZContractMeta",
    ["source"] = "module\npublic section\nmeta def ZContractHeader.metaData : Nat := 3\n"
});
Save();
Run(Command());
Run([.. cli, "verify", output, "--proof", Path.Combine(fixture, "Caller.lean"), "--fresh"]);
Console.WriteLine("PASS interface modules compile in parsed dependency order with public/meta imports and nested comments");
Reset();
contract["interfaceModules"]![0]!["source"] = """
import CIL.Safety.Imports
namespace Fake
 def contract : Nat := 0
 def contract.Holds (_linked : CIL.Program) (_slot : Nat) : Prop := True
end Fake
""";
contract["exports"]![0]!["contractConstant"] = "Fake.contract";
Save();
Run(Command());
string fakeCaller = Path.Combine(directory, "FakeCaller.lean");
File.WriteAllText(fakeCaller, """
import ExtractedImports
namespace ExampleProof
 theorem correctness : CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold (fun _ => True) := by
   intro linked links imported
   trivial
end ExampleProof
""");
(int Code, string Output, string Stdout, string Stderr) fakeResult = Execute([.. cli, "verify", output, "--proof", fakeCaller]);
if (fakeResult.Code != 1 || !fakeResult.Output.Contains("Application type mismatch", StringComparison.Ordinal) ||
    !fakeResult.Output.Contains("ExtractedImports.lean", StringComparison.Ordinal) || File.Exists(Path.Combine(output, "verified.json")))
    throw new InvalidOperationException("Fake field-notation Holds did not fail canonical contract typing or left a verification report: " + fakeResult.Output);
Console.WriteLine("PASS generated import assumptions reject a fake contract with a user-defined Holds predicate");
Reset();
contract["interfaceModules"]![0]!["source"] = originalInterface + """

namespace Fake
 def contract : Nat := 0
end Fake
namespace Extracted.Fake
 def contract : _root_.CIL.Safety.MethodContract _root_.CIL.W64 _root_.CIL.W64 := _root_.ImportFixture.addOne
end Extracted.Fake
""";
contract["exports"]![0]!["contractConstant"] = "Fake.contract";
Save();
Run(Command());
fakeResult = Execute([.. cli, "verify", output, "--proof", fakeCaller]);
if (fakeResult.Code != 1 || !fakeResult.Output.Contains("Application type mismatch", StringComparison.Ordinal) ||
    !fakeResult.Output.Contains("ExtractedImports.lean", StringComparison.Ordinal) || File.Exists(Path.Combine(output, "verified.json")))
    throw new InvalidOperationException("An Extracted namespace constant replaced the selected root contract: " + fakeResult.Output);
Reset();
contract["interfaceModules"]![0]!["source"] = originalInterface + """

namespace Extracted.CIL.Safety.MethodContract
 def Holds {I O : Type} (_contract : _root_.CIL.Safety.MethodContract I O)
     (_program : _root_.CIL.Program) (_slot : Nat) : Prop := True
end Extracted.CIL.Safety.MethodContract
""";
Save();
Run(Command());
string shadowCaller = Path.Combine(directory, "ShadowCaller.lean");
File.WriteAllText(shadowCaller, """
import ExtractedImports
example (linked : _root_.CIL.Program) :
    _root_.Extracted.ImportsHold linked =
      _root_.CIL.Safety.MethodContract.Holds _root_.ImportFixture.addOne linked 1 := by rfl
namespace ExampleProof
 theorem correctness : _root_.CIL.Safety.HoldsGiven _root_.Extracted.program _root_.Extracted.ImportsHold (fun _ => True) := by
   intro linked links imported
   trivial
end ExampleProof
""");
Run([.. cli, "verify", output, "--proof", shadowCaller]);
Console.WriteLine("PASS generated import assumptions bind root framework predicates and root contract constants");
Reset();
Run(Command());

void RejectUnrelatedTheorem(string proof, params string[] options)
{
    (int Code, string Output, string Stdout, string Stderr) result = Execute([.. cli, "verify", output, "--proof", proof, .. options]);
    string[] diagnostics = ["Theorem statement mismatch: ExampleProof.correctness"];
    if (result.Code != 1 || diagnostics.Any(diagnostic => !result.Output.Contains(diagnostic, StringComparison.Ordinal)) ||
        File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Unrelated theorem did not fail the imported-claim audit or left a verification report: " + result.Output);
}

string unrelated = Path.Combine(directory, "Unrelated.lean");
File.WriteAllText(unrelated, "namespace ExampleProof\ntheorem correctness : True := by trivial\nend ExampleProof\n");
RejectUnrelatedTheorem(unrelated);
contract["interfaceModules"]![0]!["name"] = "ConsumerImportedContract";
Save();
Run(Command());
string package = Path.Combine(directory, "UnrelatedConsumer");
Directory.CreateDirectory(Path.Combine(package, "Client"));
string revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    $"name = \"unrelated_import_consumer\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n[[lean_lib]]\nname = \"Client\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"), true);
string consumerProof = Path.Combine(package, "Proof.lean");
File.Copy(unrelated, consumerProof, true);
Run(["lake", "update"], package);
string consumerTrace = Path.Combine(directory, "unrelated-consumer-trace-" + Guid.NewGuid().ToString("N"));
string? previousConsumerTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
try
{
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", consumerTrace);
    RejectUnrelatedTheorem(consumerProof, "--proof-root", package, "--fresh");
}
finally { Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", previousConsumerTrace); }
JsonElement[] consumerStages = Directory.EnumerateFiles(consumerTrace, "*.jsonl").SelectMany(File.ReadLines)
    .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
if (!consumerStages.Any(stage => stage.GetProperty("stage").GetString() == "Checking consumer contract interfaces and import assumptions" &&
    new[] { "+ExtractedImports:olean", "+ConsumerImportedContract:olean" }.All(target =>
        stage.GetProperty("command").EnumerateArray().Any(argument => argument.GetString() == target))))
    throw new InvalidOperationException("The caller audit did not build all import modules omitted by the unrelated proof.");
Console.WriteLine("PASS ordinary and consumer import audits reject unrelated theorems without verification reports");
Reset();
Run(Command());
File.Copy(Path.Combine(fixture, "Caller.lean"), consumerProof, true);
Run([.. cli, "verify", output, "--proof", consumerProof, "--proof-root", package, "--fresh"]);
RejectSubstitution(consumerProof,
    "((System.FilePath.mk (← getFileName)).parent.getD \".\") / \".lake\" / \"packages\" / \"leancil\"",
    ".lake/build/lib/lean/" + interfaceModule + ".olean", "--proof-root", package);
File.Copy(Path.Combine(fixture, "Caller.lean"), consumerProof, true);
Console.WriteLine("PASS consumer verification rejects post-audit interface artifact substitution with unchanged original sources");

foreach (bool consumer in new[] { false, true })
{
    Reset();
    string uncheckedMarker = Path.Combine(directory, "unchecked-interface-" + Guid.NewGuid().ToString("N"));
    contract["interfaceModules"]![0]!["source"] = "import Lean\n" + interfaceSource + """

set_option debug.skipKernelTC true in
run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl <| .thmDecl {
  name := `UncheckedInterface.falsehood, levelParams := [],
  type := Lean.mkConst ``False, value := Lean.mkConst ``True.intro }
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile UNCHECKED_MARKER "inserted"
""".Replace("UNCHECKED_MARKER", JsonSerializer.Serialize(uncheckedMarker), StringComparison.Ordinal);
    Save();
    Run(Command());
    string uncheckedProof = consumer ? consumerProof : Path.Combine(directory, "UncheckedInterfaceProof.lean");
    File.WriteAllText(uncheckedProof, """
import ExtractedImports
namespace ExampleProof
theorem correctness : CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold (fun _ => False) := by
  intro linked links imported
  exact UncheckedInterface.falsehood
end ExampleProof
""");
    (int Code, string Output, string Stdout, string Stderr) uncheckedResult = Execute([.. cli, "verify", output,
        "--proof", uncheckedProof, "--fresh",
        .. consumer ? new[] { "--proof-root", package } : []]);
    if (uncheckedResult.Code != 1 || !uncheckedResult.Output.Contains("(kernel) declaration type mismatch", StringComparison.Ordinal) ||
        !uncheckedResult.Output.Contains("UncheckedInterface.falsehood", StringComparison.Ordinal) ||
        !File.Exists(uncheckedMarker) || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Independent interface replay did not reject the elaborated unchecked declaration: " + uncheckedResult.Output);
}
File.Copy(Path.Combine(fixture, "Caller.lean"), consumerProof, true);
Console.WriteLine("PASS ordinary and consumer interface replay reject unchecked falsehoods without reports");
Reset();
Run(Command());
string falseCaller = Path.Combine(directory, "ImplicitFalse.lean");
File.WriteAllText(falseCaller, "import ExtractedImports\nnamespace ExampleProof\ntheorem correctness {h : False} :\n    CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold (fun _ => False) := h.elim\nend ExampleProof\n");
(int Code, string Output, string Stdout, string Stderr) falseResult = Execute([.. cli, "verify", output, "--proof", falseCaller]);
if (falseResult.Code != 1 || !falseResult.Output.Contains("Theorem statement mismatch: ExampleProof.correctness", StringComparison.Ordinal) ||
    File.Exists(Path.Combine(output, "verified.json")))
    throw new InvalidOperationException("A claim behind an implicit False premise passed the conditional-claim audit: " + falseResult.Output);
Console.WriteLine("PASS a conditional claim behind an implicit False premise is not certified");
Reset();
using (ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(app))))
{
    // Entry now adds two, so a proof that the caller meets addOne is false.
    MethodBody body = module.GetType("ImportFixture.Application").Methods.Single(method => method.Name == "Entry").Body;
    Instruction call = body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Call);
    body.GetILProcessor().InsertAfter(call, Instruction.Create(OpCodes.Call, (MethodReference)call.Operand));
    module.Write(app);
}
contract["interfaceModules"]![0]!["source"] = originalInterface + "\ninstance (priority := high) retarget : OfNat Nat 1 := { ofNat := 0 }\n";
Save();
Run(Command());
string retargeted = Path.Combine(directory, "Retargeted.lean");
File.WriteAllText(retargeted, "import ExtractedImports\nnamespace ExampleProof\ntheorem correctness :\n    CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold (fun linked => ImportFixture.addOne.Holds linked 0) := by\n  intro linked links imported\n  exact imported\nend ExampleProof\n");
(int Code, string Output, string Stdout, string Stderr) retargetResult = Execute([.. cli, "verify", output, "--proof", retargeted]);
if (retargetResult.Code != 1 || !retargetResult.Output.Contains("Constant value mismatch: Extracted.ImportsHold", StringComparison.Ordinal) ||
    File.Exists(Path.Combine(output, "verified.json")))
    throw new InvalidOperationException("An interface OfNat instance retargeted the import slot onto the caller: " + retargetResult.Output);
Console.WriteLine("PASS an interface numeral instance cannot retarget the import premise onto the caller");
Reset();
File.Delete(Path.Combine(output, "verification.json"));
// The olean audit rejects a weakened contract even when the sidecar retains its honest closure pin.
contract["interfaceModules"]![0]!["source"] = "import CIL.Interface.Closure\n" +
    interfaceSource.Replace("output = input + 1", "True", StringComparison.Ordinal) +
    "\n";
Save();
Run(Command());
Reject([.. cli, "verify", output, "--proof", Path.Combine(fixture, "Caller.lean"), "--fresh"], "canonical closure digest mismatch");
if (File.Exists(Path.Combine(output, "verified.json")))
    throw new InvalidOperationException("A forged closure left a verification report.");
Console.WriteLine("PASS the olean audit rejects a weakened contract against its pinned canonical closure");
Reset();
Run(Command());
File.AppendAllText(Path.Combine(output, interfaceModule + ".lean"), "\n");
Reject([.. cli, "check", output], "Stale or mismatched contract interface source");
Run(Command());
File.AppendAllText(library, "rebuilt");
Reject([.. cli, "check", output], "expected " + expectedHash + ", actual ");

foreach ((string Diagnostic, Action<JsonObject> Change) test in new (string, Action<JsonObject>)[]
{
    ("Unsupported contract export kind", value => value["exports"]![0]!["kind"] = "unrecognized"),
    ("Unsupported contract interface format", value => value["formatVersion"] = 3),
    ("Typed contract exports require definition, arguments, signature and layouts", value => value["formatVersion"] = 2),
    ("Unsupported contract interface format", value => value["semanticsVersion"] = 2),
    ("framework key mismatch", value => value["frameworkKey"] = new string('0', 64)),
    ("Invalid or duplicate contract dependency", value => value["dependencies"] = new JsonArray(new JsonObject
        { ["assemblyIdentity"] = "Other", ["implementationSha256"] = "bad", ["interfaceDigest"] = "bad" })),
    ("certified SHA-256 mismatch", value => value["implementationSha256"] = new string('0', 64)),
    ("assembly identity mismatch", value =>
    {
        AssemblyNameReference identity = AssemblyNameReference.Parse(value["assemblyIdentity"]!.GetValue<string>());
        identity.Version = new Version(99, 0, 0, 0);
        value["assemblyIdentity"] = identity.FullName;
    }),
    ("MVID mismatch", value => value["mvid"] = Guid.NewGuid().ToString()),
    ("target framework mismatch", value => value["targetFramework"] = ".NETCoreApp,Version=v9.0"),
    ("export not present", value => value["exports"]![0]!["identity"] = "Other::NoMethod"),
    ("matching visibility", value => value["exports"]![0]!["visibility"] = "protected"),
    ("signature counts mismatch", value => value["exports"]![0]!["parameterCount"] = 2),
    ("signature counts mismatch", value => value["exports"]![0]!["returnsValue"] = false),
    ("profile not listed", value => value["exports"]![0]!["profiles"] = new JsonArray("x64-sse42")),
    ("certification not present", value => value["certifications"] = new JsonArray()),
    ("Invalid or duplicate contract export", value => value["exports"] = new JsonArray()),
    ("certification binding mismatch", value => value["certifications"]![0]!["closureDigest"] = new string('0', 64)),
    ("Invalid or duplicate contract interface module", value => value["interfaceModules"]![0]!["name"] = "CIL.Types"),
    ("Invalid or duplicate contract interface module", value => value["interfaceModules"]![0]!["name"] = "../Escape"),
    ("Invalid or duplicate contract interface module", value => value["interfaceModules"]![0]!["name"] = "cil.Types"),
    ("Invalid or duplicate contract interface module", value => value["interfaceModules"]![0]!["name"] = "tests.Imports"),
    ("Invalid or duplicate contract interface module", value => value["interfaceModules"]![0]!["name"] = "Lake.Build"),
    ("Invalid or duplicate contract interface module", value => value["interfaceModules"]![0]!["name"] = "LeanCILContractClosureAudit"),
    ("Invalid or duplicate contract interface module", value => value["interfaceModules"]![0]!["name"] = "leancilProof"),
    ("Invalid or duplicate contract interface module", value => value["interfaceModules"]!.AsArray().Add(new JsonObject
    {
        ["name"] = value["interfaceModules"]![0]!["name"]!.GetValue<string>().ToLowerInvariant(),
        ["source"] = "def caseCollision : Nat := 0\n"
    })),
    ("Invalid or duplicate contract export", value => value["exports"]![0]!["contractConstant"] = "Bad;axiom"),
    ("Invalid or duplicate contract export", value => value["exports"]![0]!["contractConstant"] = "_root_.ImportFixture.addOne")
})
{
    Reset();
    test.Change(contract);
    Save();
    Reject(Command(), test.Diagnostic);
}
Reset();
contract["interfaceDigest"] = new string('0', 64);
Save(bind: false);
Reject(Command(), "interface digest mismatch");
Reset();
expectedHash = new string('0', 64);
Reject(Command(), "implementation SHA-256 mismatch: expected " + expectedHash);
Reset();
// Closed generic imports are supported, but this sidecar exports only AddOne.
foreach (string artifact in new[] { "Extracted.lean", "identity.json", "verified.json" })
    File.Delete(Path.Combine(output, artifact));
(int Code, string Output, string Stdout, string Stderr) unlistedGeneric = Execute(Command(method: "Generic"));
if (unlistedGeneric.Code != 1 ||
    !unlistedGeneric.Output.Contains("Contract export not present:", StringComparison.Ordinal) ||
    !unlistedGeneric.Output.Contains("ImportFixture.Library::Identity<System.UInt64>", StringComparison.Ordinal) ||
    new[] { "Extracted.lean", "identity.json", "verified.json" }.Any(artifact => File.Exists(Path.Combine(output, artifact))))
    throw new InvalidOperationException("An unlisted closed generic instance did not fail before emission: " + unlistedGeneric.Output);
foreach ((Action<MethodDefinition> Mutation, string Diagnostic) test in new (Action<MethodDefinition>, string)[]
{
    (method => { method.IsStatic = false; method.HasThis = true; }, "Contract definition not present or ambiguous:"),
    (method => method.IsVirtual = true, "must be static, non-virtual and public or protected"),
    (method => { method.IsPublic = false; method.IsPrivate = true; }, "must be static, non-virtual and public or protected")
})
{
    Reset();
    MutateLibrary(module => test.Mutation(module.GetType("ImportFixture.Library").Methods.Single(method => method.Name == "AddOne")));
    Reject(Command(), test.Diagnostic);
}
foreach ((OpCode opcode, string diagnostic) in new[]
{
    (OpCodes.Callvirt, "callvirt requires an adjacent concrete constrained receiver"),
    (OpCodes.Newobj, "support call only"),
    (OpCodes.Ldftn, "support call only")
})
{
    Reset();
    using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(app)));
    module.GetType("ImportFixture.Application").Methods.Single(method => method.Name == "Entry")
        .Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Call).OpCode = opcode;
    module.Write(app);
    string rejectedOutput = Path.Combine(directory, "Reject-" + opcode.Code + "-" + Guid.NewGuid().ToString("N"));
    string[] command = Command();
    command[5] = rejectedOutput;
    (int Code, string Output, string Stdout, string Stderr) rejected = Execute(command);
    if (rejected.Code != 1 || !rejected.Output.Contains(diagnostic, StringComparison.Ordinal) ||
        !rejected.Output.Contains(opcode.Name, StringComparison.Ordinal) ||
        new[] { "Extracted.lean", "identity.json", "verified.json" }.Any(file => File.Exists(Path.Combine(rejectedOutput, file))))
        throw new InvalidOperationException("Unsupported import opcode was not rejected before extraction: " + rejected.Output);
}
Reset();
string stableInterface = contract["interfaceDigest"]!.GetValue<string>();
MutateLibrary(module => module.Mvid = Guid.NewGuid());
contract["mvid"] = Guid.NewGuid().ToString();
Save();
if (contract["interfaceDigest"]!.GetValue<string>() != stableInterface)
    throw new InvalidOperationException("Implementation identity changed the interface digest.");
Reset();
contract["interfaceModules"]![0]!["source"] = interfaceSource.Replace("output = input + 1", "output = input + 2", StringComparison.Ordinal);
Save();
Run(Command());
Reject([.. cli, "verify", output, "--proof", Path.Combine(fixture, "Caller.lean")], "canonical closure digest mismatch");
if (File.Exists(Path.Combine(output, "verified.json"))) throw new InvalidOperationException("Changed contract left a verification report.");
Reject([.. cli, "verify", output, "--proof", consumerProof, "--proof-root", package, "--fresh"], "canonical closure digest mismatch");
if (File.Exists(Path.Combine(output, "verified.json"))) throw new InvalidOperationException("Consumer closure rejection left a verification report.");
Reset();
contract["interfaceModules"]![0]!["source"] = interfaceSource + "\naxiom unpublishedAssumption : True\n";
Save();
Run(Command());
Reject([.. cli, "verify", output, "--proof", Path.Combine(fixture, "Caller.lean")], "contract interface");
Reject([.. cli, "verify", output, "--proof", consumerProof, "--proof-root", package, "--fresh"], "Axiom in contract interface: unpublishedAssumption");
if (File.Exists(Path.Combine(output, "verified.json"))) throw new InvalidOperationException("Consumer unused-axiom rejection left a verification report.");
Reset();
contract["isReferenceAssembly"] = true;
Save();
Run(Command());
Reject([.. cli, "verify", output, "--proof", Path.Combine(fixture, "Caller.lean")], "caller proof checked for authoring only");
if (File.Exists(Path.Combine(output, "verified.json"))) throw new InvalidOperationException("Reference-only input produced a verification report.");
Console.WriteLine("PASS canonical published contracts, fresh caller-only verification, reference authoring and import rejection paths");

foreach (string? adjacentSidecar in new[] { "{ not a contract interface", null })
{
    Reset();
    if (adjacentSidecar is not null) File.WriteAllText(sidecar, adjacentSidecar);
    Run([.. cli, "extract", app, "ImportFixture.Application::Unrelated(ulong)", output]);
    Run([.. cli, "check", output]);
    JsonElement unrelatedIdentity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")));
    if (unrelatedIdentity.GetProperty("imports").GetArrayLength() != 0 || unrelatedIdentity.GetProperty("importModules").EnumerateObject().Any())
        throw new InvalidOperationException("An adjacent sidecar of an uncalled library entered the extraction.");
}
Console.WriteLine("PASS adjacent sidecars of uncalled libraries need no pins and stay out of the extraction");

Reset();
Run(Command());
foreach (JsonElement import in JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json"))).GetProperty("imports").EnumerateArray())
    foreach (string field in new[] { "implementationPath", "sidecarPath" })
        if (Path.IsPathRooted(import.GetProperty(field).GetString()!))
            throw new InvalidOperationException("identity.json records a machine-specific import path: " + field);
string moved = directory + "-moved";
if (Directory.Exists(moved)) Directory.Delete(moved, true);
Directory.CreateDirectory(moved);
foreach (string file in new[] { app, library, sidecar }) File.Copy(file, Path.Combine(moved, Path.GetFileName(file)));
CopyTree(output, Path.Combine(moved, "extraction"));
// A stale original must not be what the moved artifact checks against.
File.AppendAllText(library, "rebuilt");
Run([.. cli, "check", Path.Combine(moved, "extraction")]);
Directory.Delete(moved, true);
Console.WriteLine("PASS import paths resolve relative to a moved extraction");

Reset();
string pinnedSidecarPath = Path.Combine(directory, "pinned-sidecar", Path.GetFileName(sidecar));
Directory.CreateDirectory(Path.GetDirectoryName(pinnedSidecarPath)!);
File.Move(sidecar, pinnedSidecarPath, true);
string[] pinnedCommand = Command();
pinnedCommand[Array.IndexOf(pinnedCommand, sidecar)] = pinnedSidecarPath;
Run(pinnedCommand);
Run([.. cli, "check", output]);
// Sidecars that appear beside the App after extraction are outside the recorded import graph.
File.Copy(pinnedSidecarPath, sidecar, true);
Run([.. cli, "check", output]);
File.WriteAllText(sidecar, "{}");
Run([.. cli, "check", output]);
File.Delete(sidecar);
Directory.Delete(Path.GetDirectoryName(pinnedSidecarPath)!, true);
Console.WriteLine("PASS check ignores sidecars that appear beside the App after extraction");

Reset();
string pinnedInterface = interfaceSource + "\ndef ImportFixture.marker : Nat := 0\n";
string forgedInterface = interfaceSource + "\ndef ImportFixture.marker : Nat := 1\n";
string forgedOutput = Path.Combine(directory, "forged-extraction");
contract["interfaceModules"]![0]!["source"] = forgedInterface;
Save();
byte[] forgedSidecar = File.ReadAllBytes(sidecar);
string[] forgedCommand = Command();
forgedCommand[5] = forgedOutput;
Run(forgedCommand);
contract["interfaceModules"]![0]!["source"] = pinnedInterface;
Save();
Run(Command());
string markerProof = Path.Combine(directory, "MarkerCaller.lean");
File.WriteAllText(markerProof, File.ReadAllText(Path.Combine(fixture, "Caller.lean")) +
    "\nnamespace ExampleProof\ntheorem marker : ImportFixture.marker = 0 := rfl\nend ExampleProof\n");
string[] swappedFiles = ["identity.json", interfaceModule + ".lean"];
Dictionary<string, byte[]> pinnedFiles = swappedFiles.ToDictionary(file => file, file => File.ReadAllBytes(Path.Combine(output, file)));
Dictionary<string, byte[]> forgedFiles = swappedFiles.ToDictionary(file => file, file => File.ReadAllBytes(Path.Combine(forgedOutput, file)));
string swapCache = Path.Combine(directory, "swap-cache-" + Guid.NewGuid().ToString("N"));
string sharedCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR") ??
    Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "LeanCIL", "libraries");
Directory.CreateDirectory(swapCache);
if (Directory.Exists(sharedCache))
    foreach (string candidate in Directory.EnumerateDirectories(sharedCache))
        if (File.Exists(Path.Combine(candidate, "cache-manifest.json")) && File.Exists(Path.Combine(candidate, "lakefile.toml")) &&
            Sha(Path.Combine(candidate, "lakefile.toml")) == Sha(At("lakefile.toml")))
            CopyTree(candidate, Path.Combine(swapCache, Path.GetFileName(candidate)));
string? savedSwapCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
string? savedDisabled = Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE");
bool swapped = false;
try
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", swapCache);
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", null);
    using (Program swapping = new())
        swapping.Verify(app, "", "", markerProof, output, existingArtifacts: true, stage: value =>
        {
            // A self-consistent forged extraction appears after staging and is restored before the final check.
            if (value == "proof checking" && !swapped)
            {
                foreach ((string file, byte[] bytes) in forgedFiles) File.WriteAllBytes(Path.Combine(output, file), bytes);
                swapped = true;
            }
            else if (value == "theorem audit" && swapped)
                foreach ((string file, byte[] bytes) in pinnedFiles) File.WriteAllBytes(Path.Combine(output, file), bytes);
        });
    if (!swapped) throw new InvalidOperationException("Precondition: verification never reached the swap window.");
    File.WriteAllBytes(sidecar, forgedSidecar);
    // Receipts are keyed by this driver's policy, so the forged extraction is checked by the same driver.
    Exception? rejected = null;
    using (Program reuse = new())
        try { reuse.Verify(app, "", "", markerProof, forgedOutput, existingArtifacts: true); }
        catch (Exception error) { rejected = error; }
    if (rejected is null || File.Exists(Path.Combine(forgedOutput, "verified.json")))
        throw new InvalidOperationException("A proof checked against one interface certified another through its success receipt.");
}
finally
{
    Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", savedSwapCache);
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", savedDisabled);
}
Console.WriteLine("PASS staged interface sources, proof keys and the report come from one identity.json snapshot");

Reset();
Run(Command());
string hashWindow = Path.Combine(directory, "hash-window");
Directory.CreateDirectory(hashWindow);
File.WriteAllText(Path.Combine(hashWindow, interfaceModule + ".lean"), interfaceSource.Replace("output = input + 1", "output = input + 2", StringComparison.Ordinal));
Run([interfaceVerification.LeanExecutable, "--root=" + hashWindow, "-o", Path.Combine(hashWindow, interfaceModule + ".olean"),
    Path.Combine(hashWindow, interfaceModule + ".lean")], leanPath: hashWindow + Path.PathSeparator + Path.Combine(interfaceLibrary, ".lake/build/lib/lean"));
byte[] unauditedArtifact = File.ReadAllBytes(Path.Combine(hashWindow, interfaceModule + ".olean"));
void RejectReplayWindowSwap(string expectedDiagnostic, Func<string?> locate, Action<Action<string>> verify)
{
    bool replaced = false;
    Exception? rejected = null;
    try
    {
        verify(value =>
        {
            // Replace the compiled interface immediately before its kernel replay.
            if (value != "kernel replay" || replaced || locate() is not string artifact) return;
            File.WriteAllBytes(artifact, unauditedArtifact);
            replaced = true;
        });
    }
    catch (Exception error) { rejected = error; }
    if (!replaced) throw new InvalidOperationException("Precondition: verification never reached the interface replay window.");
    if (rejected is null || !rejected.Message.Contains(expectedDiagnostic, StringComparison.Ordinal) ||
        File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Incorrect rejection of an interface olean replaced before replay: " + rejected?.Message);
}
string? savedHashCache = Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE");
try
{
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", "true");
    RejectReplayWindowSwap("Published contract canonical closure digest mismatch: ImportFixture.addOne", () => Directory.EnumerateDirectories(output, "proof-*")
            .Select(fresh => Path.Combine(fresh, interfaceModule + ".olean")).SingleOrDefault(File.Exists),
        stage => { using Program single = new(); single.Verify(app, "", "", Path.Combine(fixture, "Caller.lean"), output, existingArtifacts: true, stage: stage); });
    Console.WriteLine("PASS single-file verification binds interface oleans before their closure audit");
    // A token in the proof tells this session apart from concurrent consumer sessions.
    string token = Guid.NewGuid().ToString("N");
    File.WriteAllText(consumerProof, File.ReadAllText(Path.Combine(fixture, "Caller.lean")) + "\n-- " + token + "\n");
    DateTime started = DateTime.UtcNow.AddSeconds(-1);
    RejectReplayWindowSwap("changed after their closure audit", () => new DirectoryInfo(Path.GetTempPath()).EnumerateDirectories("leancil-consumer-*")
            .Where(session => session.CreationTimeUtc >= started && session.Name.Length == "leancil-consumer-".Length + 32 &&
                session.EnumerateFiles("*.lean").Any(file => File.ReadAllText(file.FullName).Contains(token, StringComparison.Ordinal)))
            .Select(session => Path.Combine(session.FullName, ".lake/packages/leancil_generated/.lake/build/lib/lean", interfaceModule + ".olean"))
            .SingleOrDefault(File.Exists),
        stage => { using Program consumer = new(); consumer.VerifyConsumer(app, consumerProof, output, "ExampleProof.correctness", package, null, stage); });
    File.Copy(Path.Combine(fixture, "Caller.lean"), consumerProof, true);
    Console.WriteLine("PASS consumer verification binds interface oleans before their closure audit");
}
finally { Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", savedHashCache); }

Reset();
contract["isReferenceAssembly"] = true;
Save();
string referenceOutput = Path.Combine(directory, "reference-extraction");
string[] referenceCommand = Command();
referenceCommand[5] = referenceOutput;
Run(referenceCommand);
string? savedReferenceCache = Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE");
try
{
    Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", null);
    using Program sequence = new();
    Exception? authoring = null;
    try { sequence.Verify(app, "", "", Path.Combine(fixture, "Caller.lean"), referenceOutput, existingArtifacts: true); }
    catch (Exception error) { authoring = error; }
    if (authoring is null || !authoring.Message.Contains("caller proof checked for authoring only", StringComparison.Ordinal))
        throw new InvalidOperationException("Precondition: the reference-only request must stop at authoring: " + authoring);
    Reset();
    Run(Command());
    sequence.Verify(app, "", "", Path.Combine(fixture, "Caller.lean"), output, existingArtifacts: true);
    if (!sequence.UseSuccessCache)
        throw new InvalidOperationException("A reference-only request disabled success receipts for a later implementation-bound request.");
}
finally { Environment.SetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE", savedReferenceCache); }
Console.WriteLine("PASS reference-only authoring disables success receipts only for its own request");
CheckInterfaceReuse();
