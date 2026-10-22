#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

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
        contract["certifications"]![0]!["interfaceDigest"] = contract["interfaceDigest"]!.DeepClone();
    }
    if (updatePin) expectedInterfaceHash = contract["interfaceDigest"]!.GetValue<string>();
    File.WriteAllText(sidecar, contract.ToJsonString());
}

using Program interfaceVerification = new();
string interfaceLibrary = interfaceVerification.Library(Inputs(At("CIL.lean")));
Run(["lake", "build", "Tests.ContractClosure"], streamOutput: true, progress: "Canonical contract closure tests");
string interfaceProbe = Path.Combine(directory, "interface-probe");
Directory.CreateDirectory(interfaceProbe);
string interfaceSource = File.ReadAllText(Path.Combine(fixture, "ImportFixture.lean"));
File.WriteAllText(Path.Combine(interfaceProbe, "ImportFixture.lean"), interfaceSource);
string interfaceLeanPath = interfaceProbe + Path.PathSeparator + Path.Combine(interfaceLibrary, ".lake/build/lib/lean");
Run([interfaceVerification.LeanExecutable, "--root=" + interfaceProbe, "-o", Path.Combine(interfaceProbe, "ImportFixture.olean"),
    Path.Combine(interfaceProbe, "ImportFixture.lean")], leanPath: interfaceLeanPath);
string closureProbe = Path.Combine(interfaceProbe, "Closure.lean");
File.WriteAllText(closureProbe, "import CIL.Interface.Closure\nimport ImportFixture\n#leancil_contract_closure ImportFixture.addOne\n");
string closureOutput = Run([interfaceVerification.LeanExecutable, closureProbe], leanPath: interfaceLeanPath);
string closureLine = closureOutput.Split('\n').Single(line => line.Contains("\"canonical\"", StringComparison.Ordinal));
JsonElement closureRecord = JsonSerializer.Deserialize<JsonElement>(closureLine[closureLine.IndexOf('{')..]);
string closureDigest = ContentKey(closureRecord.GetProperty("canonical").GetString()!);

void Reset()
{
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
    contract["interfaceModules"]![0]!["source"] = interfaceSource;
    contract["exports"]![0]!["closureDigest"] = closureDigest;
    contract["certifications"]![0]!["closureDigest"] = closureDigest;
    contract["certifications"]![0]!["statementDigest"] = ContentKey("published canonical certification statement fixture");
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
if (!stages.Any(stage => stage.GetProperty("stage").GetString()!.Contains("Kernel replay", StringComparison.Ordinal) &&
    stage.GetProperty("command").EnumerateArray().Any(argument => argument.GetString() == "ImportFixture")))
    throw new InvalidOperationException("Fresh caller verification did not independently replay the published interface declarations.");
if (!verified.Contains("Conditional verification: assumes _root_.CIL.Safety.MethodContract.Holds _root_.ImportFixture.addOne linked 1", StringComparison.Ordinal))
    throw new InvalidOperationException("Verification did not disclose imported contract premises.");
JsonElement report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (report.GetProperty("schema").GetInt32() != 4 || report.GetProperty("contractImports").GetArrayLength() != 1 ||
    report.GetProperty("imports")[0].GetProperty("acceptedVia").GetString() != "published-certification" ||
    !report.GetProperty("imports")[0].GetProperty("deploymentObligation").GetString()!.Contains("exact implementation bytes", StringComparison.Ordinal))
    throw new InvalidOperationException("Verification report omitted imported contract premises.");

string replacementInterface = interfaceSource.Replace("output = input + 1", "output = input + 2", StringComparison.Ordinal);
string SubstitutionProof(string sourceFolder, string artifactPath, string markerPath)
{
    string replacementCommand = """
open Lean Elab Command in
run_cmd do
  let folder := SOURCE_FOLDER
  let source := folder / "ImportFixture.lean"
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
    .Replace("ARTIFACT_PATH", JsonSerializer.Serialize(artifactPath), StringComparison.Ordinal);
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
        File.ReadAllText(Path.Combine(output, "ImportFixture.lean")) != interfaceSource || File.ReadAllText(proofPath) != originalProof)
        throw new InvalidOperationException("An elaborator replaced audited interface artifacts without rejection, or changed original sources: " + substitution.Output);
}
RejectSubstitution(Path.Combine(directory, "SubstitutedInterface.lean"),
    "(System.FilePath.mk (← getFileName)).parent.getD \".\"", "ImportFixture.olean");
Console.WriteLine("PASS single-file verification rejects elaborator substitution of audited interface artifacts with unchanged sources");

string originalInterface = contract["interfaceModules"]![0]!["source"]!.GetValue<string>();
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
    string[] diagnostics = ["Application type mismatch", "LeanCILImportAudit.requireConditional", "HoldsGiven"];
    if (result.Code != 1 || diagnostics.Any(diagnostic => !result.Output.Contains(diagnostic, StringComparison.Ordinal)) ||
        File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Unrelated theorem did not fail the imported-claim audit or left a verification report: " + result.Output);
}

string unrelated = Path.Combine(directory, "Unrelated.lean");
File.WriteAllText(unrelated, "namespace ExampleProof\ntheorem correctness : True := by trivial\nend ExampleProof\n");
RejectUnrelatedTheorem(unrelated);
string package = Path.Combine(directory, "UnrelatedConsumer");
Directory.CreateDirectory(Path.Combine(package, "Client"));
string revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    $"name = \"unrelated_import_consumer\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n[[lean_lib]]\nname = \"Client\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"), true);
string consumerProof = Path.Combine(package, "Proof.lean");
File.Copy(unrelated, consumerProof, true);
Run(["lake", "update"], package);
RejectUnrelatedTheorem(consumerProof, "--proof-root", package);
Console.WriteLine("PASS ordinary and consumer import audits reject unrelated theorems without verification reports");
File.Copy(Path.Combine(fixture, "Caller.lean"), consumerProof, true);
Run([.. cli, "verify", output, "--proof", consumerProof, "--proof-root", package, "--fresh"]);
RejectSubstitution(consumerProof,
    "((System.FilePath.mk (← getFileName)).parent.getD \".\") / \".lake\" / \"packages\" / \"leancil\"",
    ".lake/build/lib/lean/ImportFixture.olean", "--proof-root", package);
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
File.AppendAllText(Path.Combine(output, "ImportFixture.lean"), "\n");
Reject([.. cli, "check", output], "Stale or mismatched contract interface source");
Run(Command());
File.AppendAllText(library, "rebuilt");
Reject([.. cli, "check", output], "expected " + expectedHash + ", actual ");

foreach ((string Diagnostic, Action<JsonObject> Change) test in new (string, Action<JsonObject>)[]
{
    ("Unsupported contract export kind", value => value["exports"]![0]!["kind"] = "unrecognized"),
    ("Unsupported contract interface format", value => value["formatVersion"] = 2),
    ("Unsupported contract interface format", value => value["semanticsVersion"] = 2),
    ("framework key mismatch", value => value["frameworkKey"] = new string('0', 64)),
    ("does not support dependencies", value => value["dependencies"] = new JsonArray("Other")),
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
    ("profile not listed", value => value["exports"]![0]!["profiles"] = new JsonArray("x64-sse41")),
    ("certification not present", value => value["certifications"] = new JsonArray()),
    ("certification binding mismatch", value => value["certifications"]![0]!["closureDigest"] = new string('0', 64)),
    ("Invalid or duplicate contract interface module", value => value["interfaceModules"]![0]!["name"] = "CIL.Types"),
    ("Invalid or duplicate contract interface module", value => value["interfaceModules"]![0]!["name"] = "../Escape"),
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
Reject(Command(method: "Generic"), "Generic contract imports");
foreach (Action<MethodDefinition> mutation in new Action<MethodDefinition>[]
{
    method => { method.IsStatic = false; method.HasThis = true; },
    method => method.IsVirtual = true,
    method => { method.IsPublic = false; method.IsPrivate = true; }
})
{
    Reset();
    MutateLibrary(module => mutation(module.GetType("ImportFixture.Library").Methods.Single(method => method.Name == "AddOne")));
    Reject(Command(), "must be static, non-virtual and public or protected");
}
foreach (OpCode opcode in new[] { OpCodes.Callvirt, OpCodes.Newobj, OpCodes.Ldftn })
{
    Reset();
    using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(app)));
    module.GetType("ImportFixture.Application").Methods.Single(method => method.Name == "Entry")
        .Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Call).OpCode = opcode;
    module.Write(app);
    Reject(Command(), "support call only");
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
