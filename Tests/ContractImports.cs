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
    if (result.Code == 0 || !result.Output.Contains(diagnostic, StringComparison.Ordinal))
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

void Reset()
{
    // A proof selection left by an earlier run or a consumer check must not steer the next verification.
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
    contract["interfaceModules"]![0]!["source"] = File.ReadAllText(Path.Combine(fixture, "ImportFixture.lean"));
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
string verified = Run([.. cli, "verify", output, "--proof", Path.Combine(fixture, "Caller.lean")]);
if (!verified.Contains("Conditional verification: assumes _root_.CIL.Safety.MethodContract.Holds _root_.ImportFixture.addOne linked 1", StringComparison.Ordinal))
    throw new InvalidOperationException("Verification did not disclose imported contract premises.");
JsonElement report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (report.GetProperty("contractImports").GetArrayLength() != 1)
    throw new InvalidOperationException("Verification report omitted imported contract premises.");

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
    ("authoring-only", value => value["isReferenceAssembly"] = true),
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
foreach ((OpCode opcode, string diagnostic) in new[]
{
    (OpCodes.Callvirt, "Unsupported stack effect:"),
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
Console.WriteLine("PASS implementation-bound contract interfaces, conditional caller proof, rejected metadata and stale imports");

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
string pinnedInterface = originalInterface + "\ndef ImportFixture.marker : Nat := 0\n";
string forgedInterface = originalInterface + "\ndef ImportFixture.marker : Nat := 1\n";
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
string[] swappedFiles = ["identity.json", "ImportFixture.lean"];
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
