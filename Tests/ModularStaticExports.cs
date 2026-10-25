#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../Extractor/StaticIdentity.cs
#:include ImportReviewRegressions.cs

using System.Reflection;
using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Nethermind.LeanCIL;

// The default leaf also runs one forced full verification; the costlier compositions get their own runner.
bool fullComposition = args switch
{
    [] => false,
    ["--full-composition"] => true,
    _ => throw new ArgumentException("Expected no arguments or --full-composition.")
};
string root = At("artifacts/ModularStaticExports-" + Guid.NewGuid().ToString("N"));
string libRoot = Path.Combine(root, "Lib");
string appRoot = Path.Combine(root, "App");
string package = Path.Combine(root, "Package");
string caller = Path.Combine(root, "Caller");
foreach (string path in new[] { libRoot, appRoot, package, caller }) Directory.CreateDirectory(path);
File.WriteAllText(Path.Combine(libRoot, "Lib.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>StaticFixture.Lib</AssemblyName><AssemblyVersion>1.0.0.0</AssemblyVersion><Optimize>true</Optimize></PropertyGroup></Project>
""");
File.WriteAllText(Path.Combine(appRoot, "App.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>StaticFixture.App</AssemblyName><Optimize>true</Optimize></PropertyGroup><ItemGroup><ProjectReference Include="../Lib/Lib.csproj" /></ItemGroup></Project>
""");
File.WriteAllText(Path.Combine(libRoot, "Library.cs"), """
namespace StaticFixture;
[System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.Explicit, Size = 8, Pack = 1)]
public struct Blob { }
public static class Library { public static ulong Read() => 0; public static ulong ReadAgain() => 0; }
""");
File.WriteAllText(Path.Combine(appRoot, "Application.cs"), """
namespace StaticFixture;
[System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.Explicit, Size = 8, Pack = 1)]
public struct AppBlob { }
public static class Application
{
    public static ulong Own() => 0;
    public static ulong Entry() => Library.Read();
    public static ulong Mixed() => Own() + Library.Read() + Library.ReadAgain();
}
""");
Run(["dotnet", "build", Path.Combine(appRoot, "App.csproj"), "-c", "Release"]);
string lib = Path.Combine(libRoot, "bin", "StaticFixture.Lib.dll");
string app = Path.Combine(appRoot, "bin", "StaticFixture.App.dll");

void InstallTable(string assembly, string owner, string blob, ulong word, params string[] readers)
{
    using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(assembly)));
    TypeDefinition data = new("StaticFixture", "Data", Mono.Cecil.TypeAttributes.Public | Mono.Cecil.TypeAttributes.Abstract |
        Mono.Cecil.TypeAttributes.Sealed, module.TypeSystem.Object);
    module.Types.Add(data);
    TypeDefinition storage = module.GetType(blob);
    storage.Name = "Blob";
    FieldDefinition field = new("Table", Mono.Cecil.FieldAttributes.Static | Mono.Cecil.FieldAttributes.InitOnly |
        Mono.Cecil.FieldAttributes.HasFieldRVA, storage) { InitialValue = BitConverter.GetBytes(word) };
    data.Fields.Add(field);
    foreach (string reader in readers)
    {
        MethodDefinition method = module.GetType(owner).Methods.Single(candidate => candidate.Name == reader);
        method.Body.Instructions.Clear();
        ILProcessor il = method.Body.GetILProcessor();
        il.Append(il.Create(OpCodes.Ldsflda, field));
        il.Append(il.Create(OpCodes.Ldind_I8));
        il.Append(il.Create(OpCodes.Ret));
    }
    module.Write(assembly);
}

InstallTable(lib, "StaticFixture.Library", "StaticFixture.Blob", 17, "Read", "ReadAgain");
InstallTable(app, "StaticFixture.Application", "StaticFixture.AppBlob", 7, "Own");
if ((ulong)Assembly.Load(File.ReadAllBytes(lib)).GetType("StaticFixture.Library")!.GetMethod("Read")!.Invoke(null, null)! != 17 ||
    (ulong)Assembly.Load(File.ReadAllBytes(app)).GetType("StaticFixture.Application")!.GetMethod("Own")!.Invoke(null, null)! != 7)
    throw new InvalidOperationException("The RVA fixtures must read their distinct runtime data.");
string[] cli = ["dotnet", ExtractorPath];
string libArtifact = Path.Combine(root, "LibraryArtifact");
string ownArtifact = Path.Combine(root, "OwnArtifact");
string appArtifact = Path.Combine(root, "AppArtifact");
Run([.. cli, "extract", lib, "StaticFixture.Library::Read()", libArtifact]);
Run([.. cli, "extract", app, "StaticFixture.Application::Own()", ownArtifact]);
JsonObject libraryIdentity = JsonNode.Parse(File.ReadAllText(Path.Combine(libArtifact, "identity.json")))!.AsObject();
JsonObject appIdentity = JsonNode.Parse(File.ReadAllText(Path.Combine(ownArtifact, "identity.json")))!.AsObject();
JsonObject libStatic = libraryIdentity["staticIdentities"]![0]!.AsObject();
JsonObject appStatic = appIdentity["staticIdentities"]![0]!.AsObject();
string libKey = libStatic["identity"]!.GetValue<string>();
if (libraryIdentity["staticIdentities"]!.AsArray().Count != 1 || appIdentity["staticIdentities"]!.AsArray().Count != 1 ||
    libKey == appStatic["identity"]!.GetValue<string>() || libStatic["fieldName"]!.GetValue<string>() != appStatic["fieldName"]!.GetValue<string>())
    throw new InvalidOperationException("Separately extracted first static fields must have distinct scoped identities.");
// A fixed vector: published keys must not move with the encoder or the metadata library's name format.
if (libStatic["assemblyIdentity"]!.GetValue<string>() != "StaticFixture.Lib, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" ||
    libStatic["fieldName"]!.GetValue<string>() != "StaticFixture.Blob StaticFixture.Data::Table" ||
    libKey != "64781076327034064410872480157833285817926388820730852631679551572519415251497")
    throw new InvalidOperationException("Scoped static identity encoding changed: " + libStatic.ToJsonString());
ImportReviewRegressions.ValidateStatics_WhenApplicationCollidesWithImport_RejectsBothFields(ExtractorPath, appStatic, libStatic);
Console.WriteLine("PASS the production app-versus-import static merge rejects a named injected collision");
AssemblyNameReference signed = new("Signed.Lib", new Version(1, 2, 3, 4))
{
    Culture = "de-DE", PublicKeyToken = [0xb7, 0x7a, 0x5c, 0x56, 0x19, 0x34, 0xe0, 0x89], IsRetargetable = true
};
using (ModuleDefinition libModule = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(lib))))
    if (StaticIdentity.AssemblyIdentity(signed) != signed.FullName ||
        StaticIdentity.AssemblyIdentity(libModule.Assembly.Name) != libModule.Assembly.Name.FullName)
        throw new InvalidOperationException("Pinned assembly identity text no longer matches metadata assembly identities.");

string revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
void CreatePackage(string path, string name, params string[] modules)
{
    File.WriteAllText(Path.Combine(path, "lakefile.toml"), "name = " + JsonSerializer.Serialize(name) +
        "\n[[require]]\nname = \"leancil\"\ngit = " + JsonSerializer.Serialize(Root.Replace('\\', '/')) +
        "\nrev = " + JsonSerializer.Serialize(revision) + "\n" + string.Concat(modules.Select(module =>
            "[[lean_lib]]\nname = " + JsonSerializer.Serialize(module) + "\n")));
    File.Copy(At("lean-toolchain"), Path.Combine(path, "lean-toolchain"));
}
CreatePackage(package, "staticproducer", "PublishedTable", "LibraryProof");
CreatePackage(caller, "staticconsumer", "CallerProof");
string contract = Path.Combine(package, "PublishedTable.lean");
File.WriteAllText(contract, $$"""
import CIL.Safety.MethodContract
namespace PublishedTable
open CIL.Safety
def table : CIL.StaticDescriptor :=
  { identity := {{libKey}}, assemblyIdentity := {{JsonSerializer.Serialize(libStatic["assemblyIdentity"]!.GetValue<string>())}},
    fieldName := {{JsonSerializer.Serialize(libStatic["fieldName"]!.GetValue<string>())}},
    bytes := [17#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] }
def read : MethodContract Unit CIL.W64 where
  args _ := []
  results value := [.scalar (.i64 value)]
  pre _ memory := memory.WellFormed ∧ StaticWorldValid [table] memory
  footprint _ := []
  post _ _ final output := output = 17 ∧ final.WellFormed ∧ StaticWorldValid [table] final
end PublishedTable
""");
string proof = Path.Combine(package, "LibraryProof.lean");
File.WriteAllText(proof, """
import Extracted
import PublishedTable
import CIL.Safety.StaticMemoryBelow
import CIL.Safety.WordMemory
import CIL.Safety.SymbolicExecution
namespace LibraryProof
open CIL.Safety
private def descriptor : CIL.StaticDescriptor := (Extracted.method0.staticSites[0]'(by decide)).2
theorem correctness : PublishedTable.read.Holds Extracted.program 0 := by
  rintro input memory ⟨formed, published⟩
  have same : descriptor = PublishedTable.table := by decide +kernel
  have world : StaticWorldValid [descriptor] memory := by rw [same]; exact published
  obtain ⟨result, reference, resolved, _, valid⟩ := staticReference_valid_result descriptor [descriptor] memory formed world (by simp)
  have contents : descriptor.bytes = numberBytes (17#64).toNat 8 := by decide +kernel
  have loaded : read result reference 8 1 = .ok (numberBytes (17#64).toNat 8) := by
    have actual := valid.2.choose_spec.2.2.2.2
    change read result reference 8 1 = .ok descriptor.bytes at actual
    simpa only [contents] using actual
  have load := load_word64_of_read loaded
  have addressed : staticInstruction Extracted.method0 0 (.staticAddress descriptor.bytes) [] memory =
      .ok (result, [.reference (.address reference)]) := by
    change (do
      let (updated, address) ← staticReference descriptor memory
      pure (updated, [CIL.Safety.Value.reference (.address address)]) :
      ExecutionResult (CIL.Safety.Memory × List CIL.Safety.Value)) = _
    rw [resolved]
    rfl
  let frame : Frame := { activation := memory.nextIdentity, locals := [], owned := [] }
  have first : step Extracted.method0 (.memory (.staticAddress descriptor.bytes)) 0 [] frame [] memory =
      .ok (.next 1 [.reference (.address reference)] frame result) := by
    rw [step_memory_eq, addressed]
    rfl
  have second : step Extracted.method0 .load64 1 [] frame [.reference (.address reference)] result =
      .ok (.next 2 [.scalar (.i64 17)] frame result) := by
    rw [step_load64_eq]
    simp only [instructionStep, instruction, load, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  have returned : step Extracted.method0 .ret 2 [] frame [.scalar (.i64 17)] result =
      .ok (.returned [.scalar (.i64 17)] result) := rfl
  have executed : run Extracted.program 8 0 0 [] frame [] memory = .ok (result, [.scalar (.i64 17)]) :=
    (run_next (program := Extracted.program) (fuel := 7) (method := 0) (pc := 0)
      (by rfl) (by rfl) first).trans
      ((run_next (program := Extracted.program) (fuel := 6) (method := 0) (pc := 1)
        (by rfl) (by rfl) second).trans
        (run_return (program := Extracted.program) (fuel := 5) (method := 0) (pc := 2)
          (by rfl) (by rfl) returned (by rfl)))
  have preserved := staticReference_preserves_static_world _ _ _ _ _ formed world (by simp) resolved
  rw [same] at preserved
  exact ⟨8, result, [.scalar (.i64 17)], invoke_of_run (body := Extracted.method0) (by rfl) (by rfl) (by rfl) executed,
    Confined.ofMemoryBelow (staticReference_preserves_memory_below _ _ _ _ resolved)
      (Nat.le_refl _) (staticReference_extends_allocations _ _ _ _ resolved).next,
    17, rfl, rfl, staticReference_preserves_wellFormed _ _ _ _ formed resolved, preserved⟩
end LibraryProof
""");
// ReadAgain has Read's exact body, so one author proof certifies both exports of the shared table.
string againArtifact = Path.Combine(root, "AgainArtifact");
Run([.. cli, "extract", lib, "StaticFixture.Library::ReadAgain()", againArtifact]);
foreach (string exported in new[] { libArtifact, againArtifact })
    File.WriteAllText(Path.Combine(exported, "verification.json"), JsonSerializer.Serialize(new
    {
        schema = 1, proof = Path.GetRelativePath(exported, proof), theorem = "LibraryProof.correctness",
        proofRoot = Path.GetRelativePath(exported, package)
    }));
Run(["lake", "update"], package);
Run(["lake", "update"], caller);
string manifest = Path.Combine(root, "export.json");
File.WriteAllText(manifest, JsonSerializer.Serialize(new
{
    schema = 1, assembly = lib, proofRoot = package,
    @interface = new[] { new { module = "PublishedTable", source = contract } },
    exports = new[] { ("Read", libArtifact), ("ReadAgain", againArtifact) }.Select(export => new
    {
        method = "StaticFixture.Library::" + export.Item1 + "()", artifact = export.Item2, contract = "PublishedTable.read",
        theorem = "LibraryProof.correctness"
    })
}));
string sidecar = Path.Combine(libRoot, "StaticFixture.Lib.leancil.contracts");
Run([.. cli, "export-contracts", manifest, "--output", sidecar, "--bundle", Path.Combine(root, "Bundles")]);
JsonObject published = JsonNode.Parse(File.ReadAllText(sidecar))!.AsObject();
JsonNode ReadCertification(JsonObject contract) => contract["certifications"]!.AsArray()
    .Single(item => item!["identity"]!.GetValue<string>().EndsWith("::Read()", StringComparison.Ordinal))!;
if (published["certifications"]!.AsArray().Any(item => item!["staticIdentities"]!.AsArray().Count != 1 ||
    item["staticIdentities"]![0]!["identity"]!.GetValue<string>() != libKey))
    throw new InvalidOperationException("Published certification lost its kernel-bound static identity.");
string callerProof = Path.Combine(caller, "CallerProof.lean");
File.WriteAllText(callerProof, """
import ExtractedImports
import CIL.Safety.MethodContract
namespace ExampleProof
open CIL.Safety
theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
    (fun linked => PublishedTable.read.Holds linked 0) := by
  intro linked links imported input memory permitted
  have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
  have holds : PublishedTable.read.Holds linked 1 := imported
  dsimp only [PublishedTable.read, MethodContract.Returns]
  refine invoke_exists_of_run found (by rfl) (by rfl) ?_
  refine run_call_of_contract holds input found
    (by rfl : Extracted.method0.code[0]? = some (.call 1 0)) (by cil_checked_step []) rfl permitted ?_
  rintro final values _ framed returns
  obtain ⟨output, rfl, result⟩ := returns
  refine run_return_exists found (by rfl : Extracted.method0.code[1]? = some (.ret none))
    (by cil_checked_step []) (by rfl) ?_
  exact ⟨framed, output, rfl, result⟩
end ExampleProof
""");
string[] ExtractApp(string output) => [.. cli, "extract", app, "StaticFixture.Application::Entry()", output,
    "--import", sidecar, "--import-implementation", "StaticFixture.Lib=" + lib,
    "--import-sha256", "StaticFixture.Lib=" + Sha(lib), "--import-interface-sha256", "StaticFixture.Lib=" + published["interfaceDigest"]!.GetValue<string>()];
Run(ExtractApp(appArtifact));
// Forced full verification replays the RVA-table library against the current DLL.
string bundle = Path.GetFullPath(published["fullVerificationLocator"]!.GetValue<string>(), libRoot);
byte[] originalLib = File.ReadAllBytes(lib);
string[] FullCommand(string artifact, string callerSource, bool package) => [.. cli, "verify", artifact,
    "--proof", callerSource, .. package ? new[] { "--proof-root", caller } : [], "--force-full-verify"];
void FullVerify(string artifact, string callerSource, bool package, int slots)
{
    string trace = Path.Combine(root, "trace-" + Guid.NewGuid().ToString("N"));
    string? previousTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
    try
    {
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
        Run(FullCommand(artifact, callerSource, package));
    }
    finally { Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", previousTrace); }
    string[] stages = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line).GetProperty("stage").GetString()!).ToArray();
    // One bundle gives one library build however many slots it fills; the caller has its own.
    if (stages.Count(stage => stage == "Fresh extraction of the current imported library DLL") != slots ||
        stages.Count(stage => stage == "Capturing actual checked author and extraction kernel terms") != slots ||
        stages.Count(stage => stage == "Building fresh Lean verification library") != 2 ||
        stages.Count(stage => stage == "Independent kernel replay of the composed caller theorem") != 1 ||
        stages.Any(stage => stage.Contains("certified proof:", StringComparison.Ordinal)))
        throw new InvalidOperationException("Full verification reused a receipt instead of replaying: " + string.Join(", ", stages));
    JsonElement verified = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "verified.json")));
    JsonElement[] imports = verified.GetProperty("imports").EnumerateArray().ToArray();
    // The published statement must carry the checked static link, not only the raw link.
    if (imports.Length != slots || imports.Any(import =>
            import.GetProperty("acceptedVia").GetString() != "independently-verified" ||
            import.GetProperty("sourceBundleDigest").GetString() != Path.GetFileName(bundle) ||
            import.GetProperty("staticIdentities").GetArrayLength() != 1 ||
            import.GetProperty("staticIdentities")[0].GetProperty("identity").GetString() != libKey) ||
        verified.GetProperty("compositionTheorem").GetString() != "LeanCILFullComposition.certified" ||
        !verified.GetProperty("compositionAudit").GetString()!.Contains("linkChecked", StringComparison.Ordinal))
        throw new InvalidOperationException("Full verification did not publish the checked static composition: " + verified);
}
// Any one marker suffices where independent checks may reject the same input in either order.
void RejectFull(string artifact, params string[] markers)
{
    (int Code, string Output, string Stdout, string Stderr) result = Execute(FullCommand(artifact, callerProof, true));
    if (result.Code != 1 || !markers.Any(marker => result.Output.Contains(marker, StringComparison.Ordinal)) ||
        File.Exists(Path.Combine(artifact, "verified.json")))
        throw new InvalidOperationException("Full verification accepted a static-table forgery: " + result.Output);
}
void RewriteTable(ulong word)
{
    using ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(lib)));
    module.GetType("StaticFixture.Data").Fields.Single(field => field.Name == "Table").InitialValue = BitConverter.GetBytes(word);
    module.Write(lib);
}
// Republishes the bundle with edited export records under its new content identity, as a cooperating
// publisher could, points an edited sidecar at it and extracts the caller against that sidecar.
string Republish(Action<JsonObject> editExport, Action<JsonObject> editSidecar)
{
    string staging = Path.Combine(root, "rebundle-" + Guid.NewGuid().ToString("N"));
    CopyTree(bundle, staging);
    JsonObject inventory = JsonNode.Parse(File.ReadAllText(Path.Combine(staging, "bundle.json")))!.AsObject();
    foreach (string bundled in Directory.EnumerateDirectories(Path.Combine(staging, "exports")))
    {
        string identityPath = Path.Combine(bundled, "identity.json");
        JsonObject exportIdentity = JsonNode.Parse(File.ReadAllText(identityPath))!.AsObject();
        editExport(exportIdentity);
        File.WriteAllText(identityPath, exportIdentity.ToJsonString());
        inventory["files"]!["exports/" + Path.GetFileName(bundled) + "/identity.json"] = Sha(identityPath);
    }
    File.WriteAllText(Path.Combine(staging, "bundle.json"), inventory.ToJsonString());
    string republished = Path.Combine(root, Sha(Path.Combine(staging, "bundle.json")));
    Directory.Move(staging, republished);
    JsonObject contract = published.DeepClone().AsObject();
    editSidecar(contract);
    contract["fullVerificationLocator"] = republished;
    File.WriteAllText(sidecar, contract.ToJsonString());
    string artifact = Path.Combine(root, "Republished-" + Guid.NewGuid().ToString("N"));
    Run(ExtractApp(artifact));
    return artifact;
}

if (fullComposition)
{
    // A re-certified changed table passes ordinary import, which trusts the publisher; only the
    // independent author proof sees that the bytes no longer match the published descriptor.
    try
    {
        RewriteTable(18);
        string changedSha = Sha(lib);
        string changed = Republish(identity => identity["assemblySha256"] = changedSha, contract =>
        {
            contract["implementationSha256"] = changedSha;
            foreach (JsonNode? certification in contract["certifications"]!.AsArray())
                certification!["implementationSha256"] = changedSha;
        });
        RejectFull(changed, "descriptor = PublishedTable.table");
    }
    finally
    {
        File.WriteAllBytes(lib, originalLib);
        File.WriteAllText(sidecar, published.ToJsonString());
    }
    Console.WriteLine("PASS a re-certified changed table passes ordinary import but fails the independent library proof");

    // Both assemblies' first tables had extraction-local index 0; ReadAgain shares Read's table.
    string mixedArtifact = Path.Combine(root, "MixedArtifact");
    Run([.. cli, "extract", app, "StaticFixture.Application::Mixed()", mixedArtifact, .. ExtractApp(mixedArtifact)[6..]]);
    JsonObject mixedIdentity = JsonNode.Parse(File.ReadAllText(Path.Combine(mixedArtifact, "identity.json")))!.AsObject();
    if (mixedIdentity["staticIdentities"]!.AsArray().Count != 1 ||
        mixedIdentity["staticIdentities"]![0]!["identity"]!.GetValue<string>() != appStatic["identity"]!.GetValue<string>() ||
        mixedIdentity["imports"]!.AsArray().Count != 2)
        throw new InvalidOperationException("Precondition: the mixed caller must own one table and import two readers of another.");
    string mixedProof = Path.Combine(root, "MixedCaller.lean");
    File.WriteAllText(mixedProof, "import ExtractedImports\nnamespace ExampleProof\ntheorem correctness : " +
        "_root_.CIL.Safety.HoldsGiven _root_.Extracted.program _root_.Extracted.ImportsHold (fun _ => True) := by\n" +
        "  intro linked links imported\n  trivial\nend ExampleProof\n");
    FullVerify(mixedArtifact, mixedProof, package: false, slots: 2);
    Console.WriteLine("PASS distinct same-index app and library tables and one shared table across two imported slots");
    return;
}

Run([.. cli, "verify", appArtifact, "--proof", callerProof, "--proof-root", caller, "--fresh"]);
JsonObject report = JsonNode.Parse(File.ReadAllText(Path.Combine(appArtifact, "verified.json")))!.AsObject();
if (report["imports"]![0]!["staticIdentities"]![0]!["identity"]!.GetValue<string>() != libKey)
    throw new InvalidOperationException("Verified deployment report omitted the imported static identity.");
Console.WriteLine("PASS RVA static export, repeatable published static world precondition, imported caller and report provenance");

void Reject(Action<JsonObject> mutate, string marker)
{
    JsonObject invalid = published.DeepClone().AsObject();
    mutate(invalid);
    File.WriteAllText(sidecar, invalid.ToJsonString());
    string rejected = Path.Combine(root, "Reject-" + Guid.NewGuid().ToString("N"));
    (int Code, string Output, string Stdout, string Stderr) result = Execute(ExtractApp(rejected));
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal) || File.Exists(Path.Combine(rejected, "Extracted.lean")))
        throw new InvalidOperationException("Static certification rejection failed: " + result.Output);
}
Reject(value => ReadCertification(value).AsObject().Remove("staticIdentities"), "Missing contract interface field: staticIdentities");
Reject(value => ReadCertification(value)["staticIdentities"] = new JsonArray(), "static identities differ from the selected implementation");
Reject(value => ReadCertification(value)["staticIdentities"]![0]!["identity"] = "0", "Invalid scoped static identity");
Reject(value =>
{
    JsonNode identity = ReadCertification(value)["staticIdentities"]![0]!;
    identity["fieldName"] = "StaticFixture.Blob StaticFixture.Data::Missing";
    identity["identity"] = StaticIdentity.Key(identity["assemblyIdentity"]!.GetValue<string>(), identity["fieldName"]!.GetValue<string>());
}, "Certified static field is not present");
Reject(value => ReadCertification(value)["staticIdentities"]!.AsArray().Add(libStatic.DeepClone()), "Invalid or duplicate contract certification");
Reject(value =>
{
    JsonNode conflicting = libStatic.DeepClone();
    conflicting["fieldName"] = "StaticFixture.Blob StaticFixture.Data::Collision";
    ReadCertification(value)["staticIdentities"]!.AsArray().Add(conflicting);
}, "Static identity collision " + libKey + ": " + libStatic["assemblyIdentity"]!.GetValue<string>() + "::" + libStatic["fieldName"]!.GetValue<string>() + " and ");
File.WriteAllText(sidecar, published.ToJsonString());

// The ordinary verification above left warm receipts; full mode must still extract, capture and replay.
FullVerify(appArtifact, callerProof, package: true, slots: 1);
Console.WriteLine("PASS forced full verification of a separately compiled RVA-table library with warm receipts");
try
{
    RewriteTable(18);
    RejectFull(appArtifact, "Stale or mismatched verification artifact",
        "Full-verification imported implementation or sidecar changed");
}
finally { File.WriteAllBytes(lib, originalLib); }
string appIdentityPath = Path.Combine(appArtifact, "identity.json");
string appIdentityText = File.ReadAllText(appIdentityPath);
try
{
    JsonObject forged = JsonNode.Parse(appIdentityText)!.AsObject();
    forged["imports"]![0]!["staticIdentities"] = new JsonArray();
    File.WriteAllText(appIdentityPath, forged.ToJsonString());
    RejectFull(appArtifact, "differs from regenerated assembly, extractor or configuration metadata");
}
finally { File.WriteAllText(appIdentityPath, appIdentityText); }
string bundledInterface = Path.Combine(bundle, "interface", "PublishedTable.lean");
string bundledInterfaceText = File.ReadAllText(bundledInterface);
try
{
    File.AppendAllText(bundledInterface, "\n");
    RejectFull(appArtifact, "Contract source bundle file is missing or changed: interface/PublishedTable.lean");
}
finally { File.WriteAllText(bundledInterface, bundledInterfaceText); }
try
{
    string forgedStatics = Republish(identity => identity["staticIdentities"] = new JsonArray(), _ => { });
    RejectFull(forgedStatics, "Full-verification static identities differ from the current implementation");
}
finally { File.WriteAllText(sidecar, published.ToJsonString()); }
Console.WriteLine("PASS full verification rejects a changed table DLL, forged caller or bundle static records and a tampered bundle");

using (ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(File.ReadAllBytes(lib))))
{
    MethodDefinition read = module.GetType("StaticFixture.Library").Methods.Single(method => method.Name == "Read");
    read.Body.GetILProcessor().InsertBefore(read.Body.Instructions[0], Instruction.Create(OpCodes.Nop));
    module.Write(lib);
}
string rebuilt = Path.Combine(root, "Rebuilt");
Run([.. cli, "extract", lib, "StaticFixture.Library::Read()", rebuilt]);
JsonObject rebuiltIdentity = JsonNode.Parse(File.ReadAllText(Path.Combine(rebuilt, "identity.json")))!.AsObject();
if (rebuiltIdentity["staticIdentities"]![0]!["identity"]!.GetValue<string>() != libKey ||
    rebuiltIdentity["assemblySha256"]!.GetValue<string>() == libraryIdentity["assemblySha256"]!.GetValue<string>())
    throw new InvalidOperationException("A body-only rebuild changed the static identity or did not change the DLL.");
Console.WriteLine("PASS static certification tampering, named collisions, separate extraction and stable body-only rebuild identity");
