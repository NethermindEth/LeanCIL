#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Numerics;
using System.Reflection;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;
using Mono.Cecil.Cil;

string root = At("artifacts/ModularStaticExports-" + Guid.NewGuid().ToString("N"));
string libRoot = Path.Combine(root, "Lib");
string appRoot = Path.Combine(root, "App");
string package = Path.Combine(root, "Package");
string caller = Path.Combine(root, "Caller");
foreach (string path in new[] { libRoot, appRoot, package, caller }) Directory.CreateDirectory(path);
File.WriteAllText(Path.Combine(libRoot, "Lib.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>StaticFixture.Lib</AssemblyName><Optimize>true</Optimize></PropertyGroup></Project>
""");
File.WriteAllText(Path.Combine(appRoot, "App.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>StaticFixture.App</AssemblyName><Optimize>true</Optimize></PropertyGroup><ItemGroup><ProjectReference Include="../Lib/Lib.csproj" /></ItemGroup></Project>
""");
File.WriteAllText(Path.Combine(libRoot, "Library.cs"), """
namespace StaticFixture;
[System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.Explicit, Size = 8, Pack = 1)]
public struct Blob { }
public static class Library { public static ulong Read() => 0; }
""");
File.WriteAllText(Path.Combine(appRoot, "Application.cs"), """
namespace StaticFixture;
[System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.Explicit, Size = 8, Pack = 1)]
public struct AppBlob { }
public static class Application { public static ulong Own() => 0; public static ulong Entry() => Library.Read(); }
""");
Run(["dotnet", "build", Path.Combine(appRoot, "App.csproj"), "-c", "Release"]);
string lib = Path.Combine(libRoot, "bin", "StaticFixture.Lib.dll");
string app = Path.Combine(appRoot, "bin", "StaticFixture.App.dll");

void InstallTable(string assembly, string owner, string methodName, string blob, ulong word)
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
    MethodDefinition method = module.GetType(owner).Methods.Single(candidate => candidate.Name == methodName);
    method.Body.Instructions.Clear();
    ILProcessor il = method.Body.GetILProcessor();
    il.Append(il.Create(OpCodes.Ldsflda, field));
    il.Append(il.Create(OpCodes.Ldind_I8));
    il.Append(il.Create(OpCodes.Ret));
    module.Write(assembly);
}

InstallTable(lib, "StaticFixture.Library", "Read", "StaticFixture.Blob", 17);
InstallTable(app, "StaticFixture.Application", "Own", "StaticFixture.AppBlob", 7);
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
def identity : Nat := {{libKey}}
def read : MethodContract Unit CIL.W64 where
  args _ := []
  results value := [.scalar (.i64 value)]
  pre _ memory := memory.WellFormed ∧ StaticRegistryValid memory ∧ StaticIdentitiesAbsent [identity] memory
  footprint _ := []
  post _ _ _ output := output = 17
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
private def descriptor : CIL.StaticDescriptor := (Extracted.method0.staticSites[0]!).2
theorem correctness : PublishedTable.read.Holds Extracted.program 0 := by
  rintro input memory ⟨formed, registry, absent⟩
  have world : StaticWorldValid [descriptor] memory :=
    StaticWorldValid.of_absent _ _ (by decide) (by simp) registry (by simpa [descriptor, PublishedTable.identity, Extracted.method0] using absent)
  obtain ⟨result, reference, resolved, _, valid⟩ := staticReference_valid_result descriptor [descriptor] memory formed world (by simp)
  have loaded : read result reference 8 1 = .ok (numberBytes (17#64).toNat 8) := by
    simpa [descriptor, Extracted.method0, numberBytes] using valid.2.choose_spec.2.2.2.2
  have load := load_word64_of_read loaded
  have referenceValid := staticReference_reference_valid _ _ _ _ resolved
  have addressed : staticInstruction Extracted.method0 0 (.staticAddress descriptor.bytes) [] memory =
      .ok (result, [.reference (.address reference)]) := by
    simp [descriptor, Extracted.method0, staticInstruction, resolved, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨8, result, [.scalar (.i64 17)], ?_,
    Confined.ofMemoryBelow (staticReference_preserves_memory_below _ _ _ _ resolved)
      (Nat.le_refl _) (staticReference_extends_allocations _ _ _ _ resolved).next,
    17, rfl, rfl⟩
  cil_checked_steps [addressed, load, referenceValid]
end LibraryProof
""");
File.WriteAllText(Path.Combine(libArtifact, "verification.json"), JsonSerializer.Serialize(new
{
    schema = 1, proof = Path.GetRelativePath(libArtifact, proof), theorem = "LibraryProof.correctness",
    proofRoot = Path.GetRelativePath(libArtifact, package)
}));
Run(["lake", "update"], package);
Run(["lake", "update"], caller);
string manifest = Path.Combine(root, "export.json");
File.WriteAllText(manifest, JsonSerializer.Serialize(new
{
    schema = 1, assembly = lib, proofRoot = package,
    @interface = new[] { new { module = "PublishedTable", source = contract } },
    exports = new[] { new { method = "StaticFixture.Library::Read()", artifact = libArtifact, contract = "PublishedTable.read", theorem = "LibraryProof.correctness" } }
}));
string sidecar = Path.Combine(libRoot, "StaticFixture.Lib.leancil.contracts");
Run([.. cli, "export-contracts", manifest, "--output", sidecar]);
JsonObject published = JsonNode.Parse(File.ReadAllText(sidecar))!.AsObject();
if (published["certifications"]![0]!["staticIdentities"]!.AsArray().Count != 1 ||
    published["certifications"]![0]!["staticIdentities"]![0]!["identity"]!.GetValue<string>() != libKey)
    throw new InvalidOperationException("Published certification lost its kernel-bound static identity.");
string callerProof = Path.Combine(caller, "CallerProof.lean");
File.WriteAllText(callerProof, """
import ExtractedImports
import CIL.Safety.MethodContract
namespace CallerProof
open CIL.Safety
theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
    (fun linked => PublishedTable.read.Holds linked 0) := by
  intro linked links imported input memory permitted
  have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
  have holds : PublishedTable.read.Holds linked 1 := imported
  dsimp only [PublishedTable.read, MethodContract.Returns]
  refine invoke_exists_of_run found (by rfl) (by rfl) ?_
  refine run_call_of_contract holds input found
    (by rfl : Extracted.method0.code[0]? = some (.call 1 0)) (by cil_checked_step) rfl permitted ?_
  rintro final values _ framed returns
  obtain ⟨output, rfl, result⟩ := returns
  refine run_return_exists found (by rfl : Extracted.method0.code[1]? = some (.ret none))
    (by cil_checked_step) (by rfl) ?_
  exact ⟨framed, output, rfl, result⟩
end CallerProof
""");
string[] ExtractApp(string output) => [.. cli, "extract", app, "StaticFixture.Application::Entry()", output,
    "--import", sidecar, "--import-implementation", "StaticFixture.Lib=" + lib,
    "--import-sha256", "StaticFixture.Lib=" + Sha(lib), "--import-interface-sha256", "StaticFixture.Lib=" + published["interfaceDigest"]!.GetValue<string>()];
Run(ExtractApp(appArtifact));
Run([.. cli, "verify", appArtifact, "--proof", callerProof, "--proof-root", caller, "--fresh"]);
JsonObject report = JsonNode.Parse(File.ReadAllText(Path.Combine(appArtifact, "verified.json")))!.AsObject();
if (report["imports"]![0]!["staticIdentities"]![0]!["identity"]!.GetValue<string>() != libKey)
    throw new InvalidOperationException("Verified deployment report omitted the imported static identity.");
Console.WriteLine("PASS RVA static export, public identity-only precondition, imported caller and report provenance");

string ScopedKey(string assemblyIdentity, string fieldName)
{
    using MemoryStream encoded = new();
    using (BinaryWriter writer = new(encoded, Encoding.UTF8, leaveOpen: true))
        foreach (string part in new[] { assemblyIdentity, fieldName })
        {
            byte[] bytes = Encoding.UTF8.GetBytes(part);
            writer.Write(bytes.Length);
            writer.Write(bytes);
        }
    return new BigInteger(SHA256.HashData(encoded.ToArray()), isUnsigned: true, isBigEndian: true).ToString(System.Globalization.CultureInfo.InvariantCulture);
}
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
Reject(value => value["certifications"]![0]!.AsObject().Remove("staticIdentities"), "Missing contract interface field: staticIdentities");
Reject(value => value["certifications"]![0]!["staticIdentities"] = new JsonArray(), "static identities differ from the selected implementation");
Reject(value => value["certifications"]![0]!["staticIdentities"]![0]!["identity"] = "0", "Invalid scoped static identity");
Reject(value =>
{
    JsonNode identity = value["certifications"]![0]!["staticIdentities"]![0]!;
    identity["fieldName"] = "StaticFixture.Blob StaticFixture.Data::Missing";
    identity["identity"] = ScopedKey(identity["assemblyIdentity"]!.GetValue<string>(), identity["fieldName"]!.GetValue<string>());
}, "Certified static field is not present");
Reject(value => value["certifications"]![0]!["staticIdentities"]!.AsArray().Add(libStatic.DeepClone()), "Invalid or duplicate contract certification");
Reject(value =>
{
    JsonNode conflicting = libStatic.DeepClone();
    conflicting["fieldName"] = "StaticFixture.Blob StaticFixture.Data::Collision";
    value["certifications"]![0]!["staticIdentities"]!.AsArray().Add(conflicting);
}, "Static identity collision " + libKey + ": " + libStatic["assemblyIdentity"]!.GetValue<string>() + "::" + libStatic["fieldName"]!.GetValue<string>() + " and ");
File.WriteAllText(sidecar, published.ToJsonString());

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
