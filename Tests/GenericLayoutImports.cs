#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

using System.Reflection;
using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;
using Mono.Cecil.Cil;

string root = At("artifacts/GenericLayoutImports-" + Guid.NewGuid().ToString("N"));
string libRoot = Path.Combine(root, "Lib");
string appRoot = Path.Combine(root, "App");
string package = Path.Combine(root, "Proofs");
foreach (string directory in new[] { libRoot, appRoot, package }) Directory.CreateDirectory(directory);
string[] cli = ["dotnet", ExtractorPath];
string libProject = Path.Combine(libRoot, "Lib.csproj");
string appProject = Path.Combine(appRoot, "App.csproj");
const string libProjectText = "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>TypedFixture.Lib</AssemblyName><Optimize>true</Optimize></PropertyGroup></Project>";
File.WriteAllText(libProject, libProjectText);
File.WriteAllText(appProject, "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>TypedFixture.App</AssemblyName><Optimize>true</Optimize></PropertyGroup><ItemGroup><ProjectReference Include=\"../Lib/Lib.csproj\" /></ItemGroup></Project>");
string libSource = Path.Combine(libRoot, "Library.cs");
const string libSourceText = """
using System;
using System.Runtime.Intrinsics.X86;
namespace TypedFixture;
internal struct A_Private { public uint Tag; public A_Private(uint tag) { Tag = tag; } }
public struct Leaf { public ulong Value; }
public struct Pair { public Leaf Head; }
public static class Library
{
    public static void Copy(in Pair source, out Pair destination)
    {
        if (Avx2.IsSupported) GC.KeepAlive(typeof(A_Private));
        destination.Head.Value = source.Head.Value;
    }
    public static T Identity<T>(T value) where T : unmanaged => value;
    public static T Unsupported<T>(T value) where T : class => value;
}
public static class Generic<T> { public static ulong Value(ulong value) => value; }
""";
File.WriteAllText(libSource, libSourceText);
File.WriteAllText(Path.Combine(appRoot, "Application.cs"), """
namespace TypedFixture;
public static class Application
{
    public static void Forward(in Pair source, out Pair destination) => Library.Copy(in source, out destination);
    public static ulong Identity(ulong value) => Library.Identity(value);
    public static uint Unlisted(uint value) => Library.Identity(value);
    public static ulong ByValue(Pair value) => value.Head.Value;
    public static ulong Local() { Pair value = default; return value.Head.Value; }
}
""");
Run(["dotnet", "build", appProject, "-c", "Release"]);
string lib = Path.Combine(libRoot, "bin", "TypedFixture.Lib.dll");
string app = Path.Combine(appRoot, "bin", "TypedFixture.App.dll");
string revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"typed-import-proofs\"\n[[require]]\nname = \"leancil\"\ngit = " + JsonSerializer.Serialize(Root.Replace('\\', '/')) +
    "\nrev = " + JsonSerializer.Serialize(revision) +
    "\n[[lean_lib]]\nname = \"TypedImportInterface\"\n[[lean_lib]]\nname = \"TypedIdentityProof\"\n[[lean_lib]]\nname = \"TypedCopyProof\"\n[[lean_lib]]\nname = \"TypedIdentityCaller\"\n[[lean_lib]]\nname = \"TypedCopyCaller\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
foreach (string name in new[] { "TypedImportInterface", "TypedIdentityProof", "TypedCopyProof", "TypedIdentityCaller", "TypedCopyCaller" })
    File.Copy(At("Tests/ContractImports/" + name + ".lean"), Path.Combine(package, name + ".lean"));
Run(["lake", "update"], package);
string copyArtifact = Path.Combine(root, "Copy");
string identityArtifact = Path.Combine(root, "Identity");
string manifest = Path.Combine(root, "export.json");
string sidecar = Path.Combine(libRoot, "bin", "TypedFixture.Lib.leancil.contracts");
string bundle = Path.Combine(root, "Bundles");

void ExtractProducer()
{
    Run([.. cli, "extract", lib, "TypedFixture.Library::Copy(TypedFixture.Pair&,TypedFixture.Pair&)", copyArtifact]);
    Run([.. cli, "extract", lib, "TypedFixture.Library::Identity(T)", identityArtifact, "--type-argument", "System.UInt64"]);
    foreach ((string artifact, string proof) in new[] { (copyArtifact, "TypedCopyProof"), (identityArtifact, "TypedIdentityProof") })
        File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(new
        {
            schema = 1, proof = Path.GetRelativePath(artifact, Path.Combine(package, proof + ".lean")),
            theorem = proof + ".correctness", proofRoot = Path.GetRelativePath(artifact, package)
        }));
    JsonElement copyIdentity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(copyArtifact, "identity.json")));
    string[] layouts = copyIdentity.GetProperty("layoutIdentities").Deserialize<string[]>()!;
    if (layouts.Length != 3 || !layouts[0].EndsWith("::TypedFixture.A_Private", StringComparison.Ordinal) ||
        !layouts[1].EndsWith("::TypedFixture.Leaf", StringComparison.Ordinal) || !layouts[2].EndsWith("::TypedFixture.Pair", StringComparison.Ordinal))
        throw new InvalidOperationException("Precondition: private layout must precede the nested public closure in the actual extraction.");
}

void Publish()
{
    ExtractProducer();
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        schema = 1, assembly = lib, proofRoot = package,
        @interface = new[] { new { module = "TypedImportInterface", source = Path.Combine(package, "TypedImportInterface.lean") } },
        exports = new object[]
        {
            new { method = "TypedFixture.Library::Copy(TypedFixture.Pair&,TypedFixture.Pair&)", artifact = copyArtifact,
                contract = "TypedImportInterface.copy", theorem = "TypedCopyProof.correctness" },
            new { method = "TypedFixture.Library::Identity(T)", typeArguments = new[] { "System.UInt64" }, artifact = identityArtifact,
                contract = "TypedImportInterface.identity", theorem = "TypedIdentityProof.correctness" }
        }
    }));
    Run([.. cli, "export-contracts", manifest, "--output", sidecar, "--bundle", bundle]);
}

string[] Import(string selectedSidecar, string digest) => ["--import", selectedSidecar,
    "--import-implementation", "TypedFixture.Lib=" + lib, "--import-sha256", "TypedFixture.Lib=" + Sha(lib),
    "--import-interface-sha256", "TypedFixture.Lib=" + digest];

void Reject(string name, string marker, string dll, string selector, string selectedSidecar, string digest, params string[] extra)
{
    string output = Path.Combine(root, "Reject-" + name);
    (int Code, string Output, string Stdout, string Stderr) result = Execute(
        [.. cli, "extract", dll, selector, output, .. Import(selectedSidecar, digest), .. extra]);
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal) ||
        File.Exists(Path.Combine(output, "Extracted.lean")) || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Expected metadata rejection " + name + ": " + result.Output);
}

Publish();
JsonObject original = JsonNode.Parse(File.ReadAllText(sidecar))!.AsObject();
string interfaceDigest = original["interfaceDigest"]!.GetValue<string>();
if (original["formatVersion"]!.GetValue<int>() != 2 ||
    original["exports"]!.AsArray().Single(export => export!["typeArguments"]!.AsArray().Count == 0)!["layouts"]!.AsArray().Count != 2)
    throw new InvalidOperationException("Typed interface omitted the signature-scoped nested layout closure.");

// Use the production canonical descriptor hash instead of duplicating its field projection.
Type descriptorType = Assembly.LoadFrom(ExtractorPath).GetType("Nethermind.LeanCIL.ContractInterface")!;
JsonSerializerOptions descriptorOptions = (JsonSerializerOptions)descriptorType.GetField("Json", BindingFlags.Static | BindingFlags.NonPublic)!.GetValue(null)!;
string InterfaceDigest(JsonObject contract)
{
    object value = JsonSerializer.Deserialize(contract.ToJsonString(), descriptorType, descriptorOptions)!;
    return (string)descriptorType.GetMethod("ComputeInterfaceDigest", BindingFlags.Instance | BindingFlags.NonPublic)!.Invoke(value, null)!;
}

foreach ((string name, Action<JsonObject> mutate) in new (string, Action<JsonObject>)[]
{
    ("Packing", contract => contract["packing"] = 1),
    ("Size", contract => contract["declaredSize"] = 16),
    ("NestedScope", contract => contract["fields"]![0]!["type"]!["scope"] = "Other, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null")
})
{
    JsonObject changed = original.DeepClone().AsObject();
    JsonObject copy = changed["exports"]!.AsArray().Single(export => export!["typeArguments"]!.AsArray().Count == 0)!.AsObject();
    mutate(copy["layouts"]![1]!.AsObject());
    string digest = InterfaceDigest(changed);
    changed["interfaceDigest"] = digest;
    foreach (JsonNode? certification in changed["certifications"]!.AsArray()) certification!["interfaceDigest"] = digest;
    string tampered = Path.Combine(root, name + ".leancil.contracts");
    File.WriteAllText(tampered, changed.ToJsonString());
    Reject(name, "raw layout differs", app, "TypedFixture.Application::Forward(TypedFixture.Pair&,TypedFixture.Pair&)", tampered, digest);
}

Reject("Unlisted", "Contract export not present", app, "TypedFixture.Application::Unlisted(uint)", sidecar, interfaceDigest);
Reject("ByValue", "Unsupported type", app, "TypedFixture.Application::ByValue(TypedFixture.Pair)", sidecar, interfaceDigest);
Reject("Local", "Unsupported type", app, "TypedFixture.Application::Local()", sidecar, interfaceDigest);
Reject("Open", "primitive integer", lib, "TypedFixture.Library::Identity(T)", sidecar, interfaceDigest, "--type-argument", "!!0");
Reject("WrongArity", "exact closed generic", lib, "TypedFixture.Library::Identity(T)", sidecar, interfaceDigest,
    "--type-argument", "System.UInt64", "--type-argument", "System.UInt32");
Reject("Constraint", "constraints", lib, "TypedFixture.Library::Unsupported(T)", sidecar, interfaceDigest, "--type-argument", "System.UInt64");
Reject("GenericOwner", "exact closed generic", lib, "TypedFixture.Generic`1::Value(ulong)", sidecar, interfaceDigest);
Reject("Profile", "profile not listed", app, "TypedFixture.Application::Identity(ulong)", sidecar, interfaceDigest, "x64-v3");

foreach (string modifierScope in new[] { "ModifierA", "ModifierB" })
{
    string malformed = Path.Combine(root, modifierScope + ".dll");
    using (ModuleDefinition module = ModuleDefinition.ReadModule(app))
    {
        MethodReference call = module.GetType("TypedFixture.Application").Methods.Single(method => method.Name == "Forward")
            .Body.Instructions.Where(instruction => instruction.OpCode.Code == Code.Call).Select(instruction => (MethodReference)instruction.Operand).Single();
        ByReferenceType parameter = (ByReferenceType)call.Parameters[0].ParameterType;
        TypeReference modifier = new("System.Runtime.InteropServices", "InAttribute", module, new AssemblyNameReference(modifierScope, new Version(1, 0, 0, 0)));
        call.Parameters[0].ParameterType = new ByReferenceType(new RequiredModifierType(modifier, parameter.ElementType));
        module.Write(malformed);
    }
    Reject(modifierScope, "Custom modifiers", malformed, "TypedFixture.Application::Forward(TypedFixture.Pair&,TypedFixture.Pair&)", sidecar, interfaceDigest);
}

string wrongScope = Path.Combine(root, "WrongScope.dll");
using (ModuleDefinition module = ModuleDefinition.ReadModule(app))
{
    GenericInstanceMethod call = module.GetType("TypedFixture.Application").Methods.Single(method => method.Name == "Identity")
        .Body.Instructions.Select(instruction => instruction.Operand).OfType<GenericInstanceMethod>().Single();
    call.GenericArguments[0] = new TypeReference("System", "UInt64", module,
        new AssemblyNameReference("Other", new Version(1, 0, 0, 0))) { IsValueType = true };
    module.Write(wrongScope);
}
Reject("WrongScope", "exact scoped", wrongScope, "TypedFixture.Application::Identity(ulong)", sidecar, interfaceDigest);

if (InterfaceDigest(original) != interfaceDigest)
    throw new InvalidOperationException("Typed sidecar differs from its canonical interface digest.");

foreach ((string name, string selector, string proof) in new[]
{
    ("Forward", "TypedFixture.Application::Forward(TypedFixture.Pair&,TypedFixture.Pair&)", "TypedCopyCaller"),
    ("Identity", "TypedFixture.Application::Identity(ulong)", "TypedIdentityCaller")
})
{
    string artifact = Path.Combine(root, "App-" + name);
    Run([.. cli, "extract", app, selector, artifact, .. Import(sidecar, interfaceDigest)]);
    string author = Path.Combine(package, proof + ".lean");
    Run([.. cli, "verify", artifact, "--proof", author, "--theorem", proof + ".correctness", "--proof-root", package]);
    Run([.. cli, "verify", artifact, "--proof", author, "--theorem", proof + ".correctness", "--proof-root", package, "--force-full-verify"]);
    JsonElement report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "verified.json")));
    JsonElement imported = report.GetProperty("imports")[0];
    if (imported.GetProperty("acceptedVia").GetString() != "independently-verified" ||
        imported.GetProperty("implementationSha256").GetString() != Sha(lib) || !imported.TryGetProperty("typedSignature", out _))
        throw new InvalidOperationException("Full verification omitted typed import or exact implementation evidence.");
    Console.WriteLine("PASS typed imported " + name + ": actual SDK DLL, exact contract and independent linked proof");
}
Console.WriteLine("PASS typed layout metadata, closed instances, modifier rejection and canonical sidecar digest");
