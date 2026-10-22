#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Numerics;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;

string root = At("artifacts/TransitiveImports-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
string[] cli = ["dotnet", ExtractorPath];
string revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
string Project(string name, params string[] references)
{
    string directory = Path.Combine(root, name);
    Directory.CreateDirectory(directory);
    File.WriteAllText(Path.Combine(directory, name + ".csproj"),
        "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework>" +
        "<AssemblyName>ImportFixture." + name + "</AssemblyName><Optimize>true</Optimize></PropertyGroup><ItemGroup>" +
        string.Join("", references.Select(reference => "<ProjectReference Include=\"../" + reference + "/" + reference + ".csproj\" />")) +
        "</ItemGroup></Project>");
    return directory;
}
string bRoot = Project("B");
string aRoot = Project("A", "B");
string appRoot = Project("App", "A", "B");
File.WriteAllText(Path.Combine(bRoot, "Library.cs"), "namespace ImportFixture; public static class LibraryB { public const ulong CertificateMarker = 17; public static ulong AddOne(ulong value) => value + 1; }\n");
File.WriteAllText(Path.Combine(aRoot, "Library.cs"), "namespace ImportFixture; public static class LibraryA { public static ulong AddOne(ulong value) => LibraryB.AddOne(value); }\n");
File.WriteAllText(Path.Combine(appRoot, "Application.cs"), "namespace ImportFixture; public static class Application { public static ulong Entry(ulong value) => LibraryA.AddOne(value); public static ulong Direct(ulong value) => LibraryB.AddOne(value); }\n");
Run(["dotnet", "build", Path.Combine(appRoot, "App.csproj"), "-c", "Release"]);
string a = Path.Combine(aRoot, "bin/ImportFixture.A.dll");
string b = Path.Combine(bRoot, "bin/ImportFixture.B.dll");
string app = Path.Combine(appRoot, "bin/ImportFixture.App.dll");
string aSidecar = Path.Combine(aRoot, "bin/ImportFixture.A.leancil.contracts");
string bSidecar = Path.Combine(bRoot, "bin/ImportFixture.B.leancil.contracts");

string Package(string name, params string[] modules)
{
    string directory = Path.Combine(root, name);
    Directory.CreateDirectory(directory);
    File.Copy(At("lean-toolchain"), Path.Combine(directory, "lean-toolchain"));
    File.WriteAllText(Path.Combine(directory, "lakefile.toml"), "name = \"" + name.ToLowerInvariant() + "\"\n" +
        "[[require]]\nname = \"leancil\"\ngit = " + JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = \"" + revision + "\"\n" +
        string.Join("", modules.Select(module => "[[lean_lib]]\nname = \"" + module + "\"\n")));
    return directory;
}
string bPackage = Package("BProofPackage", "PublishedArithmetic", "BProof");
string aPackage = Package("AProofPackage", "APublished", "Conditional");
string appPackage = Package("AppProofPackage", "Conditional");
File.Copy(At("Tests/ContractImports/ImportFixture.lean"), Path.Combine(bPackage, "PublishedArithmetic.lean"));
File.WriteAllText(Path.Combine(aPackage, "APublished.lean"), "import PublishedArithmetic\n");
foreach (string package in new[] { aPackage, appPackage })
    File.Copy(At("Tests/TransitiveImports/Conditional.lean"), Path.Combine(package, "Conditional.lean"));
string bProof = Path.Combine(bPackage, "BProof.lean");
File.WriteAllText(bProof, """
import Extracted
import PublishedArithmetic
import CIL.Safety.SymbolicExecution
namespace BProof
open CIL.Safety
theorem correctness : CIL.Safety.MethodContract.Holds ImportFixture.addOne Extracted.program 0 := by
  rintro value memory formed
  dsimp only [ImportFixture.addOne, MethodContract.Returns]
  refine Exists.intro 12 (Exists.intro memory (Exists.intro _
    (And.intro ?execution (And.intro (Confined.refl _ memory) ?returns))))
  case returns => exact Exists.intro (value + 1) (And.intro rfl rfl)
  case execution =>
    cil_checked_steps
    all_goals bv_omega
end BProof
""");
foreach (string package in new[] { bPackage, aPackage, appPackage }) Run(["lake", "update"], package);
void Settings(string artifact, string package, string proof, string theorem)
{
    File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(new
    {
        schema = 1, proof = Path.GetRelativePath(artifact, proof).Replace('\\', '/'), theorem,
        proofRoot = Path.GetRelativePath(artifact, package).Replace('\\', '/')
    }));
}
void Export(string assembly, string artifact, string package, string sourceModule, string proof, string method, string theorem, string sidecar)
{
    Settings(artifact, package, proof, theorem);
    string manifest = Path.Combine(root, sourceModule + ".json");
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        schema = 1, assembly, proofRoot = package,
        @interface = new[] { new { module = sourceModule, source = Path.Combine(package, sourceModule + ".lean") } },
        exports = new[] { new { method, artifact, contract = "ImportFixture.addOne", theorem } }
    }));
    Run([.. cli, "export-contracts", manifest, "--output", sidecar]);
}
string[] Import(string sidecar, string assembly)
{
    JsonObject contract = JsonNode.Parse(File.ReadAllText(sidecar))!.AsObject();
    string name = Path.GetFileNameWithoutExtension(assembly);
    return ["--import", sidecar, "--import-implementation", name + "=" + assembly,
        "--import-sha256", name + "=" + Sha(assembly), "--import-interface-sha256", name + "=" + contract["interfaceDigest"]!.GetValue<string>()];
}
string bArtifact = Path.Combine(root, "ExtractB");
Run([.. cli, "extract", b, "ImportFixture.LibraryB::AddOne(ulong)", bArtifact]);
Export(b, bArtifact, bPackage, "PublishedArithmetic", bProof, "ImportFixture.LibraryB::AddOne(ulong)", "BProof.correctness", bSidecar);
string aArtifact = Path.Combine(root, "ExtractA");
Run([.. cli, "extract", a, "ImportFixture.LibraryA::AddOne(ulong)", aArtifact, .. Import(bSidecar, b)]);
Export(a, aArtifact, aPackage, "APublished", Path.Combine(aPackage, "Conditional.lean"),
    "ImportFixture.LibraryA::AddOne(ulong)", "ExampleProof.correctness", aSidecar);
JsonObject originalA = JsonNode.Parse(File.ReadAllText(aSidecar))!.AsObject();
JsonObject originalB = JsonNode.Parse(File.ReadAllText(bSidecar))!.AsObject();
if (originalA["dependencies"]!.AsArray().Count != 1 ||
    !originalA["certifications"]![0]!["statement"]!.GetValue<string>().Contains("HoldsGiven", StringComparison.Ordinal))
    throw new InvalidOperationException("Conditional A export lost its B dependency or its exact conditional statement.");
string certifiedA = Sha(aSidecar);
string aProof = Path.Combine(aPackage, "Conditional.lean");
File.AppendAllText(aProof, "\ntheorem ExampleProof.weakened (extra : False) : CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold " +
    "(fun linked => CIL.Safety.MethodContract.Holds ImportFixture.addOne linked 0) := False.elim extra\n");
JsonObject weakenedManifest = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "APublished.json")))!.AsObject();
weakenedManifest["exports"]![0]!["theorem"] = "ExampleProof.weakened";
string weakenedPath = Path.Combine(root, "Weakened.json");
File.WriteAllText(weakenedPath, weakenedManifest.ToJsonString());
(int Code, string Output, string Stdout, string Stderr) weakened = Execute([.. cli, "export-contracts", weakenedPath, "--output", aSidecar]);
if (weakened.Code != 1 || !weakened.Output.Contains("exact canonical Holds statement", StringComparison.Ordinal) || Sha(aSidecar) != certifiedA)
    throw new InvalidOperationException("Conditional export accepted an extra hypothesis or replaced the sidecar: " + weakened.Output);

foreach (string entry in new[] { "Entry", "Direct" })
{
    string artifact = Path.Combine(root, "App-" + entry);
    Run([.. cli, "extract", app, "ImportFixture.Application::" + entry + "(ulong)", artifact,
        .. Import(aSidecar, a), .. Import(bSidecar, b)]);
    Run([.. cli, "verify", artifact, "--proof", Path.Combine(appPackage, "Conditional.lean"), "--proof-root", appPackage, "--fresh"]);
    JsonElement identity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "identity.json")));
    JsonElement report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "verified.json")));
    if (identity.GetProperty("importGraph").GetArrayLength() != 2 || identity.GetProperty("imports").GetArrayLength() != 1 ||
        report.GetProperty("contractDependencies").GetArrayLength() != 2 ||
        identity.GetProperty("importGraph").EnumerateArray().Count(node => node.GetProperty("assemblyIdentity").GetString() == originalB["assemblyIdentity"]!.GetValue<string>()) != 1)
        throw new InvalidOperationException("App's assembly diamond duplicated B, invented a call slot, or omitted deployment dependencies.");
}
Console.WriteLine("PASS App -> A -> B and App's direct B entry with one B identity, exact proofs and fresh replay");

void Save(string path, JsonObject contract)
{
    JsonObject descriptor = new();
    foreach (string field in new[] { "schema", "semanticsVersion", "formatVersion", "frameworkKey", "assemblyIdentity", "targetFramework", "interfaceModules", "exports", "dependencies" })
        descriptor[field] = contract[field]!.DeepClone();
    contract["interfaceDigest"] = ContentKey(descriptor.ToJsonString());
    foreach (JsonNode? certification in contract["certifications"]!.AsArray())
        certification!["interfaceDigest"] = contract["interfaceDigest"]!.DeepClone();
    File.WriteAllText(path, contract.ToJsonString());
}
void Reject(string diagnostic, bool includeB = true)
{
    string output = Path.Combine(root, "Reject-" + Guid.NewGuid().ToString("N"));
    (int Code, string Output, string Stdout, string Stderr) rejected = Execute([.. cli, "extract", app,
        "ImportFixture.Application::Entry(ulong)", output, .. Import(aSidecar, a), .. includeB ? Import(bSidecar, b) : []]);
    if (rejected.Code != 1 || !rejected.Output.Contains(diagnostic, StringComparison.Ordinal) ||
        File.Exists(Path.Combine(output, "Extracted.lean")) || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Invalid transitive dependency was not rejected before extraction: " + rejected.Output);
}
Reject("Missing independently pinned contract dependency", includeB: false);
JsonObject wrong = originalA.DeepClone().AsObject();
wrong["dependencies"]![0]!["implementationSha256"] = new string('0', 64);
Save(aSidecar, wrong);
Reject("Contract dependency implementation hash mismatch: " + originalB["assemblyIdentity"]!.GetValue<string>());
wrong = originalA.DeepClone().AsObject();
wrong["dependencies"]![0]!["interfaceDigest"] = new string('0', 64);
Save(aSidecar, wrong);
Reject("Contract dependency interface digest mismatch: " + originalB["assemblyIdentity"]!.GetValue<string>());
Save(aSidecar, originalA);
JsonObject undeclared = originalA.DeepClone().AsObject();
undeclared["dependencies"] = new JsonArray();
Save(aSidecar, undeclared);
Reject("Undeclared contract dependency: " + originalB["assemblyIdentity"]!.GetValue<string>());
Save(aSidecar, originalA);
string markerAssembly = originalB["assemblyIdentity"]!.GetValue<string>();
string markerField = "System.UInt64 ImportFixture.LibraryB::CertificateMarker";
using MemoryStream encodedMarker = new();
using (BinaryWriter writer = new(encodedMarker, Encoding.UTF8, leaveOpen: true))
    foreach (string part in new[] { markerAssembly, markerField })
    {
        byte[] bytes = Encoding.UTF8.GetBytes(part);
        writer.Write(bytes.Length);
        writer.Write(bytes);
    }
string markerIdentity = new BigInteger(SHA256.HashData(encodedMarker.ToArray()), isUnsigned: true, isBigEndian: true)
    .ToString(System.Globalization.CultureInfo.InvariantCulture);
JsonObject falseStatics = originalB.DeepClone().AsObject();
falseStatics["certifications"]![0]!["staticIdentities"] = new JsonArray(new JsonObject
{
    ["identity"] = markerIdentity, ["assemblyIdentity"] = markerAssembly, ["fieldName"] = markerField
});
Save(bSidecar, falseStatics);
Reject("Contract import static identities differ from the selected implementation.");
Save(bSidecar, originalB);
JsonObject cycle = originalB.DeepClone().AsObject();
cycle["dependencies"] = new JsonArray(new JsonObject
{
    ["assemblyIdentity"] = originalA["assemblyIdentity"]!.DeepClone(),
    ["implementationSha256"] = originalA["implementationSha256"]!.DeepClone(),
    ["interfaceDigest"] = originalA["interfaceDigest"]!.DeepClone()
});
Save(bSidecar, cycle);
Reject("Contract dependency cycle: " + originalA["assemblyIdentity"]!.GetValue<string>() + " -> " +
    originalB["assemblyIdentity"]!.GetValue<string>() + " -> " + originalA["assemblyIdentity"]!.GetValue<string>());
Console.WriteLine("PASS missing nodes, conflicting B hashes, interface mismatch and named A -> B -> A cycles reject without artifacts");
