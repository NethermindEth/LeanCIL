#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ImportReviewRegressions.cs

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
  refine ⟨12, memory, [.scalar (.i64 (value + 1))], ?execution,
    Confined.refl _ memory, value + 1, rfl, ?post⟩
  case post => simp only [CIL.importedPost]
  case execution =>
    cil_checked_steps
    all_goals bv_omega
#print axioms correctness
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
    Run([.. cli, "export-contracts", manifest, "--output", sidecar, "--bundle", Path.Combine(root, "Bundles")]);
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
FullTransitive();
ImportReviewRegressions.ValidateGraph_WhenDuplicateImplementationHashDiffers_RejectsIdentity(ExtractorPath, originalB);
ImportReviewRegressions.ImportResolution_WhenTwoVersionsShareSimpleName_RejectsAmbiguity(
    ExtractorPath, bSidecar, b, Path.Combine(root, "AmbiguousVersions"));
Console.WriteLine("PASS conflicting duplicate implementation hashes and ambiguous assembly simple names reject at their production boundaries");
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
if (weakened.Code != 1 || !weakened.Output.Contains("Type mismatch", StringComparison.Ordinal) || Sha(aSidecar) != certifiedA)
    throw new InvalidOperationException("Conditional export accepted an extra hypothesis or replaced the sidecar: " + weakened.Output);

foreach (string entry in new[] { "Entry", "Direct" })
{
    string artifact = Path.Combine(root, "App-" + entry);
    Run([.. cli, "extract", app, "ImportFixture.Application::" + entry + "(ulong)", artifact,
        .. Import(aSidecar, a), .. Import(bSidecar, b)]);
    Run([.. cli, "verify", artifact, "--proof", Path.Combine(appPackage, "Conditional.lean"), "--proof-root", appPackage, "--fresh"]);
    JsonElement identity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "identity.json")));
    JsonElement report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "verified.json")));
    foreach (JsonElement node in identity.GetProperty("importGraph").EnumerateArray())
        foreach (string field in new[] { "implementationPath", "sidecarPath" })
            if (node.GetProperty(field).GetString() is not { } path || Path.IsPathRooted(path) || path.Contains('\\') ||
                !File.Exists(ExtractionIdentity.Resolve(artifact, path)))
                throw new InvalidOperationException("Graph path is not portable or does not resolve: " + field);
    JsonElement conditionalA = report.GetProperty("contractDependencies").EnumerateArray()
        .Single(node => node.GetProperty("assemblyIdentity").GetString() == originalA["assemblyIdentity"]!.GetValue<string>());
    if (!conditionalA.GetProperty("conditional").GetBoolean() || conditionalA.GetProperty("dependencies")[0].GetString() != originalB["assemblyIdentity"]!.GetValue<string>())
        throw new InvalidOperationException("The report lost A's conditional dependency on B.");
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
Reject("Missing independently pinned contract dependency: " + originalB["assemblyIdentity"]!.GetValue<string>() +
    " required by " + originalA["assemblyIdentity"]!.GetValue<string>(), includeB: false);
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
Console.WriteLine("PASS missing nodes, dependency hash mismatch, interface mismatch and named A -> B -> A cycles reject without artifacts");

// App -> A -> B under forced full verification: B's bundle is replayed because A's regenerated extraction imports it.
void FullTransitive()
{
    string Bundle(JsonObject contract, string sidecar) =>
        Path.GetFullPath(contract["fullVerificationLocator"]!.GetValue<string>(), Path.GetDirectoryName(sidecar)!);
    string aBundle = Bundle(originalA, aSidecar);
    string bBundle = Bundle(originalB, bSidecar);
    string callerProof = Path.Combine(appPackage, "Conditional.lean");
    string artifact = Path.Combine(root, "App-Full");
    Run([.. cli, "extract", app, "ImportFixture.Application::Entry(ulong)", artifact,
        .. Import(aSidecar, a), .. Import(bSidecar, b)]);
    string[] command = [.. cli, "verify", artifact, "--proof", callerProof, "--proof-root", appPackage,
        "--force-full-verify"];
    void RejectFull(string marker)
    {
        (int Code, string Output, string Stdout, string Stderr) result = Execute(command);
        if (result.Code != 1 || !result.Output.Contains(marker, StringComparison.Ordinal) ||
            File.Exists(Path.Combine(artifact, "verified.json")))
            throw new InvalidOperationException(
                "Full verification accepted an unchecked dependency: " + result.Output);
    }
    // B has no evidence of its own here, so the caller's composition must not fall back to B's sidecar.
    string hidden = bBundle + "-hidden";
    Directory.Move(bBundle, hidden);
    try { RejectFull("Full verification source bundle is missing: " + bBundle); }
    finally { Directory.Move(hidden, bBundle); }
    // A cooperating publisher republishes B's bundle with a proof that no longer closes; only B's own
    // library build can see that, and it runs before A's.
    string staging = Path.Combine(root, "rebundle-b");
    CopyTree(bBundle, staging);
    string bProofSource = Directory.EnumerateFiles(staging, "BProof.lean", SearchOption.AllDirectories).Single();
    File.WriteAllText(bProofSource, File.ReadAllText(bProofSource).Replace("cil_checked_steps", "sorry"));
    JsonObject inventory = JsonNode.Parse(File.ReadAllText(Path.Combine(staging, "bundle.json")))!.AsObject();
    inventory["files"]![Path.GetRelativePath(staging, bProofSource).Replace('\\', '/')] = Sha(bProofSource);
    File.WriteAllText(Path.Combine(staging, "bundle.json"), inventory.ToJsonString());
    string republished = Path.Combine(root, Sha(Path.Combine(staging, "bundle.json")));
    Directory.Move(staging, republished);
    JsonObject repointed = originalB.DeepClone().AsObject();
    repointed["fullVerificationLocator"] = republished;
    File.WriteAllText(bSidecar, repointed.ToJsonString());
    try
    {
        Run([.. cli, "extract", app, "ImportFixture.Application::Entry(ulong)", artifact,
            .. Import(aSidecar, a), .. Import(bSidecar, b)]);
        RejectFull("Unapproved proof axioms: sorryAx");
    }
    finally { File.WriteAllText(bSidecar, originalB.ToJsonString()); }
    Run([.. cli, "extract", app, "ImportFixture.Application::Entry(ulong)", artifact,
        .. Import(aSidecar, a), .. Import(bSidecar, b)]);

    string trace = Path.Combine(root, "trace-full");
    string? previousTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
    try { Run(command); }
    finally { Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", previousTrace); }
    (string Stage, string Command)[] traced = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line))
        .OrderBy(record => record.GetProperty("startedAtUtc").GetDateTimeOffset())
        .Select(record => (record.GetProperty("stage").GetString()!,
            string.Join(' ', record.GetProperty("command").EnumerateArray().Select(part => part.GetString()))))
        .ToArray();
    string[] stages = traced.Select(record => record.Stage).ToArray();
    int Last(string stage) => Array.FindLastIndex(stages, item => item == stage);
    int[] libraries = Enumerable.Range(0, stages.Length).Where(index => stages[index] is
        "Building fresh Lean verification library" or "Copying certified Lean verification library").ToArray();
    int Capture(int id) => Array.FindIndex(traced, record =>
        record.Command.Contains("LeanCILCaptureLeanCILFullLibrary" + id + ".lean", StringComparison.Ordinal));
    // A and B each get a fresh extraction and library build; the caller has its own build. Both extractions
    // precede both library builds, and B (id 1) is checked before A (id 0) imports it.
    if (stages.Count(stage => stage == "Fresh extraction of the current imported library DLL") != 2 ||
        stages.Count(stage => stage == "Capturing actual checked author and extraction kernel terms") != 2 ||
        libraries.Length != 3 ||
        stages.Count(stage => stage == "Independent kernel replay of the composed caller theorem") != 1 ||
        Last("Fresh extraction of the current imported library DLL") > libraries[1] ||
        Capture(1) < 0 || Capture(0) < 0 || Capture(1) > libraries[2] || Capture(1) > Capture(0))
        throw new InvalidOperationException(
            "Full verification skipped or misordered a transitive replay: " + string.Join(", ", stages));
    JsonElement verified =
        JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "verified.json")));
    JsonElement import = verified.GetProperty("imports").EnumerateArray().Single();
    Dictionary<string, string?> accepted = verified.GetProperty("contractDependencies").EnumerateArray().ToDictionary(
        node => node.GetProperty("assemblyIdentity").GetString()!,
        node => node.GetProperty("acceptedVia").GetString() == "independently-verified"
            ? node.GetProperty("sourceBundleDigest").GetString() : null);
    bool published = import.GetProperty("acceptedVia").GetString() == "independently-verified" &&
        import.GetProperty("sourceBundleDigest").GetString() == Path.GetFileName(aBundle) &&
        accepted.Count == 2 &&
        accepted[originalA["assemblyIdentity"]!.GetValue<string>()] == Path.GetFileName(aBundle) &&
        accepted[originalB["assemblyIdentity"]!.GetValue<string>()] == Path.GetFileName(bBundle) &&
        verified.GetProperty("compositionTheorem").GetString() == "LeanCILFullComposition.certified";
    if (!published)
        throw new InvalidOperationException("Full verification did not publish both checked bundles: " + verified);
    Console.WriteLine("PASS App -> A -> B forced full verification replays both bundles and rejects a missing " +
        "dependency bundle in preflight and a republished one whose proof fails its own library build");
}
