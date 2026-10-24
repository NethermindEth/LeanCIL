#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../Extractor/RuntimeAssetSelection.cs

using System.IO.Compression;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;
using Nethermind.LeanCIL;

if (args.Length != 6) throw new ArgumentException("Expected sidecar, caller proof/package, producer package/proof/interface source.");
string originalSidecar = args[0];
string callerProof = args[1];
string callerPackage = args[2];
string producerPackage = args[3];
string producerProof = args[4];
string interfaceSource = args[5];
JsonObject contract = JsonNode.Parse(File.ReadAllText(originalSidecar))!.AsObject();
string digest = contract["interfaceDigest"]!.GetValue<string>();
string root = At("artifacts/ContractDiscovery-" + Guid.NewGuid().ToString("N"));
string producer = Path.Combine(root, "Producer");
string consumer = Path.Combine(root, "Consumer");
string feed = Path.Combine(root, "Feed");
string packages = Path.Combine(root, "Packages");
foreach (string directory in new[] { producer, consumer, feed }) Directory.CreateDirectory(directory);
string[] cli = ["dotnet", ExtractorPath];
const string Library = "ImportFixture.Lib";
const string Package = "LeanCil.Discovery.Fixture";
const string Selector = "ImportFixture.Application::Entry(ulong)";
string Hash(byte[] bytes) => Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes));
bool Same(string? left, string right) => left is not null && string.Equals(Path.GetFullPath(left), Path.GetFullPath(right),
    OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal);

File.WriteAllText(Path.Combine(producer, "Producer.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
<AssemblyName>ImportFixture.Lib</AssemblyName><Optimize>true</Optimize><ProduceReferenceAssembly>true</ProduceReferenceAssembly>
</PropertyGroup></Project>
""");
File.WriteAllText(Path.Combine(producer, "Library.cs"), """
using System;
[assembly: Nethermind.LeanCIL.LeanCilContracts("DIGEST")]
namespace Nethermind.LeanCIL {
  [AttributeUsage(AttributeTargets.Assembly, AllowMultiple = false)]
  public sealed class LeanCilContractsAttribute : Attribute {
    public LeanCilContractsAttribute(string digest) { }
  }
}
namespace ImportFixture { public static class Library {
  public static ulong AddOne(ulong value) => value + 1;
  public static ulong AddSame(ulong value) => value + 1;
} }
""".Replace("DIGEST", digest, StringComparison.Ordinal));
Run(["dotnet", "build", Path.Combine(producer, "Producer.csproj"), "-c", "Release"]);
// Directory.Build.props redirects outputs; ask MSBuild instead of assuming SDK layout.
JsonElement producerPaths = MsBuildProperties(Path.Combine(producer, "Producer.csproj"), "TargetPath", "TargetRefPath");
string implementation = producerPaths.GetProperty("TargetPath").GetString()!;
string reference = producerPaths.GetProperty("TargetRefPath").GetString()!;
using (ModuleDefinition metadata = ModuleDefinition.ReadModule(reference))
    if (!metadata.Assembly.CustomAttributes.Any(attribute => attribute.AttributeType.FullName == "Nethermind.LeanCIL.LeanCilContractsAttribute"))
        throw new InvalidOperationException("Actual SDK reference emission did not retain the discovery attribute.");

byte[] Variant(string marker)
{
    using ModuleDefinition metadata = ModuleDefinition.ReadModule(implementation);
    metadata.Resources.Add(new EmbeddedResource("Discovery.Variant", ManifestResourceAttributes.Private, Encoding.UTF8.GetBytes(marker)));
    using MemoryStream bytes = new();
    metadata.Write(bytes);
    return bytes.ToArray();
}
// Every candidate differs, so each selection is identified by its bytes.
Dictionary<string, byte[]> variants = new[] { "portable", "linux-x64", "linux-arm64", "unix-x64", "unix", "net9" }
    .ToDictionary(name => name, name => Variant(name + "-variant"));
using (ZipArchive archive = ZipFile.Open(Path.Combine(feed, Package + ".1.0.0.nupkg"), ZipArchiveMode.Create))
{
    void Entry(string path, byte[] bytes)
    {
        using Stream stream = archive.CreateEntry(path).Open();
        stream.Write(bytes);
    }
    Entry(Package + ".nuspec", Encoding.UTF8.GetBytes("""
<?xml version="1.0"?><package><metadata><id>LeanCil.Discovery.Fixture</id><version>1.0.0</version>
<authors>LeanCIL</authors><description>Discovery fixture</description>
<dependencies><group targetFramework="net10.0" /></dependencies></metadata></package>
"""));
    Entry("ref/net10.0/" + Library + ".dll", File.ReadAllBytes(reference));
    Entry("lib/net9.0/" + Library + ".dll", variants["net9"]);
    Entry("lib/net10.0/" + Library + ".dll", variants["portable"]);
    foreach (string rid in new[] { "linux-x64", "linux-arm64", "unix-x64", "unix" })
        Entry("runtimes/" + rid + "/lib/net10.0/" + Library + ".dll", variants[rid]);
    Entry("contracts/" + digest + ".leancil.contracts", Encoding.UTF8.GetBytes(contract.ToJsonString()));
}
File.WriteAllText(Path.Combine(consumer, "Consumer.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
<AssemblyName>ImportFixture.App</AssemblyName><Optimize>true</Optimize>
<ManagePackageVersionsCentrally>false</ManagePackageVersionsCentrally><CopyLocalLockFileAssemblies>true</CopyLocalLockFileAssemblies></PropertyGroup>
<ItemGroup><PackageReference Include="LeanCil.Discovery.Fixture" Version="1.0.0" /></ItemGroup></Project>
""");
File.WriteAllText(Path.Combine(consumer, "Application.cs"),
    "namespace ImportFixture; public static class Application { public static ulong Entry(ulong value) => Library.AddOne(value); }");
Run(["dotnet", "restore", Path.Combine(consumer, "Consumer.csproj"), "--source", feed, "--packages", packages]);
Run(["dotnet", "build", Path.Combine(consumer, "Consumer.csproj"), "-c", "Release", "--no-restore"]);
JsonElement consumerPaths = MsBuildProperties(Path.Combine(consumer, "Consumer.csproj"), "TargetPath", "RuntimeIdentifierGraphPath");
string application = consumerPaths.GetProperty("TargetPath").GetString()!;
string bin = Path.GetDirectoryName(application)!;
string graph = consumerPaths.GetProperty("RuntimeIdentifierGraphPath").GetString()!;
if (Path.GetFileName(graph) != "PortableRuntimeIdentifierGraph.json") throw new InvalidOperationException("SDK did not select its portable RID graph: " + graph);
string deps = Path.ChangeExtension(application, ".deps.json");
string assets = Path.Combine(consumer, "obj", "project.assets.json");
string packageRoot = Path.Combine(packages, Package.ToLowerInvariant(), "1.0.0");
string packagedSidecar = Path.Combine(packageRoot, "contracts", digest + ".leancil.contracts");
JsonObject sdkDeps = JsonNode.Parse(File.ReadAllText(deps))!.AsObject();
// The real SDK shape: no manifest RID graph, rid-only `unix` assets, app-local `localPath`.
if (sdkDeps.ContainsKey("runtimes") || !File.ReadAllText(deps).Contains("\"rid\": \"unix\"", StringComparison.Ordinal) ||
    !File.Exists(Path.Combine(bin, Library + ".dll")))
    throw new InvalidOperationException("SDK deps output no longer has the shape these resolver cases exercise.");

int resolutions = 0;
(int Code, string Output, JsonElement? Result) Resolve(string? rid, string depsFile = "", string assetsFile = "", string? ridGraph = "", params string[] extra)
{
    string output = Path.Combine(root, "Resolved", resolutions++ + ".json");
    (int code, string text, _, _) = Execute([.. cli, "resolve-imports", application, "--library", Library,
        "--deps", depsFile == "" ? deps : depsFile, "--assets", assetsFile == "" ? assets : assetsFile,
        .. rid is null ? Array.Empty<string>() : ["--runtime-identifier", rid],
        .. ridGraph is null ? Array.Empty<string>() : ["--rid-graph", ridGraph == "" ? graph : ridGraph],
        .. extra, "--output", output]);
    return (code, text, code == 0 ? JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(output)) : null);
}
JsonElement Selected(string? rid, string variant, string expectedPath, string depsFile = "")
{
    (int code, string text, JsonElement? result) = Resolve(rid, depsFile);
    if (code != 0) throw new InvalidOperationException("Resolution failed for " + rid + ": " + text);
    JsonElement import = result!.Value.GetProperty("imports").EnumerateArray().Single();
    string path = import.GetProperty("implementation").GetString()!;
    if (Hash(File.ReadAllBytes(path)) != Hash(variants[variant]) || !Same(path, expectedPath) ||
        !Same(import.GetProperty("sidecar").GetString(), packagedSidecar))
        throw new InvalidOperationException($"{rid ?? "portable"} selected {path}, expected the {variant} asset at {expectedPath}.");
    return result.Value;
}
void Rejected(string name, string marker, (int Code, string Output, JsonElement? Result) outcome)
{
    if (outcome.Code != 1 || !outcome.Output.Contains(marker, StringComparison.Ordinal))
        throw new InvalidOperationException(name + " did not fail at the intended resolver guard: " + outcome.Output);
}
string RidAsset(string rid) => Path.Combine(bin, "runtimes", rid, "lib", "net10.0", Library + ".dll");

// NuGet's RuntimeGraph.ExpandRuntime and the .NET 8+ host list are breadth-first:
// osx-x64 -> osx, unix-x64, unix and linux-musl-x64 -> linux-musl, linux-x64. A depth-first
// walk reaches unix first in both. The host ignores any deps.json RID graph.
Selected("linux-x64", "linux-x64", RidAsset("linux-x64"));
Selected("linux-arm64", "linux-arm64", RidAsset("linux-arm64"));
JsonElement osx = Selected("osx-x64", "unix-x64", RidAsset("unix-x64"));
if (string.Join(",", osx.GetProperty("ridFallback").EnumerateArray().Select(item => item.GetString())) != "osx-x64,osx,unix-x64,unix,any,base")
    throw new InvalidOperationException("RID fallback order differs from NuGet's breadth-first expansion: " + osx);
Selected("linux-musl-x64", "linux-x64", RidAsset("linux-x64"));
Selected("osx-arm64", "unix", RidAsset("unix"));
// No win group matches, so the portable runtime group applies; bin/Lib.dll is its localPath.
Selected("win-x64", "portable", Path.Combine(bin, Library + ".dll"));
using (JsonDocument sdkGraph = JsonDocument.Parse(File.ReadAllBytes(graph)))
using (JsonDocument selectedDeps = JsonDocument.Parse(File.ReadAllBytes(deps)))
    foreach (string rid in sdkGraph.RootElement.GetProperty("runtimes").EnumerateObject().Select(entry => entry.Name)
        .Where(rid => rid.EndsWith("-x64", StringComparison.Ordinal) || rid.EndsWith("-arm64", StringComparison.Ordinal)))
    {
        string[] fallback = RuntimeAssetSelection.Expand(sdkGraph.RootElement, rid);
        Dictionary<string, RuntimeAsset> selected = RuntimeAssetSelection.Select(selectedDeps.RootElement, true, rid, () => fallback,
            new HashSet<string>(StringComparer.Ordinal) { Library });
        if (!selected.TryGetValue(Library, out RuntimeAsset? asset) || asset.AssetPath.Length == 0)
            throw new InvalidOperationException("SDK graph RID did not select an implementation: " + rid);
    }
// SDK executables record localPath; the host probes the application directory exactly there.
string relocated = Path.Combine(bin, "alt", Library + ".dll");
Directory.CreateDirectory(Path.GetDirectoryName(relocated)!);
File.WriteAllBytes(relocated, variants["linux-x64"]);
JsonObject localDeps = Copy(deps);
EachLibrary(localDeps, library => library["runtimeTargets"]!["runtimes/linux-x64/lib/net10.0/" + Library + ".dll"]!["localPath"] = "alt/" + Library + ".dll");
Selected("linux-x64", "linux-x64", relocated, Write("local.deps.json", localDeps));
EachLibrary(localDeps, library => library["runtimeTargets"]!["runtimes/linux-x64/lib/net10.0/" + Library + ".dll"]!["localPath"] = "../" + Library + ".dll");
Rejected("unsafe localPath", "Unsafe discovery asset path", Resolve("linux-x64", Write("unsafe-local.deps.json", localDeps)));
Console.WriteLine("PASS actual SDK deps/assets and portable RID graph select the host's net10.0 runtime asset");

Rejected("portable without RID", "Runtime identifier is required", Resolve(null));
Rejected("RID without graph", "requires --rid-graph", Resolve("linux-x64", ridGraph: null));
string hostileGraph = Path.Combine(root, "hostile-graph.json");
File.WriteAllText(hostileGraph, """{"runtimes":{"linux-x64":{"#import":["win-x86"]},"win-x86":{"#import":[]}}}""");
Rejected("cross-architecture fallback", "Cross-architecture RID fallback", Resolve("linux-x64", ridGraph: hostileGraph));
File.WriteAllText(hostileGraph, """{"runtimes":{"linux-x64":{"imports":["linux"]}}}""");
Rejected("malformed graph", "Invalid RID graph entry", Resolve("linux-x64", ridGraph: hostileGraph));
Rejected("profile/RID mismatch", "Runtime identifier does not match the execution profile: linux-x64", Resolve("linux-x64", "", "", "", "--profile", "arm64-advsimd"));

string Write(string name, JsonNode document)
{
    string path = Path.Combine(root, name);
    File.WriteAllText(path, document.ToJsonString());
    return path;
}
void EachLibrary(JsonObject document, Action<JsonObject> edit)
{
    foreach (KeyValuePair<string, JsonNode?> target in document["targets"]!.AsObject())
        foreach (KeyValuePair<string, JsonNode?> item in target.Value!.AsObject())
            if (item.Key.StartsWith(Package + "/", StringComparison.Ordinal)) edit(item.Value!.AsObject());
}
JsonObject Copy(string path) => JsonNode.Parse(File.ReadAllText(path))!.AsObject();

// The host takes a library's whole best RID group: a linux-x64 group without Lib.dll
// hides both unix-x64 and the portable Lib.dll from that library.
JsonObject perLibraryDeps = Copy(deps), perLibraryAssets = Copy(assets);
foreach (JsonObject document in new[] { perLibraryDeps, perLibraryAssets })
    EachLibrary(document, library =>
    {
        JsonObject targets = library["runtimeTargets"]!.AsObject();
        JsonNode linux = targets["runtimes/linux-x64/lib/net10.0/" + Library + ".dll"]!.DeepClone();
        targets.Remove("runtimes/linux-x64/lib/net10.0/" + Library + ".dll");
        targets["runtimes/linux-x64/lib/net10.0/Companion.dll"] = linux;
    });
Rejected("per-library RID group", "no runtime implementation",
    Resolve("linux-x64", Write("group.deps.json", perLibraryDeps), Write("group.assets.json", perLibraryAssets)));

JsonObject wrongFramework = Copy(deps);
wrongFramework["runtimeTarget"]!["name"] = ".NETCoreApp,Version=v9.0";
Rejected("wrong TFM", "requires net10.0", Resolve("linux-x64", Write("wrong-framework.deps.json", wrongFramework)));

JsonObject traversalDeps = Copy(deps), traversalAssets = Copy(assets);
foreach (JsonObject document in new[] { traversalDeps, traversalAssets })
    EachLibrary(document, library =>
    {
        JsonObject targets = library["runtimeTargets"]!.AsObject();
        string path = "runtimes/linux-x64/lib/net10.0/" + Library + ".dll";
        JsonNode entry = targets[path]!.DeepClone();
        targets.Remove(path);
        targets["../../" + Library + ".dll"] = entry;
    });
Rejected("asset traversal", "Unsafe discovery asset path",
    Resolve("linux-x64", Write("traversal.deps.json", traversalDeps), Write("traversal.assets.json", traversalAssets)));

JsonObject conflictingAssets = Copy(assets);
EachLibrary(conflictingAssets, library => library["runtimeTargets"]!.AsObject().Remove("runtimes/linux-x64/lib/net10.0/" + Library + ".dll"));
Rejected("deps/assets disagreement", "Conflicting deps/NuGet runtime asset", Resolve("linux-x64", "", Write("conflict.assets.json", conflictingAssets)));

JsonObject referenceDeps = Copy(deps), referenceAssets = Copy(assets);
foreach (JsonObject document in new[] { referenceDeps, referenceAssets })
    EachLibrary(document, library => { library.Remove("runtime"); library.Remove("runtimeTargets"); });
Rejected("reference-only attribute", "Reference-only discovery located the interface",
    Resolve(null, Write("ref.deps.json", referenceDeps), Write("ref.assets.json", referenceAssets)));

byte[] deployed = File.ReadAllBytes(RidAsset("linux-x64"));
File.WriteAllBytes(RidAsset("linux-x64"), variants["unix"]);
Rejected("differing app-local and package copies", "Ambiguous discovery files", Resolve("linux-x64"));
File.WriteAllBytes(RidAsset("linux-x64"), deployed);

// SDK deps.json has no compile assets; the NuGet reference assembly must still be read.
byte[] Attributed(byte[] assembly, string? advertised)
{
    using ModuleDefinition metadata = ModuleDefinition.ReadModule(new MemoryStream(assembly));
    CustomAttribute attribute = metadata.Assembly.CustomAttributes.Single(item => item.AttributeType.FullName == "Nethermind.LeanCIL.LeanCilContractsAttribute");
    if (advertised is null) metadata.Assembly.CustomAttributes.Remove(attribute);
    else attribute.ConstructorArguments[0] = new CustomAttributeArgument(attribute.ConstructorArguments[0].Type, advertised);
    using MemoryStream bytes = new();
    metadata.Write(bytes);
    return bytes.ToArray();
}
string packagedReference = Path.Combine(packageRoot, "ref", "net10.0", Library + ".dll");
byte[] originalReference = File.ReadAllBytes(packagedReference);
File.WriteAllBytes(packagedReference, Attributed(originalReference, new string('0', 64)));
Rejected("reference/runtime digest disagreement", "Reference/runtime contract attribute mismatch", Resolve("linux-x64"));
File.WriteAllBytes(packagedReference, originalReference);
string packagedRuntime = Path.Combine(packageRoot, "runtimes", "linux-x64", "lib", "net10.0", Library + ".dll");
byte[] unadvertised = Attributed(variants["linux-x64"], null);
foreach (string path in new[] { RidAsset("linux-x64"), packagedRuntime }) File.WriteAllBytes(path, unadvertised);
(int Code, string Output, JsonElement? Result) referenceAdvertised = Resolve("linux-x64");
foreach (string path in new[] { RidAsset("linux-x64"), packagedRuntime }) File.WriteAllBytes(path, variants["linux-x64"]);
if (referenceAdvertised.Code != 0 || !Same(referenceAdvertised.Result!.Value.GetProperty("imports")[0].GetProperty("sidecar").GetString(), packagedSidecar))
    throw new InvalidOperationException("A digest advertised only by the reference assembly did not locate its sidecar: " + referenceAdvertised.Output);
Console.WriteLine("PASS resolver rejects missing RID or graph, cross-architecture and malformed graphs, and unsafe or ambiguous manifests");

// Certify the resolved linux-x64 import; the resolver output is locations, the pins come separately.
string selectedImplementation = Path.Combine(packageRoot, "runtimes", "linux-x64", "lib", "net10.0", Library + ".dll");
string artifact = Path.Combine(root, "ProducerArtifact");
Run([.. cli, "extract", selectedImplementation, "ImportFixture.Library::AddOne(ulong)", artifact]);
File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(new
{
    schema = 1, proof = producerProof, theorem = "LibProof.correctness", proofRoot = producerPackage
}));
string manifest = Path.Combine(root, "publish.json");
File.WriteAllText(manifest, JsonSerializer.Serialize(new
{
    schema = 1, assembly = selectedImplementation, proofRoot = producerPackage,
    @interface = new[] { new { module = "PublishedArithmetic", source = interfaceSource } },
    exports = new[] { new { method = "ImportFixture.Library::AddOne(ulong)", artifact,
        contract = "ImportFixture.addOne", theorem = "LibProof.correctness" } }
}));
Run([.. cli, "export-contracts", manifest, "--output", packagedSidecar]);
if (JsonNode.Parse(File.ReadAllText(packagedSidecar))!["interfaceDigest"]!.GetValue<string>() != digest)
    throw new InvalidOperationException("Republished producer changed its logical interface digest.");
string[] resolvedArguments = Selected("linux-x64", "linux-x64", RidAsset("linux-x64")).GetProperty("arguments")
    .EnumerateArray().Select(item => item.GetString()!).ToArray();
string[] Extract(string output, string hash) => [.. cli, "extract", application, Selector, output, .. resolvedArguments,
    "--import-sha256", Library + "=" + hash, "--import-interface-sha256", Library + "=" + digest];
string selectedOutput = Path.Combine(root, "Selected");
Run(Extract(selectedOutput, Hash(variants["linux-x64"])));
Run([.. cli, "verify", selectedOutput, "--proof", callerProof, "--proof-root", callerPackage]);
JsonElement import = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(selectedOutput, "verified.json"))).GetProperty("imports")[0];
JsonElement binding = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(selectedOutput, "identity.json"))).GetProperty("imports")[0];
if (import.GetProperty("implementationSha256").GetString() != Hash(variants["linux-x64"]) ||
    !Same(ExtractionIdentity.Resolve(selectedOutput, binding.GetProperty("implementationPath").GetString()!), RidAsset("linux-x64")) || import.GetProperty("interfaceDigest").GetString() != digest)
    throw new InvalidOperationException("Report did not name the resolved net10.0 linux-x64 implementation: " + import);
(int Code, string Output, string Stdout, string Stderr) wrongPin = Execute(Extract(Path.Combine(root, "WrongPin"), Hash(variants["linux-arm64"])));
if (wrongPin.Code != 1 || !wrongPin.Output.Contains("implementation SHA-256 mismatch", StringComparison.Ordinal) ||
    File.Exists(Path.Combine(root, "WrongPin", "Extracted.lean")))
    throw new InvalidOperationException("A resolved location was accepted without its independent pin: " + wrongPin.Output);
Console.WriteLine("PASS resolved locations certify only under the independent implementation and interface pins");

partial class Program
{
    static JsonElement MsBuildProperties(string project, params string[] names)
    {
        (int Code, string Output, string Stdout, string Stderr) result = Execute(["dotnet", "msbuild", project, "-p:Configuration=Release",
            .. names.Select(name => "-getProperty:" + name)]);
        if (result.Code != 0) throw new InvalidOperationException("MSBuild property query failed: " + result.Output);
        return JsonSerializer.Deserialize<JsonElement>(result.Stdout).GetProperty("Properties");
    }
}
