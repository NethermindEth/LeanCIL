#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

using System.IO.Compression;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;

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

// The resource is descriptor-only and is present before the SDK finalizes the DLL.
// Certification remains an external fixture envelope over those final bytes.
Run([.. cli, "interface-descriptor", originalSidecar, Path.Combine(producer, "Interface.json")]);
File.WriteAllText(Path.Combine(producer, "Producer.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
<AssemblyName>ImportFixture.Lib</AssemblyName><Optimize>true</Optimize><ProduceReferenceAssembly>true</ProduceReferenceAssembly>
</PropertyGroup><ItemGroup><EmbeddedResource Include="Interface.json" LogicalName="LeanCIL.Contracts.Interface" /></ItemGroup></Project>
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
string implementation = Path.Combine(producer, "bin", Library + ".dll");
string reference = Path.Combine(producer, "obj", "Release", "net10.0", "ref", Library + ".dll");
using (ModuleDefinition metadata = ModuleDefinition.ReadModule(reference))
{
    if (!metadata.Assembly.CustomAttributes.Any(attribute => attribute.AttributeType.FullName == "Nethermind.LeanCIL.LeanCilContractsAttribute") ||
        metadata.Resources.Any(resource => resource.Name == "LeanCIL.Contracts.Interface"))
        throw new InvalidOperationException("Actual SDK reference emission did not retain only the discovery attribute.");
}

byte[] Variant(string marker)
{
    using ModuleDefinition metadata = ModuleDefinition.ReadModule(implementation);
    metadata.Resources.Add(new EmbeddedResource("Discovery.Variant", ManifestResourceAttributes.Private, Encoding.UTF8.GetBytes(marker)));
    using MemoryStream bytes = new();
    metadata.Write(bytes);
    return bytes.ToArray();
}
byte[] portable = Variant("portable-net10");
byte[] x64 = Variant("linux-x64-net10");
byte[] arm64 = Variant("linux-arm64-net10");
byte[] net9 = Variant("net9-decoy");
void Bind(JsonObject sidecar, byte[] bytes)
{
    using ModuleDefinition metadata = ModuleDefinition.ReadModule(new MemoryStream(bytes));
    string hash = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes));
    sidecar["implementationSha256"] = hash;
    sidecar["mvid"] = metadata.Mvid.ToString();
    foreach (JsonNode? certification in sidecar["certifications"]!.AsArray()) certification!["implementationSha256"] = hash;
}
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
    Entry("lib/net9.0/" + Library + ".dll", net9);
    Entry("lib/net10.0/" + Library + ".dll", portable);
    Entry("runtimes/linux-x64/lib/net10.0/" + Library + ".dll", x64);
    Entry("runtimes/linux-arm64/lib/net10.0/" + Library + ".dll", arm64);
    Entry("contracts/" + digest + ".leancil.contracts", Encoding.UTF8.GetBytes(contract.ToJsonString()));
}
File.WriteAllText(Path.Combine(consumer, "Consumer.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
<AssemblyName>ImportFixture.App</AssemblyName><Optimize>true</Optimize></PropertyGroup>
<ItemGroup><PackageReference Include="LeanCil.Discovery.Fixture" Version="1.0.0" /></ItemGroup></Project>
""");
File.WriteAllText(Path.Combine(consumer, "Application.cs"),
    "namespace ImportFixture; public static class Application { public static ulong Entry(ulong value) => Library.AddOne(value); public static ulong Identity(ulong value) => value; }");
Run(["dotnet", "restore", Path.Combine(consumer, "Consumer.csproj"), "--source", feed, "--packages", packages]);
Run(["dotnet", "build", Path.Combine(consumer, "Consumer.csproj"), "-c", "Release", "--no-restore"]);
string application = Path.Combine(consumer, "bin", "ImportFixture.App.dll");
string deps = Path.Combine(consumer, "bin", "ImportFixture.App.deps.json");
string assets = Path.Combine(consumer, "obj", "project.assets.json");
string packageRoot = Path.Combine(packages, Package.ToLowerInvariant(), "1.0.0");
string discoveredSidecar = Path.Combine(packageRoot, "contracts", digest + ".leancil.contracts");
int publication = 0;
void Publish(string dll)
{
    string artifact = Path.Combine(root, "ProducerArtifact" + publication++);
    Run([.. cli, "extract", dll, "ImportFixture.Library::AddOne(ulong)", artifact]);
    File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(new
    {
        schema = 1, proof = producerProof, theorem = "LibProof.correctness", proofRoot = producerPackage
    }));
    string manifest = Path.Combine(root, "publish.json");
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        schema = 1, assembly = dll, proofRoot = producerPackage,
        @interface = new[] { new { module = "PublishedArithmetic", source = interfaceSource } },
        exports = new[] { new { method = "ImportFixture.Library::AddOne(ulong)", artifact,
            contract = "ImportFixture.addOne", theorem = "LibProof.correctness" } }
    }));
    Run([.. cli, "export-contracts", manifest, "--output", discoveredSidecar]);
    contract = JsonNode.Parse(File.ReadAllText(discoveredSidecar))!.AsObject();
    if (contract["interfaceDigest"]!.GetValue<string>() != digest)
        throw new InvalidOperationException("Final resource-bearing producer changed its logical interface digest.");
}
Publish(Path.Combine(packageRoot, "runtimes", "linux-x64", "lib", "net10.0", Library + ".dll"));
// A portable SDK build copies its portable runtime locally. The package's selected
// RID asset is deliberately different; remove that unrelated deployment copy.
File.Delete(Path.Combine(consumer, "bin", Library + ".dll"));

// The same SDK deps contain multi-RID managed assets, but Identity needs no import.
// Merely having those unrelated assets must not make a local proof require a RID.
string localOutput = Path.Combine(root, "NoImports");
Run([.. cli, "extract", application, "ImportFixture.Application::Identity(ulong)", localOutput,
    "--import-deps", deps, "--import-assets", assets]);
string localProof = Path.Combine(root, "Identity.lean");
File.WriteAllText(localProof, """
import Extracted
import Examples.Support
namespace ExampleProof
theorem correctness (value : CIL.W64) :
    (CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i64 value)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i64 value)] := by rfl
#print axioms correctness
end ExampleProof
""");
Run([.. cli, "verify", localOutput, "--proof", localProof]);
JsonElement localIdentity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(localOutput, "identity.json")));
if (localIdentity.GetProperty("imports").GetArrayLength() != 0 || !File.Exists(Path.Combine(localOutput, "verified.json")))
    throw new InvalidOperationException("Local-method regression did not prove the no-import path.");

string Hash(byte[] bytes) => Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes));
string[] Command(string output, string? selectedRid, string depsFile, string assetsFile, string hash) =>
    [.. cli, "extract", application, Selector, output, "--import-deps", depsFile, "--import-assets", assetsFile,
        .. selectedRid is null ? Array.Empty<string>() : new[] { "--runtime-identifier", selectedRid },
        "--import-sha256", Library + "=" + hash, "--import-interface-sha256", Library + "=" + digest];
string selectedOutput = Path.Combine(root, "Selected");
Run(Command(selectedOutput, "linux-x64", deps, assets, Hash(x64)));
Run([.. cli, "verify", selectedOutput, "--proof", callerProof, "--proof-root", callerPackage]);
JsonElement report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(selectedOutput, "verified.json")));
JsonElement import = report.GetProperty("imports")[0];
if (import.GetProperty("implementationSha256").GetString() != Hash(x64) ||
    !import.GetProperty("implementationPath").GetString()!.Contains("runtimes/linux-x64/", StringComparison.Ordinal) ||
    import.GetProperty("discovery").GetProperty("runtimeIdentifier").GetString() != "linux-x64" ||
    import.GetProperty("discovery").GetProperty("carrier").GetString() != "embedded-and-sidecar" ||
    import.GetProperty("interfaceDigest").GetString() != digest)
    throw new InvalidOperationException("Report did not name the selected net10.0 x64 implementation and equal carrier digest.");
Console.WriteLine("PASS actual SDK deps/assets and reference metadata select net10.0/RID implementation in the success report");

string explicitOutput = Path.Combine(root, "ExplicitOverrideNoRid");
Run([.. Command(explicitOutput, null, deps, assets, Hash(x64)), "--import", discoveredSidecar,
    "--import-implementation", Library + "=" + Path.Combine(packageRoot, "runtimes", "linux-x64", "lib", "net10.0", Library + ".dll")]);
Run([.. cli, "verify", explicitOutput, "--proof", callerProof, "--proof-root", callerPackage]);
Console.WriteLine("PASS unrelated multi-RID assets do not block local methods or an explicit pinned implementation");

// Exercise provenance that exists only in importGraph, using the real extraction.
string graphOnly = Path.Combine(root, "GraphOnly");
Directory.CreateDirectory(graphOnly);
JsonObject graphIdentity = JsonNode.Parse(File.ReadAllText(Path.Combine(selectedOutput, "identity.json")))!.AsObject();
graphIdentity["imports"] = new JsonArray();
File.WriteAllText(Path.Combine(graphOnly, "identity.json"), graphIdentity.ToJsonString());
ContractDiscoveryInputs.ValidateOutput(graphOnly);
byte[] graphDeps = File.ReadAllBytes(deps);
try
{
    File.AppendAllText(deps, "\n");
    bool rejected = false;
    try { ContractDiscoveryInputs.ValidateOutput(graphOnly); }
    catch (InvalidDataException error) when (error.Message == "Stale contract discovery input: " + deps) { rejected = true; }
    if (!rejected) throw new InvalidOperationException("Graph-only discovery provenance did not reject the exact changed input.");
}
finally { File.WriteAllBytes(deps, graphDeps); }
RejectPostAuditDiscoveryMutation(application, selectedOutput, callerPackage, callerProof, deps);
Console.WriteLine("PASS graph-only provenance and post-audit mutation reject without publishing success");

void Reject(string name, string marker, string[] command)
{
    (int Code, string Output, string Stdout, string Stderr) result = Execute(command);
    string output = command[5];
    if (result.Code != 1 || !result.Output.Contains(marker, StringComparison.Ordinal) ||
        File.Exists(Path.Combine(output, "Extracted.lean")) || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException(name + " did not fail at the intended discovery guard: " + result.Output);
}
Reject("ambiguous architecture", "Runtime identifier is required", Command(Path.Combine(root, "NoRid"), null, deps, assets, Hash(x64)));
Reject("wrong runtime implementation pin", "implementation SHA-256 mismatch", Command(Path.Combine(root, "WrongPin"), "linux-arm64", deps, assets, Hash(x64)));
Reject("profile/RID mismatch", "Runtime identifier does not match the execution profile: linux-x64",
    [.. Command(Path.Combine(root, "WrongArchitecture"), "linux-x64", deps, assets, Hash(x64)), "arm64-armbase"]);

// Both fallback DLLs exist and differ. The declared order must select linux-x64
// before unix-x64, and then prefer that RID asset over the portable runtime.
string unixRuntime = Path.Combine(packageRoot, "runtimes", "unix-x64", "lib", "net10.0", Library + ".dll");
Directory.CreateDirectory(Path.GetDirectoryName(unixRuntime)!);
File.WriteAllBytes(unixRuntime, portable);
JsonObject fallbackDeps = JsonNode.Parse(File.ReadAllText(deps))!.AsObject();
JsonObject fallbackAssets = JsonNode.Parse(File.ReadAllText(assets))!.AsObject();
foreach (JsonObject document in new[] { fallbackDeps, fallbackAssets })
{
    document["runtimes"] = new JsonObject
    {
        ["linux-custom-x64"] = new JsonArray("linux-x64", "unix-x64"),
        ["linux-x64"] = new JsonArray(), ["unix-x64"] = new JsonArray()
    };
    foreach (KeyValuePair<string, JsonNode?> target in document["targets"]!.AsObject())
        foreach (KeyValuePair<string, JsonNode?> item in target.Value!.AsObject())
            if (item.Value!["runtimeTargets"] is JsonObject runtimeTargets)
                runtimeTargets["runtimes/unix-x64/lib/net10.0/" + Library + ".dll"] =
                    new JsonObject { ["rid"] = "unix-x64", ["assetType"] = "runtime" };
}
string fallbackDepsPath = Path.Combine(root, "fallback.deps.json");
string fallbackAssetsPath = Path.Combine(root, "fallback.assets.json");
File.WriteAllText(fallbackDepsPath, fallbackDeps.ToJsonString());
File.WriteAllText(fallbackAssetsPath, fallbackAssets.ToJsonString());
string fallbackOutput = Path.Combine(root, "Fallback");
Run(Command(fallbackOutput, "linux-custom-x64", fallbackDepsPath, fallbackAssetsPath, Hash(x64)));
Run([.. cli, "verify", fallbackOutput, "--proof", callerProof, "--proof-root", callerPackage]);
JsonElement fallbackIdentity = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(fallbackOutput, "identity.json")));
if (fallbackIdentity.GetProperty("imports")[0].GetProperty("implementationSha256").GetString() != Hash(x64) || Hash(x64) == Hash(portable))
    throw new InvalidOperationException("Declared RID fallback order did not select its independently pinned first implementation.");
foreach (JsonObject document in new[] { fallbackDeps, fallbackAssets })
    document["runtimes"]!["linux-custom-x64"] = new JsonArray("unix-x64", "linux-x64");
File.WriteAllText(fallbackDepsPath, fallbackDeps.ToJsonString());
File.WriteAllText(fallbackAssetsPath, fallbackAssets.ToJsonString());
Reject("RID fallback ranking", "implementation SHA-256 mismatch",
    Command(Path.Combine(root, "ReversedFallback"), "linux-custom-x64", fallbackDepsPath, fallbackAssetsPath, Hash(x64)));
Console.WriteLine("PASS declared RID fallback ranking and profile architecture reject incompatible selections");

string badDeps = Path.Combine(root, "wrong-framework.deps.json");
JsonObject wrongFramework = JsonNode.Parse(File.ReadAllText(deps))!.AsObject();
wrongFramework["runtimeTarget"]!["name"] = ".NETCoreApp,Version=v9.0";
File.WriteAllText(badDeps, wrongFramework.ToJsonString());
Reject("wrong TFM", "requires net10.0", Command(Path.Combine(root, "WrongTfm"), "linux-x64", badDeps, assets, Hash(x64)));

string badAssets = Path.Combine(root, "traversal.assets.json");
JsonObject traversal = JsonNode.Parse(File.ReadAllText(assets))!.AsObject();
foreach (KeyValuePair<string, JsonNode?> target in traversal["targets"]!.AsObject())
    foreach (KeyValuePair<string, JsonNode?> item in target.Value!.AsObject())
        if (item.Value!["runtimeTargets"] is JsonObject runtimeTargets)
            foreach (string path in runtimeTargets.Where(pair => pair.Value!["rid"]!.GetValue<string>() == "linux-x64").Select(pair => pair.Key).ToArray())
            {
                runtimeTargets["../../" + Library + ".dll"] = runtimeTargets[path]!.DeepClone();
                runtimeTargets.Remove(path);
            }
File.WriteAllText(badAssets, traversal.ToJsonString());
// Supply matching synthetic deps so containment, rather than manifest agreement,
// is the rejecting guard. The SDK originals remain untouched.
JsonObject traversalDeps = JsonNode.Parse(File.ReadAllText(deps))!.AsObject();
foreach (KeyValuePair<string, JsonNode?> target in traversalDeps["targets"]!.AsObject())
    foreach (KeyValuePair<string, JsonNode?> item in target.Value!.AsObject())
        if (item.Value!["runtimeTargets"] is JsonObject runtimeTargets)
            foreach (string path in runtimeTargets.Where(pair => pair.Value!["rid"]!.GetValue<string>() == "linux-x64").Select(pair => pair.Key).ToArray())
            {
                runtimeTargets["../../" + Library + ".dll"] = runtimeTargets[path]!.DeepClone();
                runtimeTargets.Remove(path);
            }
string traversalDepsPath = Path.Combine(root, "traversal.deps.json");
File.WriteAllText(traversalDepsPath, traversalDeps.ToJsonString());
Reject("asset traversal", "Unsafe discovery asset path", Command(Path.Combine(root, "Traversal"), "linux-x64", traversalDepsPath, badAssets, Hash(x64)));

string runtimePath = Path.Combine(packageRoot, "runtimes", "linux-x64", "lib", "net10.0", Library + ".dll");
using (ModuleDefinition metadata = ModuleDefinition.ReadModule(new MemoryStream(x64)))
{
    Resource resource = metadata.Resources.Single(item => item.Name == "LeanCIL.Contracts.Interface");
    metadata.Resources.Remove(resource);
    metadata.Resources.Add(new EmbeddedResource("LeanCIL.Contracts.Interface", ManifestResourceAttributes.Private, Encoding.UTF8.GetBytes("{}")));
    using MemoryStream bytes = new();
    metadata.Write(bytes);
    byte[] malformed = bytes.ToArray();
    File.WriteAllBytes(runtimePath, malformed);
    JsonObject malformedContract = contract.DeepClone().AsObject();
    Bind(malformedContract, malformed);
    File.WriteAllText(discoveredSidecar, malformedContract.ToJsonString());
    Reject("embedded descriptor mismatch", "Embedded contract descriptor fields", Command(Path.Combine(root, "BadResource"), "linux-x64", deps, assets, Hash(malformed)));
}
File.WriteAllBytes(runtimePath, x64);
File.WriteAllText(discoveredSidecar, contract.ToJsonString());

byte[] originalDeps = File.ReadAllBytes(deps);
File.AppendAllText(deps, "\n");
(int Code, string Output, string Stdout, string Stderr) stale = Execute([.. cli, "check", selectedOutput]);
if (stale.Code != 1 || !stale.Output.Contains("Stale contract discovery input", StringComparison.Ordinal))
    throw new InvalidOperationException("Changed discovery manifest passed extraction recheck: " + stale.Output);
(int Code, string Output, string Stdout, string Stderr) staleVerification = Execute([.. cli, "verify", selectedOutput,
    "--proof", callerProof, "--proof-root", callerPackage]);
if (staleVerification.Code != 1 || !staleVerification.Output.Contains("Stale contract discovery input", StringComparison.Ordinal) ||
    File.Exists(Path.Combine(selectedOutput, "verified.json")))
    throw new InvalidOperationException("Stale discovery inputs retained or published success: " + staleVerification.Output);
File.WriteAllBytes(deps, originalDeps);
Run([.. cli, "check", selectedOutput]);

JsonObject portableDeps = JsonNode.Parse(File.ReadAllText(deps))!.AsObject();
JsonObject portableAssets = JsonNode.Parse(File.ReadAllText(assets))!.AsObject();
void RemoveRuntimeTargets(JsonObject document)
{
    foreach (KeyValuePair<string, JsonNode?> target in document["targets"]!.AsObject())
        foreach (KeyValuePair<string, JsonNode?> item in target.Value!.AsObject()) item.Value!.AsObject().Remove("runtimeTargets");
}
RemoveRuntimeTargets(portableDeps);
RemoveRuntimeTargets(portableAssets);
// Add an unrelated managed multi-RID library to both SDK-derived manifests.
// The real requested package still has a valid automatic portable implementation.
foreach (JsonObject document in new[] { portableDeps, portableAssets })
{
    document["libraries"]!["Unrelated.Runtime/1.0.0"] = new JsonObject
    {
        ["type"] = "package", ["path"] = "unrelated.runtime/1.0.0"
    };
    foreach (KeyValuePair<string, JsonNode?> target in document["targets"]!.AsObject())
        target.Value!["Unrelated.Runtime/1.0.0"] = new JsonObject
        {
            ["runtimeTargets"] = new JsonObject
            {
                ["runtimes/linux-x64/lib/net10.0/Unrelated.dll"] = new JsonObject { ["rid"] = "linux-x64", ["assetType"] = "runtime" },
                ["runtimes/linux-arm64/lib/net10.0/Unrelated.dll"] = new JsonObject { ["rid"] = "linux-arm64", ["assetType"] = "runtime" }
            }
        };
}
string portableDepsPath = Path.Combine(root, "portable.deps.json");
string portableAssetsPath = Path.Combine(root, "portable.assets.json");
File.WriteAllText(portableDepsPath, portableDeps.ToJsonString());
File.WriteAllText(portableAssetsPath, portableAssets.ToJsonString());
Publish(Path.Combine(packageRoot, "lib", "net10.0", Library + ".dll"));
string portableOutput = Path.Combine(root, "Portable");
Run(Command(portableOutput, null, portableDepsPath, portableAssetsPath, Hash(portable)));
Run([.. cli, "verify", portableOutput, "--proof", callerProof, "--proof-root", callerPackage]);
Console.WriteLine("PASS automatic portable import ignores unrelated multi-RID assets and stale manifests reject");

// Keep the actual SDK compile/ref entries; remove runtime selections only.
foreach (JsonObject document in new[] { portableDeps, portableAssets })
    foreach (KeyValuePair<string, JsonNode?> target in document["targets"]!.AsObject())
        foreach (KeyValuePair<string, JsonNode?> item in target.Value!.AsObject()) item.Value!.AsObject().Remove("runtime");
File.WriteAllText(portableDepsPath, portableDeps.ToJsonString());
File.WriteAllText(portableAssetsPath, portableAssets.ToJsonString());
Reject("reference-only attribute", "Reference-only discovery located the interface", Command(Path.Combine(root, "RefOnly"), null,
    portableDepsPath, portableAssetsPath, Hash(portable)));
Console.WriteLine("PASS SDK reference attribute locates interface without certifying a runtime implementation");

partial class Program
{
    static void RejectPostAuditDiscoveryMutation(string assembly, string output, string package, string proof, string manifest)
    {
        byte[] original = File.ReadAllBytes(manifest);
        bool callbackRan = false;
        using Program verification = new() { freshLibrary = true };
        ConsumerExportAudit audit = new("", (_, _, _) =>
        {
            File.AppendAllText(manifest, "\n");
            callbackRan = true;
        });
        try
        {
            ConsumerRequest request = new(assembly, output, proof, "ExampleProof.correctness", null, ExportAudit: audit);
            ConsumerOutcome outcome = verification.VerifyConsumerRequests(package, [request], null, batch: false)[0];
            string expected = "Stale contract discovery input: " + manifest;
            if (!callbackRan || outcome.Report is not null || outcome.Error?.Message.Contains(expected, StringComparison.Ordinal) != true ||
                File.Exists(Path.Combine(output, "verified.json")))
                throw new InvalidOperationException("Post-audit discovery mutation did not reject the exact input without a report: " + outcome.Error);
        }
        finally { File.WriteAllBytes(manifest, original); }
    }
}
