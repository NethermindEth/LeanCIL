#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;
using System.Text.Json.Nodes;

var root = At("artifacts/InitializedExports-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
string[] cli = ["dotnet", ExtractorPath];
var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
string Project(string name, string? reference, string source)
{
    var directory = Path.Combine(root, name);
    Directory.CreateDirectory(directory);
    File.WriteAllText(Path.Combine(directory, name + ".csproj"),
        "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework>" +
        "<AssemblyName>InitializationFixture." + name + "</AssemblyName><Optimize>true</Optimize></PropertyGroup>" +
        (reference is null ? "" : "<ItemGroup><ProjectReference Include=\"../" + reference + "/" + reference +
            ".csproj\" /></ItemGroup>") + "</Project>");
    File.WriteAllText(Path.Combine(directory, name + ".cs"), source);
    return directory;
}
var library = Project("Lib", null, """
namespace InitializationFixture;
public struct Word
{
    public ulong Value;
    public static readonly Word One;
    static Word() { One = new Word { Value = 1 }; }
    public static ulong AddOne(ulong value) => value + 1;
}
""");
var app = Project("App", "Lib", """
namespace InitializationFixture;
public static class Application { public static ulong Entry(ulong value) => Word.AddOne(value); }
""");
Run(["dotnet", "build", Path.Combine(app, "App.csproj"), "-c", "Release"]);
var dll = Path.Combine(library, "bin/InitializationFixture.Lib.dll");
var appDll = Path.Combine(app, "bin/InitializationFixture.App.dll");
string Package(string name, params string[] modules)
{
    var directory = Path.Combine(root, name);
    Directory.CreateDirectory(directory);
    File.Copy(At("lean-toolchain"), Path.Combine(directory, "lean-toolchain"));
    File.WriteAllText(Path.Combine(directory, "lakefile.toml"), "name = \"" + name.ToLowerInvariant() + "\"\n" +
        "[[require]]\nname = \"leancil\"\ngit = " + JsonSerializer.Serialize(Root.Replace('\\', '/')) +
        "\nrev = \"" + revision + "\"\n" +
        string.Join("", modules.Select(module => "[[lean_lib]]\nname = \"" + module + "\"\n")));
    return directory;
}
var producer = Package("Producer", "PublishedArithmetic", "LibraryProof");
var consumer = Package("Consumer", "CallerProof");
File.Copy(At("Tests/ContractImports/ImportFixture.lean"), Path.Combine(producer, "PublishedArithmetic.lean"));
File.WriteAllText(Path.Combine(producer, "LibraryProof.lean"), """
import Extracted
import PublishedArithmetic
import CIL.Safety.SymbolicExecution
/-! Arithmetic under the extraction's explicitly recorded runtime initialization premise. -/
namespace LibraryProof
open CIL.Safety
/-- The selected arithmetic body returns the next word. -/
theorem correctness : MethodContract.Holds ImportFixture.addOne Extracted.program 0 := by
  rintro value memory formed
  dsimp only [ImportFixture.addOne, MethodContract.Returns]
  refine ⟨12, memory, [.scalar (.i64 (value + 1))], ?execution,
    Confined.refl _ memory, value + 1, rfl, ?post⟩
  case post => simp only [CIL.importedPost]
  case execution =>
    cil_checked_steps
    all_goals bv_omega
#print axioms correctness
end LibraryProof
""");
File.WriteAllText(Path.Combine(consumer, "CallerProof.lean"),
    File.ReadAllText(At("Tests/TransitiveImports/Conditional.lean")) + "\n#print axioms ExampleProof.correctness\n");
Run(["lake", "update"], producer);
Run(["lake", "update"], consumer);
var artifact = Path.Combine(root, "LibraryArtifact");
const string method = "InitializationFixture.Word::AddOne(ulong)";
var blocked = Execute([.. cli, "extract", dll, method, artifact]);
if (blocked.Code != 1 || !blocked.Output.Contains("static initialisation", StringComparison.Ordinal))
    throw new InvalidOperationException("Unacknowledged type initialization was accepted: " + blocked.Output);
Run([.. cli, "extract", dll, method, artifact, "--assume-initialized", "InitializationFixture.Word"]);
File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(new
{
    schema = 1, proof = Path.GetRelativePath(artifact, Path.Combine(producer, "LibraryProof.lean")),
    theorem = "LibraryProof.correctness", proofRoot = Path.GetRelativePath(artifact, producer)
}));
var manifest = Path.Combine(root, "export.json");
File.WriteAllText(manifest, JsonSerializer.Serialize(new
{
    schema = 1, assembly = dll, proofRoot = producer,
    @interface = new[] { new { module = "PublishedArithmetic",
        source = Path.Combine(producer, "PublishedArithmetic.lean") } },
    exports = new[] { new { method, artifact, contract = "ImportFixture.addOne",
        theorem = "LibraryProof.correctness" } }
}));
var sidecar = Path.Combine(root, "InitializationFixture.Lib.leancil.contracts");
var libraryProof = Path.Combine(producer, "LibraryProof.lean");
var honestProof = File.ReadAllText(libraryProof);
File.AppendAllText(libraryProof, """

macro_rules
  | `(_root_.Extracted.initializationAssumptions = $_types:term) => do
      dbg_trace "Attempted to erase the initialization premise audit"
      `(True = True)
""");
var forgeryTrace = Path.Combine(root, "trace-forged-initialization");
var priorTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", forgeryTrace);
var forged = Execute([.. cli, "export-contracts", manifest, "--output", sidecar]);
Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", priorTrace);
File.WriteAllText(libraryProof, honestProof);
var attemptedForgery = Directory.EnumerateFiles(forgeryTrace, "*.log", SearchOption.AllDirectories)
    .Any(path => File.ReadAllText(path).Contains("Attempted to erase the initialization premise audit",
        StringComparison.Ordinal));
if (forged.Code != 1 || !attemptedForgery ||
    !forged.Output.Contains(
        "Theorem statement mismatch: LeanCILExportAudit.initializationAssumptions", StringComparison.Ordinal) ||
    File.Exists(sidecar))
    throw new InvalidOperationException("A forged initialization-list theorem was accepted: " + forged.Output);
Run([.. cli, "export-contracts", manifest, "--output", sidecar, "--bundle", Path.Combine(root, "Bundles")]);
var original = File.ReadAllText(sidecar);
var published = JsonNode.Parse(original)!.AsObject();
var expectedAssembly = published["assemblyIdentity"]!.GetValue<string>();
var types = published["exports"]![0]!["initializationAssumptions"]![0]!["types"]!.AsArray();
if (types.Count != 1 || types[0]!["assemblyIdentity"]!.GetValue<string>() != expectedAssembly ||
    types[0]!["typeName"]!.GetValue<string>() != "InitializationFixture.Word")
    throw new InvalidOperationException("The published initialization premise lost its assembly or type identity.");
string[] Extract(string output) => [.. cli, "extract", appDll,
    "InitializationFixture.Application::Entry(ulong)", output,
    "--import", sidecar, "--import-implementation", "InitializationFixture.Lib=" + dll,
    "--import-sha256", "InitializationFixture.Lib=" + Sha(dll), "--import-interface-sha256",
    "InitializationFixture.Lib=" + JsonNode.Parse(File.ReadAllText(sidecar))!["interfaceDigest"]!.GetValue<string>()];
var caller = Path.Combine(root, "CallerArtifact");
Run(Extract(caller));
Run([.. cli, "verify", caller, "--proof", Path.Combine(consumer, "CallerProof.lean"), "--proof-root", consumer]);
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(caller, "verified.json")));
var inherited = report.GetProperty("initializationAssumptions").EnumerateArray().Single();
if (inherited.GetProperty("assemblyIdentity").GetString() != expectedAssembly ||
    inherited.GetProperty("typeName").GetString() != "InitializationFixture.Word" ||
    report.GetProperty("imports")[0].GetProperty("initializationAssumptions").GetArrayLength() != 1 ||
    !File.ReadAllText(Path.Combine(caller, "Extracted.lean")).Contains("def Extracted.initializationAssumptions"))
    throw new InvalidOperationException("The caller certificate dropped the imported initialization premise.");
Console.WriteLine("PASS a static-readonly struct library exports and its caller retains " +
    "the scoped initialization premise");
var forwardingInterface = Path.Combine(consumer, "PublishedForward.lean");
File.WriteAllText(forwardingInterface, "import PublishedArithmetic\n");
File.AppendAllText(Path.Combine(consumer, "lakefile.toml"), "\n[[lean_lib]]\nname = \"PublishedForward\"\n");
File.WriteAllText(Path.Combine(caller, "verification.json"), JsonSerializer.Serialize(new
{
    schema = 1, proof = Path.GetRelativePath(caller, Path.Combine(consumer, "CallerProof.lean")),
    theorem = "ExampleProof.correctness", proofRoot = Path.GetRelativePath(caller, consumer)
}));
var forwardingManifest = Path.Combine(root, "forward.json");
File.WriteAllText(forwardingManifest, JsonSerializer.Serialize(new
{
    schema = 1, assembly = appDll, proofRoot = consumer,
    @interface = new[] { new { module = "PublishedForward", source = forwardingInterface } },
    exports = new[] { new { method = "InitializationFixture.Application::Entry(ulong)", artifact = caller,
        contract = "ImportFixture.addOne", theorem = "ExampleProof.correctness" } }
}));
var forwardingSidecar = Path.Combine(root, "InitializationFixture.App.leancil.contracts");
Run([.. cli, "export-contracts", forwardingManifest, "--output", forwardingSidecar]);
var forwardingContract = JsonNode.Parse(File.ReadAllText(forwardingSidecar))!;
var forwarded = forwardingContract["exports"]![0]!["initializationAssumptions"]![0]!["types"]!;
if (!JsonNode.DeepEquals(types, forwarded))
    throw new InvalidOperationException("Re-exporting the caller changed its dependency's initialization premise.");
Console.WriteLine("PASS conditional re-export retains the dependency's exact scoped initialization premise");
var top = Project("Top", "App", """
namespace InitializationFixture;
public static class Top { public static ulong Entry(ulong value) => Application.Entry(value); }
""");
Run(["dotnet", "build", Path.Combine(top, "Top.csproj"), "-c", "Release", "-p:BuildProjectReferences=false"]);
string[] ExtractTop(string output)
{
    var contract = JsonNode.Parse(File.ReadAllText(forwardingSidecar))!.AsObject();
    return [.. cli, "extract", Path.Combine(top, "bin/InitializationFixture.Top.dll"),
        "InitializationFixture.Top::Entry(ulong)", output,
        "--import", forwardingSidecar, "--import-implementation", "InitializationFixture.App=" + appDll,
        "--import-sha256", "InitializationFixture.App=" + Sha(appDll), "--import-interface-sha256",
        "InitializationFixture.App=" + contract["interfaceDigest"]!.GetValue<string>(), .. Extract(output)[6..]];
}
var topArtifact = Path.Combine(root, "TopArtifact");
Run(ExtractTop(topArtifact));
var topIdentity = JsonNode.Parse(File.ReadAllText(Path.Combine(topArtifact, "identity.json")))!;
if (!JsonNode.DeepEquals(types, topIdentity["initializationAssumptions"]))
    throw new InvalidOperationException("The transitive caller changed its dependency's initialization premise.");
var originalForwarding = File.ReadAllText(forwardingSidecar);
var weakenedForwarding = JsonNode.Parse(originalForwarding)!.AsObject();
weakenedForwarding["exports"]![0]!["initializationAssumptions"]![0]!["types"] = new JsonArray();
Resign(weakenedForwarding);
File.WriteAllText(forwardingSidecar, weakenedForwarding.ToJsonString());
try
{
    var output = Path.Combine(root, "RejectedTransitive");
    var weakened = Execute(ExtractTop(output));
    if (weakened.Code != 1 || !weakened.Output.Contains(
            "initialization assumptions differ from its dependencies", StringComparison.Ordinal) ||
        File.Exists(Path.Combine(output, "identity.json")))
        throw new InvalidOperationException("A forwarding export erased its dependency premise: " + weakened.Output);
}
finally { File.WriteAllText(forwardingSidecar, originalForwarding); }
var full = Execute([.. cli, "verify", caller, "--proof", Path.Combine(consumer, "CallerProof.lean"),
    "--proof-root", consumer, "--force-full-verify"]);
if (full.Code != 1 || !full.Output.Contains("initialization assumptions", StringComparison.Ordinal) ||
    File.Exists(Path.Combine(caller, "verified.json")))
    throw new InvalidOperationException("Full mode accepted a runtime initialization premise: " + full.Output);
void Resign(JsonObject changed)
{
    var descriptor = new JsonObject();
    foreach (var field in new[] { "schema", "semanticsVersion", "formatVersion", "frameworkKey", "assemblyIdentity",
        "targetFramework", "interfaceModules", "exports", "dependencies" })
        descriptor[field] = changed[field]!.DeepClone();
    changed["interfaceDigest"] = ContentKey(descriptor.ToJsonString());
    foreach (var certification in changed["certifications"]!.AsArray())
        certification!["interfaceDigest"] = changed["interfaceDigest"]!.DeepClone();
}
void Reject(Action<JsonObject> mutate, string marker)
{
    var changed = JsonNode.Parse(original)!.AsObject();
    mutate(changed);
    Resign(changed);
    File.WriteAllText(sidecar, changed.ToJsonString());
    try
    {
        var output = Path.Combine(root, "Rejected-" + Guid.NewGuid().ToString("N"));
        var rejected = Execute(Extract(output));
        if (rejected.Code != 1 || !rejected.Output.Contains(marker, StringComparison.Ordinal) ||
            File.Exists(Path.Combine(output, "identity.json")))
            throw new InvalidOperationException("Invalid initialization descriptor accepted: " + rejected.Output);
    }
    finally { File.WriteAllText(sidecar, original); }
}
Reject(value => value["exports"]![0]!.AsObject().Remove("initializationAssumptions"), "static initialisation");
Reject(value => value["exports"]![0]!["initializationAssumptions"]![0]!["types"]![0]!["typeName"] =
    "InitializationFixture.Missing", "type with a static constructor");
Reject(value => value["exports"]![0]!["initializationAssumptions"]![0]!["types"]![0]!["assemblyIdentity"] =
    "Other, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null", "static initialisation");
Reject(value => value["exports"]![0]!["initializationAssumptions"]![0]!["profile"] = "x64-v3",
    "each exact exported profile");
Console.WriteLine("PASS omitted, wrong-type, wrong-assembly and wrong-profile premises reject; " +
    "full mode remains closed");
