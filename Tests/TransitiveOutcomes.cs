#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;
using System.Text.Json.Nodes;

// Independently compose a named exceptional contract through three separately compiled forwarders.
var root = At("artifacts/TransitiveOutcomes-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
string[] cli = ["dotnet", ExtractorPath];
var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
string Project(string name, string? reference, string body)
{
    var directory = Path.Combine(root, name);
    Directory.CreateDirectory(directory);
    File.WriteAllText(Path.Combine(directory, name + ".csproj"),
        "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework>" +
        "<AssemblyName>OutcomeFixture." + name + "</AssemblyName><Optimize>true</Optimize></PropertyGroup>" +
        (reference is null ? "" : "<ItemGroup><ProjectReference Include=\"../" + reference + "/" + reference +
            ".csproj\" /></ItemGroup>") + "</Project>");
    File.WriteAllText(Path.Combine(directory, "Library.cs"),
        "namespace OutcomeFixture; public static class " + name + " { " + body + " }");
    return directory;
}
var bRoot = Project("B", null, "public static ulong Percent(ulong value) => value <= 100 ? value : " +
    "throw new System.ArgumentOutOfRangeException(nameof(value));");
var aRoot = Project("A", "B", "public static ulong Percent(ulong value) => B.Percent(value);");
var cRoot = Project("C", "A", "public static ulong Percent(ulong value) => A.Percent(value);");
var appRoot = Project("App", "C", "public static ulong Percent(ulong value) => C.Percent(value);");
Run(["dotnet", "build", Path.Combine(appRoot, "App.csproj"), "-c", "Release"]);
string Assembly(string directory, string name) => Path.Combine(directory, "bin", "OutcomeFixture." + name + ".dll");
var b = Assembly(bRoot, "B");
var a = Assembly(aRoot, "A");
var c = Assembly(cRoot, "C");
var app = Assembly(appRoot, "App");
string Package(string name, params string[] modules)
{
    var directory = Path.Combine(root, name);
    Directory.CreateDirectory(directory);
    File.Copy(At("lean-toolchain"), Path.Combine(directory, "lean-toolchain"));
    File.WriteAllText(Path.Combine(directory, "lakefile.toml"),
        "name = " + JsonSerializer.Serialize(name.ToLowerInvariant()) + "\n[[require]]\nname = \"leancil\"\ngit = " +
        JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " + JsonSerializer.Serialize(revision) +
        "\n" + string.Concat(modules.Select(module => "\n[[lean_lib]]\nname = " +
            JsonSerializer.Serialize(module) + "\n")));
    Run(["lake", "update"], directory);
    return directory;
}
var bPackage = Package("BProofPackage", "DerivedPercentProof", "PublishedOutcome");
var aPackage = Package("AProofPackage", "Forward", "PublishedForwardOutcome");
var cPackage = Package("CProofPackage", "Forward", "PublishedSecondForwardOutcome");
var appPackage = Package("AppProofPackage", "Forward");
var interfaceSource = Path.Combine(bPackage, "PublishedOutcome.lean");
File.Copy(At("Tests/ContractImports/DerivedInterface.lean"), interfaceSource);
File.WriteAllText(Path.Combine(bPackage, "DerivedPercentProof.lean"),
    File.ReadAllText(At("Tests/ContractImports/DerivedPercentProof.lean"))
        .Replace("import DerivedInterface", "import PublishedOutcome", StringComparison.Ordinal));
const string forwardProof = """
    import ExtractedImports
    import CIL.Safety.OutcomeContract
    /-! A separately compiled forwarder preserves both normal and named exceptional outcomes. -/
    namespace Forward
    open CIL.Safety
    /-- The selected callee's exact public outcome contract survives the forwarding call. -/
    theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
        (fun linked => DerivedInterface.percentBounded.Holds linked 0) := by
      intro linked links imported value memory formed
      have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
      have holds : DerivedInterface.percentBounded.Holds linked 1 := imported
      dsimp only [DerivedInterface.percentBounded]
      cases raised : DerivedInterface.percentRaises value with
      | some exception =>
        refine raises_of_run found (by rfl) (by rfl) ?_
        refine run_next_raises found Extracted.method0_instruction0 (by cil_checked_step []) ?_
        exact run_call_raises_of_contract holds value found Extracted.method0_instruction1
          (by cil_checked_step []) rfl (by rfl) formed raised
      | none =>
        refine invoke_exists_of_run found (by rfl) (by rfl) ?_
        refine run_next_exists _ found Extracted.method0_instruction0 (by cil_checked_step []) ?_
        refine run_call_of_outcome holds value found Extracted.method0_instruction1
          (by cil_checked_step []) rfl formed raised ?_
        rintro final values _ framed returns
        obtain ⟨output, rfl, result⟩ := returns
        refine run_return_exists found Extracted.method0_instruction2 (by cil_checked_step []) (by rfl) ?_
        exact ⟨framed, output, rfl, result⟩
    #print axioms correctness
    end Forward
    """;
File.WriteAllText(Path.Combine(aPackage, "Forward.lean"), forwardProof);
File.WriteAllText(Path.Combine(cPackage, "Forward.lean"), forwardProof);
File.WriteAllText(Path.Combine(appPackage, "Forward.lean"), forwardProof);
var forwardingInterface = Path.Combine(aPackage, "PublishedForwardOutcome.lean");
File.WriteAllText(forwardingInterface, "import PublishedOutcome\n");
var secondForwardingInterface = Path.Combine(cPackage, "PublishedSecondForwardOutcome.lean");
File.WriteAllText(secondForwardingInterface, "import PublishedForwardOutcome\n");
string[] Import(string sidecar, string assembly, string name)
{
    var descriptor = JsonNode.Parse(File.ReadAllText(sidecar))!;
    return ["--import", sidecar, "--import-implementation", name + "=" + assembly,
        "--import-sha256", name + "=" + Sha(assembly),
        "--import-interface-sha256", name + "=" + descriptor["interfaceDigest"]!.GetValue<string>()];
}
string Export(string name, string assembly, string package, string module, string source, string proof,
    string theorem, string[] imports)
{
    var artifact = Path.Combine(root, "Extract" + name);
    Run([.. cli, "extract", assembly, "OutcomeFixture." + name + "::Percent(ulong)", artifact, .. imports]);
    File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(new
    {
        schema = 1, proof = Path.GetRelativePath(artifact, Path.Combine(package, proof)), theorem,
        proofRoot = Path.GetRelativePath(artifact, package)
    }));
    var manifest = Path.Combine(root, name + "-exports.json");
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        schema = 1, assembly, proofRoot = package,
        @interface = new[] { new { module, source } },
        exports = new[] { new { method = "OutcomeFixture." + name + "::Percent(ulong)", artifact,
            contract = "DerivedInterface.percentBounded", theorem } }
    }));
    var sidecar = Path.Combine(root, "OutcomeFixture." + name + ".leancil.contracts");
    Run([.. cli, "export-contracts", manifest, "--output", sidecar, "--bundle", Path.Combine(root, "Bundles")]);
    return sidecar;
}
var bSidecar = Export("B", b, bPackage, "PublishedOutcome", interfaceSource, "DerivedPercentProof.lean",
    "DerivedPercentProof.correctness", []);
var aSidecar = Export("A", a, aPackage, "PublishedForwardOutcome", forwardingInterface, "Forward.lean",
    "Forward.correctness", Import(bSidecar, b, "OutcomeFixture.B"));
var cSidecar = Export("C", c, cPackage, "PublishedSecondForwardOutcome", secondForwardingInterface, "Forward.lean",
    "Forward.correctness", [.. Import(aSidecar, a, "OutcomeFixture.A"), .. Import(bSidecar, b, "OutcomeFixture.B")]);
var artifact = Path.Combine(root, "ExtractApp");
Run([.. cli, "extract", app, "OutcomeFixture.App::Percent(ulong)", artifact,
    .. Import(cSidecar, c, "OutcomeFixture.C"), .. Import(aSidecar, a, "OutcomeFixture.A"),
    .. Import(bSidecar, b, "OutcomeFixture.B")]);
Run([.. cli, "verify", artifact, "--proof", Path.Combine(appPackage, "Forward.lean"),
    "--theorem", "Forward.correctness", "--proof-root", appPackage, "--force-full-verify"]);
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "verified.json")));
if (report.GetProperty("contractDependencies").GetArrayLength() != 3 ||
    report.GetProperty("contractDependencies").EnumerateArray().Any(node =>
        node.GetProperty("acceptedVia").GetString() != "independently-verified") ||
    report.GetProperty("compositionTheorem").GetString() != "LeanCILFullComposition.certified")
    throw new InvalidOperationException("The named exceptional contract lost its independently checked dependency closure.");
Console.WriteLine("PASS App -> C -> A -> B preserves the normal bound and named ArgumentOutOfRangeException");
