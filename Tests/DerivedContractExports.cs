#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// A library proves exact internal contracts against its actual extraction and exports weaker public
// contracts derived only by Holds.weaken; separately compiled callers verify from the sidecar alone.
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

string root = At("artifacts/DerivedContractExports-" + Guid.NewGuid().ToString("N"));
string libRoot = Path.Combine(root, "Lib");
string appRoot = Path.Combine(root, "App");
string package = Path.Combine(root, "Proofs");
string callerPackage = Path.Combine(root, "CallerProofs");
foreach (string directory in new[] { libRoot, appRoot, package, callerPackage }) Directory.CreateDirectory(directory);
string[] cli = ["dotnet", ExtractorPath];
string Project(string assembly, string references) =>
    "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>" +
    assembly + "</AssemblyName><Optimize>true</Optimize></PropertyGroup>" + references + "</Project>";
File.WriteAllText(Path.Combine(libRoot, "Lib.csproj"), Project("DerivedFixture.Lib", ""));
File.WriteAllText(Path.Combine(appRoot, "App.csproj"), Project("DerivedFixture.App",
    "<ItemGroup><ProjectReference Include=\"../Lib/Lib.csproj\" /></ItemGroup>"));
File.WriteAllText(Path.Combine(libRoot, "Library.cs"), """
using System;
namespace DerivedFixture;
public static class Library
{
    public static ulong Percent(ulong value) =>
        value <= 100 ? value : throw new ArgumentOutOfRangeException(nameof(value));
    public static void AddTo(in ulong left, in ulong right, out ulong sum) { sum = left + right; }
}
""");
File.WriteAllText(Path.Combine(appRoot, "Application.cs"), """
namespace DerivedFixture;
public static class Application
{
    public static ulong Shift(ulong value) => Library.Percent(value) + 1;
    public static void Sum(in ulong left, in ulong right, out ulong sum) => Library.AddTo(in left, in right, out sum);
}
""");
Run(["dotnet", "build", Path.Combine(appRoot, "App.csproj"), "-c", "Release"]);
string lib = Path.Combine(libRoot, "bin", "DerivedFixture.Lib.dll");
string app = Path.Combine(appRoot, "bin", "DerivedFixture.App.dll");
string sidecar = Path.Combine(libRoot, "bin", "DerivedFixture.Lib.leancil.contracts");

// The published module must not share a path with any source of the leancil package, this fixture's own included.
const string interfaceModule = "PublishedDerivedInterface";
string revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
void Package(string directory, string name, string[] modules)
{
    File.WriteAllText(Path.Combine(directory, "lakefile.toml"),
        "name = \"" + name + "\"\n[[require]]\nname = \"leancil\"\ngit = " +
        JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " + JsonSerializer.Serialize(revision) + "\n" +
        string.Join("", modules.Select(module => "[[lean_lib]]\nname = \"" + module + "\"\n")));
    File.Copy(At("lean-toolchain"), Path.Combine(directory, "lean-toolchain"));
    foreach (string module in modules)
        File.WriteAllText(Path.Combine(directory, module + ".lean"), File.ReadAllText(At("Tests/ContractImports/" +
            (module == interfaceModule ? "DerivedInterface" : module) + ".lean"))
            .Replace("import DerivedInterface\n", "import " + interfaceModule + "\n", StringComparison.Ordinal));
    Run(["lake", "update"], directory);
}
string[] producerModules = [interfaceModule, "DerivedPercentProof", "DerivedAddProof"];
string[] callerModules = ["DerivedShiftCaller", "DerivedSumCaller"];
Package(package, "derived-proofs", producerModules);
Package(callerPackage, "derived-callers", callerModules);
string interfaceSource = Path.Combine(package, interfaceModule + ".lean");

(string Method, string Artifact, string Contract, string Kind, string Proof, string Derivation)[] exports =
[
    ("DerivedFixture.Library::Percent(ulong)", Path.Combine(root, "Percent"), "DerivedInterface.percentBounded",
        "outcome", "DerivedPercentProof", "percent_exact.weaken percent_bounded_refines"),
    ("DerivedFixture.Library::AddTo(ulong&,ulong&,ulong&)", Path.Combine(root, "AddTo"), "DerivedInterface.addPublic",
        "method", "DerivedAddProof", "add_internal.weaken add_public_refines")
];
foreach ((string method, string artifact, string contract, _, string proof, string derivation) in exports)
{
    // The exported theorem is the consequence rule alone, so no execution reasoning is repeated for it.
    string exported = "theorem correctness : " + contract + ".Holds Extracted.program 0 :=\n  " + derivation + "\n";
    if (!File.ReadAllText(Path.Combine(package, proof + ".lean")).Contains(exported, StringComparison.Ordinal))
        throw new InvalidOperationException("Precondition: " + proof + " must export exactly " + derivation);
    Run([.. cli, "extract", lib, method, artifact]);
    File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(new
    {
        schema = 1, proof = Path.GetRelativePath(artifact, Path.Combine(package, proof + ".lean")).Replace('\\', '/'),
        theorem = proof + ".correctness", proofRoot = Path.GetRelativePath(artifact, package).Replace('\\', '/')
    }));
}
string Manifest(string name, string? onlyProof = null)
{
    string path = Path.Combine(root, name + ".json");
    File.WriteAllText(path, JsonSerializer.Serialize(new
    {
        schema = 1, assembly = lib, proofRoot = package,
        @interface = new[] { new { module = interfaceModule, source = interfaceSource } },
        exports = exports.Where(export => onlyProof is null || export.Proof == onlyProof).Select(export => new
        {
            method = export.Method, artifact = export.Artifact, contract = export.Contract,
            theorem = export.Proof + ".correctness"
        }).ToArray()
    }));
    return path;
}
Run([.. cli, "export-contracts", Manifest("export"), "--output", sidecar]);

// The exporter accepts each derived theorem as the exact canonical Holds statement of its public contract.
JsonObject published = JsonNode.Parse(File.ReadAllText(sidecar))!.AsObject();
string interfaceDigest = published["interfaceDigest"]!.GetValue<string>();
JsonArray certifications = published["certifications"]!.AsArray();
string Text(JsonNode? node, string field) => node![field]!.GetValue<string>();
foreach ((string method, _, string contract, string kind, _, _) in exports)
{
    string holds = kind == "outcome" ? "OutcomeContract.Holds" : "MethodContract.Holds";
    JsonNode export = published["exports"]!.AsArray().Single(entry => Text(entry, "contractConstant") == contract)!;
    JsonNode certification = certifications.Single(entry => Text(entry, "identity") == Text(export, "identity"))!;
    string statement = Text(certification, "statement");
    string expected = "LeanCILExportAudit.certified : CIL.Safety." + holds + " " + contract + " Extracted.program 0";
    if (Text(export, "kind") != kind || statement != expected ||
        Text(certification, "theorem") != "LeanCILExportAudit.certified")
        throw new InvalidOperationException("Derived export lost its kind or exact statement: " + method + ": " +
            statement);
}
if (published["exports"]!.AsArray().Count != 2 || certifications.Count != 2)
    throw new InvalidOperationException("Derived sidecar must certify exactly the two public exports.");

// The compact interface is the public module alone; internal contracts and their proofs never reach a consumer.
string[] internalNames =
    ["DerivedPercentProof", "DerivedAddProof", "percentExact", "addInternal", "addPre", "weaken", "Refines"];
JsonNode module = published["interfaceModules"]!.AsArray().Single()!;
string publishedSource = Text(module, "source");
string sidecarText = File.ReadAllText(sidecar);
if (Text(module, "name") != interfaceModule || publishedSource != File.ReadAllText(interfaceSource) ||
    internalNames.Any(name => sidecarText.Contains(name, StringComparison.Ordinal)))
    throw new InvalidOperationException("The published sidecar reached an internal contract or proof.");
Console.WriteLine("PASS exact internal contracts derive the published MethodContract and OutcomeContract theorems");

// An unrefined public contract fails only its refinement proof, so nothing is published. One renamed exception
// stands for all four kinds; each proof module's Rejected section refutes every kind on the actual extraction.
string certified = Sha(sidecar);
string publicText = File.ReadAllText(interfaceSource);
string renamed = publicText.Replace("else some \"System.ArgumentOutOfRangeException\"",
    "else some \"System.ArgumentException\"", StringComparison.Ordinal);
if (renamed == publicText)
    throw new InvalidOperationException("Precondition: the public contract must name its exception.");
File.WriteAllText(interfaceSource, renamed);
// Only the affected export is attempted, so the unchanged one is not verified again.
(int Code, string Output, string Stdout, string Stderr) rejected =
    Execute([.. cli, "export-contracts", Manifest("reject", "DerivedPercentProof"), "--output", sidecar]);
File.WriteAllText(interfaceSource, publicText);
// Null unless the output reports this theorem's axiom set exactly once.
string? Axioms(string theorem)
{
    MatchCollection reported = Regex.Matches(rejected.Output, @"'DerivedPercentProof\." + Regex.Escape(theorem) +
        @"' depends on axioms: \[([^\]]*)\]", RegexOptions.Singleline);
    return reported.Count == 1 ? reported[0].Groups[1].Value : null;
}
if (rejected.Code != 1 || Sha(sidecar) != certified ||
    Axioms("percent_exact") is not { } exact || exact.Contains("sorryAx", StringComparison.Ordinal) ||
    Axioms("percent_bounded_refines")?.Contains("sorryAx", StringComparison.Ordinal) != true)
    throw new InvalidOperationException("A renamed exception was published or failed outside its refinement: " +
        rejected.Output);
Console.WriteLine("PASS a public contract naming another exception cannot be derived or published");

// Separately compiled callers see only the sidecar's public interface and the selected DLL.
if (Directory.EnumerateFiles(callerPackage, "*.lean", SearchOption.TopDirectoryOnly)
    .Any(path => producerModules.Contains(Path.GetFileNameWithoutExtension(path), StringComparer.Ordinal)))
    throw new InvalidOperationException("Precondition: the caller package must not contain producer modules.");
foreach ((string selector, string proof) in new[]
{
    ("DerivedFixture.Application::Shift(ulong)", "DerivedShiftCaller"),
    ("DerivedFixture.Application::Sum(ulong&,ulong&,ulong&)", "DerivedSumCaller")
})
{
    string artifact = Path.Combine(root, "App-" + proof);
    Run([.. cli, "extract", app, selector, artifact, "--import", sidecar,
        "--import-implementation", "DerivedFixture.Lib=" + lib, "--import-sha256", "DerivedFixture.Lib=" + Sha(lib),
        "--import-interface-sha256", "DerivedFixture.Lib=" + interfaceDigest]);
    Run([.. cli, "verify", artifact, "--proof", Path.Combine(callerPackage, proof + ".lean"),
        "--theorem", proof + ".correctness", "--proof-root", callerPackage]);
    JsonElement report =
        JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "verified.json")));
    JsonElement imported = report.GetProperty("imports").EnumerateArray().Single();
    if (imported.GetProperty("acceptedVia").GetString() != "published-certification" ||
        imported.GetProperty("implementationSha256").GetString() != Sha(lib) ||
        imported.GetProperty("interfaceDigest").GetString() != interfaceDigest)
        throw new InvalidOperationException("Caller did not accept the derived public contract for the DLL: " + proof);
    Console.WriteLine("PASS " + proof + " verifies from the derived public contract and the selected DLL");
}
// Git marks pack files read-only, which makes recursive deletion fail on Windows.
EnumerationOptions ownFiles = new() { RecurseSubdirectories = true, AttributesToSkip = FileAttributes.ReparsePoint };
foreach (string file in Directory.EnumerateFiles(root, "*", ownFiles))
    File.SetAttributes(file, FileAttributes.Normal);
Directory.Delete(root, recursive: true);
