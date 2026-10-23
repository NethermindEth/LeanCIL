#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

using System.Text.Json;
using System.Text.Json.Nodes;

string[] cli = ["dotnet", ExtractorPath];
string root = At("artifacts/ContractExport-" + Guid.NewGuid().ToString("N"));
string libraryRoot = Path.Combine(root, "Lib");
string appRoot = Path.Combine(root, "App");
string package = Path.Combine(root, "Package");
string callerPackage = Path.Combine(root, "CallerPackage");
string artifact = Path.Combine(root, "ExportArtifact");
string secondArtifact = Path.Combine(root, "SecondExportArtifact");
string callerArtifact = Path.Combine(root, "CallerArtifact");
string bundle = Path.Combine(root, "Bundles");
string manifestPath = Path.Combine(root, "export.json");
Directory.CreateDirectory(libraryRoot);
Directory.CreateDirectory(appRoot);
Directory.CreateDirectory(package);
Directory.CreateDirectory(callerPackage);
File.WriteAllText(Path.Combine(libraryRoot, "Lib.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>ImportFixture.Lib</AssemblyName><Optimize>true</Optimize></PropertyGroup></Project>
""");
File.WriteAllText(Path.Combine(appRoot, "App.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>ImportFixture.App</AssemblyName><Optimize>true</Optimize></PropertyGroup><ItemGroup><ProjectReference Include="../Lib/Lib.csproj" /></ItemGroup></Project>
""");
string librarySource = Path.Combine(libraryRoot, "Library.cs");
File.WriteAllText(librarySource, "namespace ImportFixture; public static class Library { public static ulong AddOne(ulong value) => value + 1; public static ulong AddSame(ulong value) => value + 1; " +
    "internal static ulong Hidden(ulong value) => value + 1; } public struct Value { public ulong Field; public ulong Add(ulong value) => value + Field; } " +
    "public static class Seeded { public static readonly ulong Seed = (ulong)System.Environment.ProcessorCount; }\n");
File.WriteAllText(Path.Combine(appRoot, "Application.cs"), "namespace ImportFixture; public static class Application { public static ulong Entry(ulong value) => Library.AddOne(value); }\n");
Run(["dotnet", "build", Path.Combine(appRoot, "App.csproj"), "-c", "Release"]);
string library = Path.Combine(libraryRoot, "bin", "ImportFixture.Lib.dll");
string app = Path.Combine(appRoot, "bin", "ImportFixture.App.dll");
string sidecar = Path.Combine(libraryRoot, "bin", "ImportFixture.Lib.leancil.contracts");
string revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"),
    "name = \"producer\"\n[[require]]\nname = \"leancil\"\ngit = " + JsonSerializer.Serialize(Root.Replace('\\', '/')) +
    "\nrev = \"" + revision + "\"\n[[lean_lib]]\nname = \"PublishedArithmetic\"\n[[lean_lib]]\nname = \"LibProof\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
string contractSource = Path.Combine(package, "PublishedArithmetic.lean");
File.Copy(At("Tests/ContractImports/ImportFixture.lean"), contractSource);
string proof = Path.Combine(package, "LibProof.lean");
File.WriteAllText(proof, """
import Extracted
import PublishedArithmetic
import CIL.Safety.SymbolicExecution

namespace LibProof
open CIL.Safety
theorem correctness : CIL.Safety.MethodContract.Holds ImportFixture.addOne Extracted.program 0 := by
  rintro value memory formed
  dsimp only [ImportFixture.addOne, MethodContract.Returns]
  have subtractMax : value - 18446744073709551615#64 = value + 1 := by
    rw [BitVec.sub_eq_add_neg]
    rfl
  refine ⟨12, memory, [.scalar (.i64 (value + 1))], ?execution,
    Confined.refl _ memory, value + 1, rfl, ?post⟩
  case post => simp only [CIL.importedPost]
  case execution =>
    cil_checked_steps [subtractMax]
    all_goals bv_omega
theorem unrelated : True := True.intro
def proofDefinition : CIL.Safety.MethodContract.Holds ImportFixture.addOne Extracted.program 0 := correctness
end LibProof
""");
Run(["lake", "update"], package);
File.WriteAllText(Path.Combine(callerPackage, "lakefile.toml"),
    "name = \"consumer\"\n[[require]]\nname = \"leancil\"\ngit = " + JsonSerializer.Serialize(Root.Replace('\\', '/')) +
    "\nrev = \"" + revision + "\"\n[[lean_lib]]\nname = \"Caller\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(callerPackage, "lean-toolchain"));
string callerProof = Path.Combine(callerPackage, "Caller.lean");
File.Copy(At("Tests/ContractImports/Caller.lean"), callerProof);
Run(["lake", "update"], callerPackage);

void ExtractLibrary()
{
    Run([.. cli, "extract", library, "ImportFixture.Library::AddOne(ulong)", artifact]);
    File.WriteAllText(Path.Combine(artifact, "verification.json"), JsonSerializer.Serialize(new
    {
        schema = 1, proof = Path.GetRelativePath(artifact, proof).Replace('\\', '/'), theorem = "LibProof.correctness",
        proofRoot = Path.GetRelativePath(artifact, package).Replace('\\', '/')
    }));
}

JsonObject ProducerManifest(string theorem = "LibProof.correctness") => JsonSerializer.SerializeToNode(new
{
    schema = 1, assembly = library, proofRoot = package,
    @interface = new[] { new { module = "PublishedArithmetic", source = contractSource } },
    exports = new[] { new { method = "ImportFixture.Library::AddOne(ulong)", artifact, contract = "ImportFixture.addOne", theorem } }
})!.AsObject();

void Export(JsonObject manifest)
{
    File.WriteAllText(manifestPath, manifest.ToJsonString());
    Run([.. cli, "export-contracts", manifestPath, "--output", sidecar, "--bundle", bundle]);
}

void RejectExport(JsonObject manifest, string marker, string? previous)
{
    File.WriteAllText(manifestPath, manifest.ToJsonString());
    (int Code, string Output, string Stdout, string Stderr) result = Execute([.. cli, "export-contracts", manifestPath, "--output", sidecar]);
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal) ||
        (previous is null ? File.Exists(sidecar) : !File.Exists(sidecar) || Sha(sidecar) != previous))
        throw new InvalidOperationException("Failed export changed/published a sidecar: " + result.Output);
}

ExtractLibrary();
RejectExport(ProducerManifest("LibProof.unrelated"), "exact canonical Holds statement", null);
RejectExport(ProducerManifest("LibProof.proofDefinition"), "Expected an export theorem", null);
Export(ProducerManifest());
JsonObject first = JsonNode.Parse(File.ReadAllText(sidecar))!.AsObject();
string interfaceDigest = first["interfaceDigest"]!.GetValue<string>();
string closureDigest = first["exports"]![0]!["closureDigest"]!.GetValue<string>();
string implementation = Sha(library);
string firstSidecar = Sha(sidecar);
if (first["implementationSha256"]!.GetValue<string>() != implementation || first["certifications"]!.AsArray().Count != 1 ||
    first["exports"]![0]!["kind"]!.GetValue<string>() != "method" ||
    first["certifications"]![0]!["theorem"]!.GetValue<string>() != "LeanCILExportAudit.certified" ||
    string.IsNullOrWhiteSpace(first["certifications"]![0]!["statement"]!.GetValue<string>()) ||
    !System.Text.RegularExpressions.Regex.IsMatch(first["certifications"]![0]!["statementDigest"]!.GetValue<string>(), @"\A[0-9a-f]{64}\z"))
    throw new InvalidOperationException("Export did not bind the actual implementation and complete certification.");
string publishedBundle = first["fullVerificationLocator"]!.GetValue<string>();
JsonObject inventory = JsonNode.Parse(File.ReadAllText(Path.Combine(publishedBundle, "bundle.json")))!.AsObject();
foreach (string path in Directory.EnumerateFiles(publishedBundle, "*", SearchOption.AllDirectories))
    if (Path.GetFileName(path).Contains(".olean", StringComparison.Ordinal) || Path.GetExtension(path) is ".dll" or ".ilean" or ".c" or ".o")
        throw new InvalidOperationException("Source bundle contained compiled output: " + path);
if (inventory["files"]!.AsObject().Any(pair => pair.Key.StartsWith("consumer/.lake/packages/leancil/", StringComparison.Ordinal)) ||
    !inventory["files"]!.AsObject().Any(pair => pair.Key.StartsWith("framework/CIL/", StringComparison.Ordinal)) ||
    !inventory["files"]!.AsObject().ContainsKey("exports/0/ExportAudit.lean"))
    throw new InvalidOperationException("Source bundle duplicated the framework package or omitted its framework/audit source closure.");
// A verifier needs the compatibility key and the producing revision without a second source.
if (inventory["frameworkKey"]?.GetValue<string>() != first["frameworkKey"]!.GetValue<string>() ||
    inventory["leanCilRevision"]?.GetValue<string>() != revision)
    throw new InvalidOperationException("Source bundle did not record its framework key and LeanCIL revision: " + inventory.ToJsonString());

string CallerVerify()
{
    Run([.. cli, "extract", app, "ImportFixture.Application::Entry(ulong)", callerArtifact, "--import", sidecar,
        "--import-implementation", "ImportFixture.Lib=" + library, "--import-sha256", "ImportFixture.Lib=" + Sha(library),
        "--import-interface-sha256", "ImportFixture.Lib=" + interfaceDigest]);
    return Run([.. cli, "verify", callerArtifact, "--proof", callerProof, "--proof-root", callerPackage]);
}

CallerVerify();
JsonElement initialCaller = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(callerArtifact, "verified.json")));
if (initialCaller.GetProperty("schema").GetInt32() != 4)
    throw new InvalidOperationException("Imported contract verification did not produce the schema-4 trust report.");
Console.WriteLine("PASS verified Lib -> generated sidecar -> App, with a source-only complete bundle");
RejectPostAuditMutations(library, artifact, package, proof, contractSource, sidecar);
Run(["dotnet", "run", "--file", "Tests/FullImportVerification.cs", "--", app, library, sidecar, publishedBundle,
    callerPackage, callerProof, package, proof], streamOutput: true, progress: "Independent full imported-library verification");

string restricted = Sha(sidecar);
string Restriction(string name, string assembly, string method, params string[] options)
{
    string folder = Path.Combine(root, "Restriction-" + name);
    Run([.. cli, "extract", assembly, method, folder, .. options]);
    File.WriteAllText(Path.Combine(folder, "verification.json"), JsonSerializer.Serialize(new
    {
        schema = 1, proof = Path.GetRelativePath(folder, proof).Replace('\\', '/'), theorem = "LibProof.correctness",
        proofRoot = Path.GetRelativePath(folder, package).Replace('\\', '/')
    }));
    return folder;
}
JsonObject RestrictedManifest(string assembly, string method, string folder)
{
    JsonObject manifest = ProducerManifest();
    manifest["assembly"] = assembly;
    manifest["exports"]![0]!["method"] = method;
    manifest["exports"]![0]!["artifact"] = folder;
    return manifest;
}
const string shape = "Contract exports require a public or protected static, non-virtual, non-generic method.";
const string assumptions = "Contract export version 1 rejects imports and static/initialization assumptions: ";
foreach ((string Name, string Method, string Marker) restriction in new[]
{
    ("internal", "ImportFixture.Library::Hidden(ulong)", shape),
    ("instance", "ImportFixture.Value::Add(ulong)", shape)
})
    RejectExport(RestrictedManifest(library, restriction.Method, Restriction(restriction.Name, library, restriction.Method)), restriction.Marker, restricted);
RejectExport(RestrictedManifest(library, "ImportFixture.Library::AddOne(ulong)",
    Restriction("initialized", library, "ImportFixture.Library::AddOne(ulong)", "--assume-initialized", "ImportFixture.Seeded")),
    assumptions + "initializedTypes", restricted);
RejectExport(RestrictedManifest(app, "ImportFixture.Application::Entry(ulong)",
    Restriction("imports", app, "ImportFixture.Application::Entry(ulong)", "--import", sidecar, "--import-implementation", "ImportFixture.Lib=" + library,
        "--import-sha256", "ImportFixture.Lib=" + Sha(library), "--import-interface-sha256", "ImportFixture.Lib=" + interfaceDigest)),
    assumptions + "imports", restricted);
string customProfile = Path.Combine(root, "custom-profile.json");
JsonObject profile = JsonNode.Parse(JsonSerializer.Serialize(new
{
    name = "scalar", architecture = "scalar", nativeWidth = 64, littleEndian = true, advSimd = false, sse2 = false, ssse3 = false,
    sse42 = false, avx = false, avx2 = false, avx512F = false, avx512FVL = false, bmi1 = false, sse41 = false, avx512DQ = false,
    avx512DQVL = false, bmi2 = false, armBase64 = false, vector256Accelerated = false, x86Base64 = false, vector128Accelerated = true
}))!.AsObject();
File.WriteAllText(customProfile, profile.ToJsonString());
RejectExport(RestrictedManifest(library, "ImportFixture.Library::AddOne(ulong)",
    Restriction("profile", library, "ImportFixture.Library::AddOne(ulong)", "@" + customProfile)),
    "Contract exports require an exact built-in profile.", restricted);
string referenceAssembly = Directory.EnumerateFiles(libraryRoot, "ImportFixture.Lib.dll", SearchOption.AllDirectories)
    .Single(path => path.Replace('\\', '/').Contains("/ref/", StringComparison.Ordinal));
RejectExport(RestrictedManifest(referenceAssembly, "ImportFixture.Library::AddOne(ulong)", artifact),
    "Cannot certify exports from a reference assembly.", restricted);
File.WriteAllText(manifestPath, ProducerManifest().ToJsonString());
(int Code, string Output, string Stdout, string Stderr) overlapping = Execute([.. cli, "export-contracts", manifestPath, "--output", sidecar,
    "--bundle", Path.Combine(package, "Bundles")]);
if (overlapping.Code == 0 || !overlapping.Output.Contains("Contract bundle output must be outside proof sources and extraction artifacts.", StringComparison.Ordinal) ||
    Sha(sidecar) != restricted || Directory.Exists(Path.Combine(package, "Bundles")))
    throw new InvalidOperationException("A bundle inside the proof sources was not rejected before publication: " + overlapping.Output);
Console.WriteLine("PASS version 1 export restrictions reject each unsupported method shape, assumption, profile, reference assembly and bundle location");

string pinnedSidecar = Sha(sidecar);
string[] bundlesBefore = Directory.EnumerateDirectories(bundle).Order(StringComparer.Ordinal).ToArray();
// The extractor verifies against the framework copy beside it.
string frameworkManifest = Path.Combine(Path.GetDirectoryName(ExtractorPath)!, "verification", "lake-manifest.json");
byte[] frameworkManifestBytes = File.ReadAllBytes(frameworkManifest);
string authorProof = File.ReadAllText(proof);
try
{
    // The proof elaborates after the input snapshot and edits a bundled framework source; neither a bundle nor a sidecar may appear.
    File.WriteAllText(proof, authorProof.Replace("namespace LibProof", "run_cmd Lean.Elab.Command.liftIO <| IO.FS.withFile " +
        JsonSerializer.Serialize(frameworkManifest) + " .append (fun handle => handle.putStr \"\\n\")\nnamespace LibProof", StringComparison.Ordinal));
    File.WriteAllText(manifestPath, ProducerManifest().ToJsonString());
    (int Code, string Output, string Stdout, string Stderr) changed = Execute([.. cli, "export-contracts", manifestPath, "--output", sidecar, "--bundle", bundle]);
    if (File.ReadAllBytes(frameworkManifest).SequenceEqual(frameworkManifestBytes))
        throw new InvalidOperationException("Precondition: the export proof did not edit the framework source: " + changed.Output);
    if (changed.Code == 0 || !changed.Output.Contains("inputs changed during", StringComparison.OrdinalIgnoreCase) || Sha(sidecar) != pinnedSidecar ||
        !Directory.EnumerateDirectories(bundle).Order(StringComparer.Ordinal).SequenceEqual(bundlesBefore))
        throw new InvalidOperationException("A framework source changed during export was published: " + changed.Output);
}
finally
{
    File.WriteAllBytes(frameworkManifest, frameworkManifestBytes);
    File.WriteAllText(proof, authorProof);
}
Console.WriteLine("PASS a bundled framework source changed during export publishes neither a bundle nor a sidecar");

string commentedCopy = Path.Combine(root, "CommentedArithmetic.lean");
File.WriteAllText(commentedCopy, File.ReadAllText(contractSource) + "\n-- Same closure, different published text.\n");
JsonObject commentedPublication = ProducerManifest();
commentedPublication["interface"]![0]!["source"] = commentedCopy;
RejectExport(commentedPublication, "byte-identical to its proofRoot module: PublishedArithmetic", pinnedSidecar);
Console.WriteLine("PASS a published interface must be the proofRoot module the export proof compiled against");

JsonObject two = ProducerManifest();
JsonObject invalid = two["exports"]![0]!.DeepClone().AsObject();
invalid["theorem"] = "LibProof.unrelated";
two["exports"]!.AsArray().Add(invalid);
RejectExport(two, "Duplicate contract export method/profile pair", firstSidecar);

Run([.. cli, "extract", library, "ImportFixture.Library::AddSame(ulong)", secondArtifact]);
File.WriteAllText(Path.Combine(secondArtifact, "verification.json"), JsonSerializer.Serialize(new
{
    schema = 1, proof = Path.GetRelativePath(secondArtifact, proof).Replace('\\', '/'), theorem = "LibProof.correctness",
    proofRoot = Path.GetRelativePath(secondArtifact, package).Replace('\\', '/')
}));
invalid["method"] = "ImportFixture.Library::AddSame(ulong)";
invalid["artifact"] = secondArtifact;
RejectExport(two, "exact canonical Holds statement", firstSidecar);
Console.WriteLine("PASS a later invalid export cannot publish a partial sidecar");

File.WriteAllText(librarySource, "namespace ImportFixture; public static class Library { public static ulong AddOne(ulong value) => unchecked(value - ulong.MaxValue); public static ulong AddSame(ulong value) => value + 1; }\n");
Run(["dotnet", "build", Path.Combine(libraryRoot, "Lib.csproj"), "-c", "Release"]);
if (Sha(library) == implementation) throw new InvalidOperationException("Precondition: the second library implementation must differ.");
ExtractLibrary();
Export(ProducerManifest());
JsonObject second = JsonNode.Parse(File.ReadAllText(sidecar))!.AsObject();
if (second["interfaceDigest"]!.GetValue<string>() != interfaceDigest || second["exports"]![0]!["closureDigest"]!.GetValue<string>() != closureDigest ||
    second["implementationSha256"]!.GetValue<string>() == implementation)
    throw new InvalidOperationException("A body-only rebuild changed the public contract identity or retained the old DLL hash.");
CallerVerify();
JsonElement reused = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(callerArtifact, "verified.json")));
if (reused.GetProperty("libraryBuild").GetString() != "consumer-proof-cache")
    throw new InvalidOperationException("An unchanged consumer proof did not reuse its interface-bound proof result.");
if (!File.ReadAllText(Path.Combine(callerArtifact, "verified.json")).Contains(Sha(library), StringComparison.Ordinal))
    throw new InvalidOperationException("Reused caller report did not bind the new implementation hash.");
Console.WriteLine("PASS a new library body retains interface/closure identities, unchanged caller proof, cache reuse and new deployment hash");

string prior = Sha(sidecar);
string publishedOnly = Path.Combine(root, "PublishedOnly.lean");
string originalContractSource = File.ReadAllText(contractSource);
File.WriteAllText(publishedOnly, originalContractSource.Replace("output = input + 1", "output = input + 2", StringComparison.Ordinal));
if (File.ReadAllText(publishedOnly) == originalContractSource)
    throw new InvalidOperationException("Precondition: the independent published contract must differ from the producer contract.");
JsonObject differentPublication = ProducerManifest();
differentPublication["interface"]![0]!["source"] = publishedOnly;
RejectExport(differentPublication, "byte-identical to its proofRoot module: PublishedArithmetic", prior);
if (File.ReadAllText(contractSource) != originalContractSource)
    throw new InvalidOperationException("The independent closure mismatch fixture changed the producer proof interface.");
Console.WriteLine("PASS different valid published and proof contract closures cannot replace a published sidecar");
File.WriteAllText(contractSource, File.ReadAllText(contractSource).Replace("output = input + 1", "output = input + 2", StringComparison.Ordinal));
RejectExport(ProducerManifest(), "unsolved goals", prior);
Console.WriteLine("PASS a failing library contract cannot replace a published sidecar");

partial class Program
{
    static void RejectPostAuditMutations(string assembly, string output, string package, string proof,
        string publishedSource, string sidecar)
    {
        const string auditSource = """
import Lean
import CIL.Safety.Linking
import CIL.Interface.Closure
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let .thmInfo author <- getConstInfo `LibProof.correctness | throwError "Expected an export theorem"
  unless author.levelParams.isEmpty do throwError "Export theorem must have a closed statement"
  let expected <- Lean.Elab.Term.elabType (<- `(@_root_.CIL.Safety.MethodContract.Holds _ _
    _root_.ImportFixture.addOne _root_.Extracted.program 0))
  unless <- isDefEq author.type expected do throwError "Export theorem does not have the exact canonical Holds statement"
theorem LeanCILExportAudit.certified : @_root_.CIL.Safety.MethodContract.Holds _ _
    _root_.ImportFixture.addOne _root_.Extracted.program 0 := _root_.LibProof.correctness
theorem LeanCILExportAudit.closed : _root_.CIL.Safety.Closed _root_.Extracted.program :=
  _root_.CIL.Safety.Closed.of_check (by decide +kernel)
theorem LeanCILExportAudit.noImports : _root_.Extracted.imports = [] := rfl
theorem LeanCILExportAudit.noStaticSites :
    _root_.Extracted.program.all (fun body => body.staticSites.isEmpty) = true := by decide +kernel
""";
        Dictionary<string, string> original = new[] { proof, publishedSource, sidecar }
            .ToDictionary(path => path, Sha, StringComparer.Ordinal);
        foreach (bool compiled in new[] { false, true })
        {
            using Program verification = new() { freshLibrary = true };
            bool callbackRan = false;
            ConsumerExportAudit audit = new(auditSource, (session, module, leanPath) =>
            {
                string target;
                if (compiled)
                {
                    string relative = module.Replace('.', Path.DirectorySeparatorChar) + ".olean";
                    string[] artifacts = leanPath.Split(Path.PathSeparator).Select(directory => Path.Combine(directory, relative))
                        .Where(File.Exists).Distinct(StringComparer.Ordinal).ToArray();
                    if (artifacts.Length != 1)
                        throw new InvalidOperationException("Expected exactly one checked export wrapper artifact.");
                    target = artifacts[0];
                }
                else target = Within(session, Path.GetRelativePath(package, proof));
                if (!File.Exists(target)) throw new InvalidOperationException("Missing checked export mutation target: " + target);
                File.AppendAllText(target, "\npost-audit-mutation\n");
                callbackRan = true;
            });
            ConsumerRequest request = new(assembly, output, proof, "LeanCILExportAudit.certified", null, ExportAudit: audit);
            ConsumerOutcome outcome = verification.VerifyConsumerRequests(package, [request], null, batch: false)[0];
            string expected = compiled ? "Compiled artifacts changed during contract export audit"
                : "Sources changed during contract export audit";
            if (!callbackRan || outcome.Report is not null || outcome.Error?.Message != expected ||
                File.Exists(Path.Combine(output, "verified.json")))
                throw new InvalidOperationException("Post-callback export mutation did not fail its exact integrity guard: " + outcome.Error);
            if (original.Any(pair => !File.Exists(pair.Key) || Sha(pair.Key) != pair.Value))
                throw new InvalidOperationException("Post-callback export mutation changed original proof, published source or sidecar bytes.");
            Console.WriteLine("PASS post-callback export " + (compiled ? "compiled artifact" : "source") + " mutation rejects without a report");
        }
    }
}
