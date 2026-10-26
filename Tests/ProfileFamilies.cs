#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;
using System.Text.Json.Nodes;

var root = At("artifacts/ProfileFamilies");
var assemblyRoot = Path.Combine(root, "Assembly");
var package = Path.Combine(root, "Package");
Directory.CreateDirectory(assemblyRoot);
Directory.CreateDirectory(package);
File.WriteAllText(Path.Combine(assemblyRoot, "Family.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
<Optimize>true</Optimize></PropertyGroup></Project>
""");
File.WriteAllText(Path.Combine(assemblyRoot, "Family.cs"), """
public static class Family
{
    public static bool Supported() => System.Runtime.Intrinsics.X86.Sse2.IsSupported;
    public static int Pruned() => System.Runtime.Intrinsics.X86.Avx2.IsSupported ? 2 : 1;
}
public static class InitializedFamily
{
    public static readonly int Value;
    static InitializedFamily() { Value = 42; }
    public static bool Supported() => System.Runtime.Intrinsics.X86.Sse2.IsSupported;
}
""");
Run(["dotnet", "build", Path.Combine(assemblyRoot, "Family.csproj"), "-c", "Release"]);
var assembly = Path.Combine(assemblyRoot, "bin/Family.dll");
var profiles = new[] { "x64-sse2", "x64-sse42", "x64-v3", "scalar" };
var artifacts = profiles.Select(profile => Path.Combine(root, profile)).ToArray();
var proof = Path.Combine(package, "FamilyProof.lean");
for (var index = 0; index < profiles.Length; index++)
{
    Run(Extract("extract", assembly, "Family", "Family::Supported()", artifacts[index], profiles[index]));
    File.WriteAllText(Path.Combine(artifacts[index], "verification.json"), JsonSerializer.Serialize(new
    {
        schema = 1, proof, theorem = "FamilyProof.family", proofRoot = package
    }));
}
var reference = Path.Combine(package, "Reference.lean");
File.WriteAllText(reference, File.ReadAllText(Path.Combine(artifacts[0], "Extracted.lean"))
    .Replace("Extracted", "Reference", StringComparison.Ordinal));
var contract = Path.Combine(package, "FamilyContract.lean");
File.Copy(At("Tests/ContractImports/ProfileFamilyContract.lean"), contract, overwrite: true);
File.Copy(At("Tests/ContractImports/ProfileFamilyProof.lean"), proof, overwrite: true);
var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(package, "lakefile.toml"), $$"""
name = "family"
[[require]]
name = "leancil"
git = {{JsonSerializer.Serialize(Root.Replace('\\', '/'))}}
rev = "{{revision}}"
[[lean_lib]]
name = "FamilyContract"
[[lean_lib]]
name = "Reference"
[[lean_lib]]
name = "FamilyProof"
""");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"), overwrite: true);
Run(["lake", "update"], package);
var manifestPath = Path.Combine(root, "manifest.json");
var sidecar = Path.Combine(root, "Family.leancil.contracts");
var bundle = Path.Combine(root, "Bundle");
JsonObject Manifest(params int[] selected) => JsonSerializer.SerializeToNode(new
{
    schema = 1, assembly, proofRoot = package,
    @interface = new[] { new { module = "FamilyContract", source = contract } },
    exports = new[] { new
    {
        method = "Family::Supported()", contract = "FamilyContract.supported", theorem = "FamilyProof.family",
        program = "Reference.program", referenceProfile = profiles[0],
        profiles = selected.Select(index => new { profile = profiles[index], artifact = artifacts[index] }).ToArray()
    } }
})!.AsObject();
void Export(JsonObject manifest, string? rejection = null)
{
    File.WriteAllText(manifestPath, manifest.ToJsonString());
    var previous = File.Exists(sidecar) ? Sha(sidecar) : null;
    var result = Execute(["dotnet", ExtractorPath, "export-contracts", manifestPath,
        "--output", sidecar, "--bundle", bundle]);
    File.WriteAllText(Path.Combine(root, "run-" + Guid.NewGuid().ToString("N") + ".log"), result.Output);
    if (rejection is null)
    {
        if (result.Code != 0) throw new InvalidOperationException(result.Output);
    }
    else if (result.Code == 0 || !result.Output.Contains(rejection, StringComparison.Ordinal) ||
        (previous is null ? File.Exists(sidecar) : !File.Exists(sidecar) || Sha(sidecar) != previous))
        throw new InvalidOperationException("Expected rejection without sidecar publication: " +
            rejection + "\n" + result.Output);
}
Export(Manifest(0, 1, 2));
var published = JsonNode.Parse(File.ReadAllText(sidecar))!;
if (published["exports"]![0]!["profiles"]!.AsArray().Count != 3)
    throw new InvalidOperationException("One family entry did not publish all three checked profiles.");
Console.WriteLine("PASS one family theorem and manifest entry, three independently checked profiles");
var app = Path.Combine(root, "App");
var callerPackage = Path.Combine(root, "Caller");
Directory.CreateDirectory(app);
Directory.CreateDirectory(callerPackage);
File.WriteAllText(Path.Combine(app, "App.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
<Optimize>true</Optimize></PropertyGroup><ItemGroup>
<ProjectReference Include="../Assembly/Family.csproj" /></ItemGroup></Project>
""");
File.WriteAllText(Path.Combine(app, "App.cs"),
    "public static class App { public static bool Query() => Family.Supported(); }");
Run(["dotnet", "build", Path.Combine(app, "App.csproj"), "-c", "Release"]);
File.WriteAllText(Path.Combine(callerPackage, "lakefile.toml"), $$"""
name = "caller"
[[require]]
name = "leancil"
git = {{JsonSerializer.Serialize(Root.Replace('\\', '/'))}}
rev = "{{revision}}"
[[lean_lib]]
name = "Caller"
""");
File.Copy(At("lean-toolchain"), Path.Combine(callerPackage, "lean-toolchain"), true);
var caller = Path.Combine(callerPackage, "Caller.lean");
File.Copy(At("Tests/ContractImports/ProfileFamilyCaller.lean"), caller, true);
Run(["lake", "update"], callerPackage);
var callerArtifact = Path.Combine(root, "CallerArtifact");
Run(["dotnet", ExtractorPath, "extract", Path.Combine(app, "bin/App.dll"), "App::Query()", callerArtifact,
    "x64-v3", "--import", sidecar, "--import-implementation", "Family=" + assembly,
    "--import-sha256", "Family=" + Sha(assembly), "--import-interface-sha256",
    "Family=" + published["interfaceDigest"]!.GetValue<string>()]);
var full = Execute(["dotnet", ExtractorPath, "verify", callerArtifact, "--proof", caller,
    "--proof-root", callerPackage, "--force-full-verify"]);
File.WriteAllText(Path.Combine(root, "full-consumer.log"), full.Output);
if (full.Code != 0 || JsonNode.Parse(File.ReadAllText(Path.Combine(callerArtifact, "verified.json")))!
        ["compositionTheorem"]?.GetValue<string>() != "LeanCILFullComposition.certified")
    throw new InvalidOperationException("Family source-bundle verification failed: " + full.Output);
Console.WriteLine("PASS independent full verification consumes the third expanded profile and fixed reference");
Export(Manifest(0, 3), "Profile family disagrees on read flag: CIL.Feature.sse2");
Console.WriteLine("PASS disagreeing read flag named and partial publication rejected");
var wrong = Manifest(0, 1);
wrong["exports"]![0]!["profiles"]![1]!["profile"] = "x64-v4";
Export(wrong, "does not match its selected profile");
Export(Manifest(1), "must include its referenceProfile artifact");
var duplicate = Manifest(0, 0);
Export(duplicate, "distinct profiles");
var familySource = File.ReadAllText(proof);
var different = familySource.Replace("Reference.program", "different", StringComparison.Ordinal)
    .Replace("import Reference", "import Reference\nimport Extracted", StringComparison.Ordinal)
    .Replace("open CIL CIL.Safety", "open CIL CIL.Safety\n" +
        "@[cil_code] def different : Program := Reference.program ++ Extracted.program", StringComparison.Ordinal);
File.WriteAllText(proof, different);
var changed = Manifest(0);
changed["exports"]![0]!["program"] = "FamilyProof.different";
Export(changed, "reference differs from its fixed extraction artifact");
File.WriteAllText(proof, familySource);
Console.WriteLine("PASS different reference body rejected despite valid family contract and flag agreement");
File.WriteAllText(proof, familySource.Replace("theorem family", "def family", StringComparison.Ordinal));
Export(Manifest(0), "Expected a theorem");
File.WriteAllText(proof, familySource);
Console.WriteLine("PASS family definition rejected by theorem audit");
File.WriteAllText(proof, familySource + """

set_option hygiene false in
macro_rules
  | `(theorem LeanCILExportAudit.referenceIdentity : $_left:term = $_right:term := $_proof:term) =>
      `(theorem LeanCILExportAudit.referenceIdentity : True := True.intro)
""");
Export(Manifest(0), "Theorem statement mismatch: LeanCILExportAudit.referenceIdentity");
File.WriteAllText(proof, familySource);
Console.WriteLine("PASS author macro cannot bypass the fixed reference audit");
File.WriteAllText(proof, familySource + """

set_option hygiene false in
macro_rules
  | `(theorem LeanCILExportAudit.referenceUniform : $_left:term = $_right:term := $_proof:term) =>
      `(theorem LeanCILExportAudit.referenceUniform : True := True.intro)
""");
Export(Manifest(0), "Theorem statement mismatch: LeanCILExportAudit.referenceUniform");
File.WriteAllText(proof, familySource);
Console.WriteLine("PASS author macro cannot bypass the uniform profile audit");
File.WriteAllText(proof, familySource + """

run_cmd do
  let path := ".lake/build/lib/lean/LeanCILProfileReference.olean"
  let bytes ← IO.FS.readBinFile path
  IO.FS.writeBinFile path (bytes.push 0)
""");
Export(Manifest(0), "Generated export artifacts changed during proof checking");
File.WriteAllText(proof, familySource);
Console.WriteLine("PASS author code cannot replace the compiled fixed reference");
File.WriteAllText(proof, familySource + """

theorem FamilyProof.impossible (profile : CIL.FeatureProfile) (impossible : False) :
    FamilyContract.supported.Holds (CIL.reprofile Reference.program profile) 0 := impossible.elim
#print axioms FamilyProof.impossible
""");
var impossible = Manifest(0);
impossible["exports"]![0]!["theorem"] = "FamilyProof.impossible";
Export(impossible, "False");
File.WriteAllText(proof, familySource);
Console.WriteLine("PASS false family predicate rejected");
var outcome = Manifest(0, 1);
outcome["exports"]![0]!["contract"] = "FamilyContract.outcome";
outcome["exports"]![0]!["theorem"] = "FamilyProof.outcomeFamily";
Export(outcome);
Console.WriteLine("PASS one outcome-family entry certifies two profiles");
var pruned = new[] { Path.Combine(root, "PrunedReference"), Path.Combine(root, "PrunedWide") };
foreach (var (index, profile) in new[] { "x64-sse2", "x64-v3" }.Index())
{
    Run(Extract("extract", assembly, "Family", "Family::Pruned()", pruned[index], profile));
    File.Copy(Path.Combine(artifacts[0], "verification.json"), Path.Combine(pruned[index], "verification.json"), true);
}
var referenceSource = File.ReadAllText(reference);
File.WriteAllText(reference, File.ReadAllText(Path.Combine(pruned[0], "Extracted.lean"))
    .Replace("Extracted", "Reference", StringComparison.Ordinal));
var pruning = Manifest(0, 2);
pruning["exports"]![0]!["method"] = "Family::Pruned()";
pruning["exports"]![0]!["profiles"]![0]!["artifact"] = pruned[0];
pruning["exports"]![0]!["profiles"]![1]!["artifact"] = pruned[1];
Export(pruning, "extraction differs from the reprofiled reference program");
File.WriteAllText(reference, referenceSource);
Console.WriteLine("PASS independently checked pruning difference rejected");
var initialized = new[] { Path.Combine(root, "InitializedReference"), Path.Combine(root, "InitializedWide") };
foreach (var (index, profile) in new[] { "x64-sse2", "x64-v3" }.Index())
{
    Run(["dotnet", ExtractorPath, "extract", assembly, "InitializedFamily::Supported()", initialized[index],
        profile, "--assume-initialized", "InitializedFamily"]);
    File.Copy(Path.Combine(artifacts[0], "verification.json"),
        Path.Combine(initialized[index], "verification.json"), true);
}
File.WriteAllText(reference, File.ReadAllText(Path.Combine(initialized[0], "Extracted.lean"))
    .Replace("Extracted", "Reference", StringComparison.Ordinal));
var initialization = Manifest(0, 2);
initialization["exports"]![0]!["method"] = "InitializedFamily::Supported()";
initialization["exports"]![0]!["profiles"]![0]!["artifact"] = initialized[0];
initialization["exports"]![0]!["profiles"]![1]!["artifact"] = initialized[1];
Export(initialization);
var assumptions = JsonNode.Parse(File.ReadAllText(sidecar))!["exports"]![0]!["initializationAssumptions"]!.AsArray();
if (assumptions.Count != 2 || assumptions.Any(profile =>
        profile!["types"]!.AsArray().Count != 1 ||
        profile["types"]![0]!["typeName"]!.GetValue<string>() != "InitializedFamily"))
    throw new InvalidOperationException("Profile family lost a scoped initialization premise.");
File.WriteAllText(reference, referenceSource);
Console.WriteLine("PASS fixed reference metadata and scoped initialization premises preserved for both profiles");
Console.WriteLine("All profile-family checks passed.");
