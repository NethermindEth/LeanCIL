#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ExportVerificationSuites.cs

using System.Text.Json;
using System.Text.Json.Nodes;

if (args.Length < 8) throw new ArgumentException("Expected app, library, sidecar, bundle, caller package/proof and producer package/proof.");
string? cohort = ExportVerificationSuites.Select(args[8..], full: true);
if (cohort is null)
{
    Run(["dotnet", "run", "--file", "Tests/FullModuleResolution.cs"], streamOutput: true, progress: "Full-verification module resolution");
    foreach (ExportSuite entry in ExportVerificationSuites.FullPlan())
        Run(["dotnet", "run", "--file", "Tests/FullImportVerification.cs", "--", .. args[..8], "--cohort", entry.Cohort],
            streamOutput: true, progress: "Full export cohort " + entry.Cohort);
    return;
}
ExportCaseLedger completed = new(cohort);
string app = args[0];
string library = args[1];
string sidecar = args[2];
string bundle = args[3];
string callerPackage = args[4];
string caller = args[5];
string producerPackage = args[6];
string producerProof = args[7];
string root = At("artifacts/FullImportVerification-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
string artifact = Path.Combine(root, "App");
string[] cli = ["dotnet", ExtractorPath];
string originalSidecar = File.ReadAllText(sidecar);
byte[] originalLibrary = File.ReadAllBytes(library);
string originalCaller = File.ReadAllText(caller);
string proofInBundle = "consumer/" + Path.GetRelativePath(producerPackage, producerProof).Replace('\\', '/');

void ExtractApp(string? destination = null)
{
    JsonObject contract = JsonNode.Parse(File.ReadAllText(sidecar))!.AsObject();
    Run([.. cli, "extract", app, "ImportFixture.Application::Entry(ulong)", destination ?? artifact,
        "--import", sidecar, "--import-implementation", "ImportFixture.Lib=" + library,
        "--import-sha256", "ImportFixture.Lib=" + Sha(library),
        "--import-interface-sha256", "ImportFixture.Lib=" + contract["interfaceDigest"]!.GetValue<string>()]);
}
string[] FullCommand(params string[] options) => [.. cli, "verify", artifact, "--proof", caller,
    "--proof-root", callerPackage, "--force-full-verify", .. options];
void Reject(string diagnostic, params string[] options)
{
    (int Code, string Output, string Stdout, string Stderr) result = Execute(FullCommand(options));
    if (result.Code != 1 || !result.Output.Contains(diagnostic, StringComparison.Ordinal) ||
        File.Exists(Path.Combine(artifact, "verified.json")))
        throw new InvalidOperationException("Full verification did not reject its intended invalid input: " + result.Output);
}
void AssertIndependent(string output)
{
    JsonElement report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
    if (report.GetProperty("imports")[0].GetProperty("acceptedVia").GetString() != "independently-verified" ||
        report.GetProperty("imports")[0].GetProperty("sourceBundleDigest").GetString() != Path.GetFileName(bundle) ||
        report.GetProperty("compositionTheorem").GetString() != "LeanCILFullComposition.certified" ||
        !report.GetProperty("compositionAudit").GetString()!.Contains("LeanCILFullComposition.certified", StringComparison.Ordinal) ||
        // The published statement must carry the checked static link, not only the raw link.
        !report.GetProperty("compositionAudit").GetString()!.Contains("linkChecked", StringComparison.Ordinal))
        throw new InvalidOperationException("Full verification did not publish the independently checked composition and source identity.");
}

string? previousTrace = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
if (cohort is "consumer" or "checks" or "theorems" or "composition") ExtractApp();
if (cohort is "consumer" or "ordinary")
{
    string hiddenProof = producerProof + ".hidden";
    File.Move(producerProof, hiddenProof);
    string trace = Path.Combine(root, "trace");
    try
    {
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
        if (cohort == "consumer")
        {
            Run(FullCommand("--full-artifact", "ImportFixture.Lib=" + bundle));
            AssertIndependent(artifact);
            completed.CompleteCase("full.consumer-explicit");
            Run(FullCommand());
            AssertIndependent(artifact);
            completed.CompleteCase("full.consumer-repeat");
        }
        else
        {
            string ordinary = Path.Combine(root, "OrdinaryApp");
            ExtractApp(ordinary);
            Run([.. cli, "verify", ordinary, "--proof", caller, "--force-full-verify"]);
            AssertIndependent(ordinary);
            completed.CompleteCase("full.ordinary");
        }
    }
    finally
    {
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", previousTrace);
        File.Move(hiddenProof, producerProof);
    }
    JsonElement[] stages = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
    var expectedRuns = cohort == "consumer" ? 2 : 1;
    var proofRuns = stages.GroupBy(stage => stage.GetProperty("processId").GetInt32())
        .Select(group => group.Select(stage => stage.GetProperty("stage").GetString()!).ToArray())
        .Where(group => group.Contains("Fresh extraction of the current imported library DLL",
            StringComparer.Ordinal)).ToArray();
    if (stages.Count(stage => stage.GetProperty("stage").GetString() == "Fresh extraction of the current imported library DLL") != expectedRuns ||
        stages.Count(stage => stage.GetProperty("stage").GetString() == "Capturing actual checked author and extraction kernel terms") != expectedRuns ||
        stages.Count(stage => stage.GetProperty("stage").GetString() == "Independent kernel replay of the composed caller theorem") != expectedRuns ||
        proofRuns.Length != expectedRuns || proofRuns.Any(run =>
            run.Count(stage => stage == "Building fresh consumer proof and dependencies") !=
                (cohort == "consumer" ? 2 : 1) ||
            run.Count(stage => stage.StartsWith("Checking Proof:", StringComparison.Ordinal)) !=
                (cohort == "consumer" ? 0 : 1)))
        throw new InvalidOperationException("Repeated full verification did not re-extract, audit and replay each actual library and composition.");
    Console.WriteLine("PASS " + cohort + " full verification without original library proof paths");
}

if (cohort == "pair")
{
    string[] TraceStages(string directory) => Directory.EnumerateFiles(directory, "*.jsonl").SelectMany(File.ReadLines)
        .Select(line => JsonSerializer.Deserialize<JsonElement>(line).GetProperty("stage").GetString()!).ToArray();
    string pairRoot = Path.Combine(root, "Pair");
    Directory.CreateDirectory(pairRoot);
    string[] pairMethods = ["ImportFixture.Library::AddOne(ulong)", "ImportFixture.Library::AddSame(ulong)"];
    string[] pairArtifacts = pairMethods.Select((_, index) => Path.Combine(pairRoot, "Export" + index)).ToArray();
    for (int index = 0; index < pairMethods.Length; index++)
    {
        Run([.. cli, "extract", library, pairMethods[index], pairArtifacts[index]]);
        File.WriteAllText(Path.Combine(pairArtifacts[index], "verification.json"), JsonSerializer.Serialize(new
        {
            schema = 1, proof = Path.GetRelativePath(pairArtifacts[index], producerProof).Replace('\\', '/'), theorem = "LibProof.correctness",
            proofRoot = Path.GetRelativePath(pairArtifacts[index], producerPackage).Replace('\\', '/')
        }));
    }
    string pairManifest = Path.Combine(pairRoot, "export.json");
    string pairSidecar = Path.Combine(pairRoot, "ImportFixture.Lib.leancil.contracts");
    File.WriteAllText(pairManifest, JsonSerializer.Serialize(new
    {
        schema = 1, assembly = library, proofRoot = producerPackage,
        @interface = new[] { new { module = "PublishedArithmetic", source = Path.Combine(producerPackage, "PublishedArithmetic.lean") } },
        exports = pairMethods.Select((method, index) => new { method, artifact = pairArtifacts[index], contract = "ImportFixture.addOne", theorem = "LibProof.correctness" })
    }));
    Run([.. cli, "export-contracts", pairManifest, "--output", pairSidecar, "--bundle", Path.Combine(pairRoot, "Bundles")]);
    string pairApp = Path.Combine(pairRoot, "App");
    Directory.CreateDirectory(pairApp);
    File.WriteAllText(Path.Combine(pairApp, "PairApp.csproj"), $$"""
    <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AssemblyName>ImportFixture.PairApp</AssemblyName><Optimize>true</Optimize></PropertyGroup><ItemGroup><Reference Include="ImportFixture.Lib"><HintPath>{{library}}</HintPath></Reference></ItemGroup></Project>
    """);
    File.WriteAllText(Path.Combine(pairApp, "Application.cs"), "namespace ImportFixture; public static class PairApplication { public static ulong Entry(ulong value) => Library.AddSame(Library.AddOne(value)); }\n");
    Run(["dotnet", "build", Path.Combine(pairApp, "PairApp.csproj"), "-c", "Release"]);
    if (!originalLibrary.AsSpan().SequenceEqual(File.ReadAllBytes(library))) throw new InvalidOperationException("Precondition: the pair caller build changed the library DLL.");
    string pairArtifact = Path.Combine(pairRoot, "Caller");
    JsonObject pairContract = JsonNode.Parse(File.ReadAllText(pairSidecar))!.AsObject();
    Run([.. cli, "extract", Path.Combine(pairApp, "bin", "ImportFixture.PairApp.dll"), "ImportFixture.PairApplication::Entry(ulong)", pairArtifact,
        "--import", pairSidecar, "--import-implementation", "ImportFixture.Lib=" + library, "--import-sha256", "ImportFixture.Lib=" + Sha(library),
        "--import-interface-sha256", "ImportFixture.Lib=" + pairContract["interfaceDigest"]!.GetValue<string>()]);
    string pairCaller = Path.Combine(pairRoot, "PairCaller.lean");
    File.WriteAllText(pairCaller, "import ExtractedImports\nnamespace ExampleProof\ntheorem correctness : " +
        "_root_.CIL.Safety.HoldsGiven _root_.Extracted.program _root_.Extracted.ImportsHold (fun _ => True) := by\n" +
        "  intro linked links imported\n  trivial\nend ExampleProof\n");
    string pairTrace = Path.Combine(root, "pair-trace");
    try
    {
        Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", pairTrace);
        Run([.. cli, "verify", pairArtifact, "--proof", pairCaller, "--force-full-verify"]);
    }
    finally { Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", previousTrace); }
    JsonElement pairReport = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(pairArtifact, "verified.json")));
    JsonElement[] pairImports = pairReport.GetProperty("imports").EnumerateArray().ToArray();
    string pairBundle = Path.GetFileName(pairContract["fullVerificationLocator"]!.GetValue<string>());
    string[] pairStages = TraceStages(pairTrace);
    // The caller and the shared bundle each obtain the library once; a per-slot build would add a third.
    if (pairImports.Length != 2 || pairImports.Any(import => import.GetProperty("acceptedVia").GetString() != "independently-verified" ||
            import.GetProperty("sourceBundleDigest").GetString() != pairBundle) ||
        pairStages.Count(stage => stage == "Fresh extraction of the current imported library DLL") != 2 ||
        pairStages.Count(stage => stage == "Capturing actual checked author and extraction kernel terms") != 2 ||
        pairStages.Count(stage => stage is "Building fresh Lean verification library" or "Copying certified Lean verification library") != 2 ||
        pairStages.Count(stage => stage == "Building fresh consumer proof and dependencies") != 2 ||
        pairStages.Count(stage => stage.StartsWith("Checking Proof:", StringComparison.Ordinal)) != 1)
        throw new InvalidOperationException("Two imports from one bundle were not verified with one library build: " + string.Join(", ", pairStages));
    completed.CompleteCase("full.pair");
    Console.WriteLine("PASS two imports from one source bundle share one independent library build");

}

if (cohort == "consumer")
{
    (int Code, string Output, string Stdout, string Stderr) artifactWithoutFull = Execute([.. cli, "verify", artifact,
        "--proof", caller, "--proof-root", callerPackage, "--full-artifact", "ImportFixture.Lib=" + bundle]);
    if (artifactWithoutFull.Code != 1 || !artifactWithoutFull.Output.Contains("--full-artifact requires --force-full-verify", StringComparison.Ordinal) ||
        File.Exists(Path.Combine(artifact, "verified.json")))
        throw new InvalidOperationException("A full artifact without full mode was accepted or retained a stale report: " + artifactWithoutFull.Output);
    completed.CompleteCase("full.artifact-mode");
}

if (cohort == "checks")
{
    Reject("Full verification source bundle is missing", "--full-artifact", "ImportFixture.Lib=" + Path.Combine(root, "missing", Path.GetFileName(bundle)));
    completed.CompleteCase("full.missing-bundle");
    string inventoryPath = Path.Combine(bundle, "bundle.json");
    byte[] inventoryBytes = File.ReadAllBytes(inventoryPath);
    try
    {
        File.AppendAllText(inventoryPath, "\n");
        Reject("Contract source bundle manifest digest mismatch");
        completed.CompleteCase("full.inventory-bytes");
    }
    finally { File.WriteAllBytes(inventoryPath, inventoryBytes); }
    string authorPath = Path.Combine(bundle, proofInBundle);
    byte[] authorBytes = File.ReadAllBytes(authorPath);
    try
    {
        File.AppendAllText(authorPath, "\n");
        Reject("Contract source bundle file is missing or changed: " + proofInBundle);
        completed.CompleteCase("full.producer-bytes");
    }
    finally { File.WriteAllBytes(authorPath, authorBytes); }
    string forgedArtifact = Path.Combine(bundle, "Proof.olean");
    try
    {
        File.WriteAllText(forgedArtifact, "not proof evidence");
        Reject("Contract source bundle contains an unrecorded file: Proof.olean");
        completed.CompleteCase("full.unrecorded-olean");
    }
    finally { File.Delete(forgedArtifact); }
    try
    {
        File.AppendAllText(library, "changed-current-dll");
        Reject("Full-verification imported implementation or sidecar changed");
        completed.CompleteCase("full.deployed-dll");
    }
    finally { File.WriteAllBytes(library, originalLibrary); }

}

string Rebundle(string proofSource, bool staleClosure = false)
{
    string staging = Path.Combine(root, "rebundle-" + Guid.NewGuid().ToString("N"));
    CopyTree(bundle, staging);
    File.WriteAllText(Path.Combine(staging, proofInBundle), proofSource);
    JsonObject inventory = JsonNode.Parse(File.ReadAllText(Path.Combine(staging, "bundle.json")))!.AsObject();
    inventory["files"]![proofInBundle] = Sha(Path.Combine(staging, proofInBundle));
    if (staleClosure) inventory["exports"]![0]!["digest"] = new string('0', 64);
    File.WriteAllText(Path.Combine(staging, "bundle.json"), inventory.ToJsonString());
    string destination = Path.Combine(root, Sha(Path.Combine(staging, "bundle.json")));
    Directory.Move(staging, destination);
    JsonObject current = JsonNode.Parse(originalSidecar)!.AsObject();
    current["fullVerificationLocator"] = destination;
    File.WriteAllText(sidecar, current.ToJsonString());
    ExtractApp();
    return destination;
}

void RejectCallerMutation(bool consumer, bool sourceOnly, bool shadow = false)
{
    string suffix = (consumer ? "consumer" : "ordinary") + (shadow ? "-original-root-shadow" : sourceOnly ? "-source" : "-artifact");
    string callerContext = Path.Combine(root, suffix + "-caller.json");
    string mutationMarker = Path.Combine(root, suffix + "-mutation.json");
    string attackCaller = Path.Combine(callerPackage, "FullMutationCaller.lean");
    string attackArtifact = Path.Combine(root, "MutationApp-" + suffix);
    string cache = Path.Combine(root, "mutation-cache-" + suffix);
    string? previousCache = Environment.GetEnvironmentVariable("LEANCIL_CACHE_DIR");
    string originalProducer = File.ReadAllText(producerProof);
    string recordContext = $$"""

open Lean Elab Command in
run_cmd do
  let source <- IO.FS.realPath (System.FilePath.mk (<- getFileName))
  let cwd <- IO.currentDir
  let search <- IO.getEnv "LEAN_PATH"
  IO.FS.writeFile {{JsonSerializer.Serialize(callerContext)}} (Json.mkObj [
    ("source", toJson source.toString), ("cwd", toJson cwd.toString),
    ("leanPath", toJson (search.getD ""))]).compress
""";
    string callerSource = "import Lean\n" + originalCaller + recordContext;
    File.WriteAllText(attackCaller, callerSource);
    using Program paths = new();
    string weakCaller = "import ExtractedImports\nnamespace ExampleProof\ntheorem correctness : " +
        "_root_.CIL.Safety.HoldsGiven _root_.Extracted.program _root_.Extracted.ImportsHold (fun _ => True) := by\n" +
        "  intro linked links imported\n  trivial\nend ExampleProof\n";
    string mutateCaller = $$"""

open Lean Elab Command in
run_cmd do
  let context <- IO.ofExcept <| Json.parse (<- IO.FS.readFile {{JsonSerializer.Serialize(callerContext)}})
  let source := System.FilePath.mk (<- IO.ofExcept <| context.getObjValAs? String "source")
  let folder := source.parent.getD "."
  let original <- IO.FS.readFile source
  let callerArtifact := folder / {{JsonSerializer.Serialize(consumer ? ".lake/build/lib/lean/LeanCILProof.olean" : "Proof.olean")}}
  let originalArtifact <- IO.FS.readBinFile callerArtifact
  let target <-
    if {{(shadow ? "true" : "false")}} then
      pure ((callerArtifact.parent.getD ".") / "LeanCILFullExpected0.olean")
    else pure {{(sourceOnly ? "source" : "callerArtifact")}}
  if {{(shadow ? "true" : "false")}} then
    let shadowSource := (target.parent.getD ".") / "LeanCILFullExpected0.lean"
    IO.FS.writeFile shadowSource {{JsonSerializer.Serialize(weakCaller)}}
    let search <- IO.ofExcept <| context.getObjValAs? String "leanPath"
    let cwd := System.FilePath.mk (<- IO.ofExcept <| context.getObjValAs? String "cwd")
    let compiled <- IO.Process.output {
      cmd := {{JsonSerializer.Serialize(paths.LeanExecutable)}}
      args := #["--root=" ++ (target.parent.getD ".").toString, "-o", target.toString, shadowSource.toString]
      cwd := some cwd
      env := #[("LEAN_PATH", some search), ("LEAN_SYSROOT", some {{JsonSerializer.Serialize(paths.Toolchain)}})] }
    unless compiled.exitCode == 0 do throwError "Caller shadow compile failed: {compiled.stdout} {compiled.stderr}"
  else if {{(sourceOnly ? "true" : "false")}} then
    IO.FS.writeFile source (original ++ "\n")
  else
    let before <- IO.FS.readBinFile target
    try
      IO.FS.writeFile source (original ++ "\ntheorem FullCallerSubstitutionMarker : True := True.intro\n")
      let cwd := System.FilePath.mk (<- IO.ofExcept <| context.getObjValAs? String "cwd")
      let search <- IO.ofExcept <| context.getObjValAs? String "leanPath"
      let compiled <- IO.Process.output {
        cmd := {{JsonSerializer.Serialize(paths.LeanExecutable)}}
        args := #["--root=" ++ folder.toString, "-o", target.toString, source.toString]
        cwd := some cwd
        env := #[("LEAN_PATH", some search), ("LEAN_SYSROOT", some {{JsonSerializer.Serialize(paths.Toolchain)}})] }
      unless compiled.exitCode == 0 do
        throwError "Caller substitution compile failed: {compiled.stdout} {compiled.stderr}"
      if (<- IO.FS.readBinFile target) == before then throwError "Caller artifact did not change"
    finally
      IO.FS.writeFile source original
  IO.FS.writeFile {{JsonSerializer.Serialize(mutationMarker)}} (Json.mkObj [
    ("target", toJson target.toString), ("sourceRestored", toJson ((<- IO.FS.readFile source) == original)),
    ("originalArtifactUnchanged", toJson ((<- IO.FS.readBinFile callerArtifact) == originalArtifact))]).compress
""";
    try
    {
        Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", cache);
        Rebundle("import Lean\n" + originalProducer + mutateCaller);
        ExtractApp(attackArtifact);
        (int Code, string Output, string Stdout, string Stderr) rejected = Execute([.. cli, "verify", attackArtifact,
            "--proof", attackCaller, "--force-full-verify", .. consumer ? new[] { "--proof-root", callerPackage } : []]);
        if (!File.Exists(mutationMarker))
            throw new InvalidOperationException("Producer mutation did not execute during fresh verification: " + rejected.Output);
        JsonElement mutation = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(mutationMarker));
        // Lean spells paths with mixed separators and a lowercase drive on Windows.
        string target = Path.GetFullPath(mutation.GetProperty("target").GetString()!);
        string diagnostic = shadow ? "Unexpected full-verification caller artifact: " + target
            : sourceOnly ? "Sources changed during full import audit"
            : "Full-verification source or compiled artifact changed: " + target;
        if (rejected.Code != 1 || !rejected.Output.Contains(diagnostic, OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal) ||
            mutation.GetProperty("sourceRestored").GetBoolean() == sourceOnly ||
            mutation.GetProperty("originalArtifactUnchanged").GetBoolean() != (sourceOnly || shadow) ||
            File.Exists(Path.Combine(attackArtifact, "verified.json")) ||
            Directory.Exists(cache) && Directory.EnumerateFiles(cache, "receipt.json", SearchOption.AllDirectories).Any())
            throw new InvalidOperationException("Producer changed an already checked caller without its exact integrity rejection: " + rejected.Output);
        if (File.ReadAllText(attackCaller) != callerSource || File.ReadAllText(caller) != originalCaller ||
            File.ReadAllText(producerProof) != originalProducer)
            throw new InvalidOperationException("Producer caller-substitution test changed original proof sources.");
        Console.WriteLine("PASS producer " + suffix + " mutation rejects after actual execution without a report or receipt");
    }
    finally
    {
        Environment.SetEnvironmentVariable("LEANCIL_CACHE_DIR", previousCache);
        File.Delete(attackCaller);
        File.WriteAllText(sidecar, originalSidecar);
        ExtractApp();
    }
}

switch (cohort)
{
    case "consumer-artifact":
        RejectCallerMutation(consumer: true, sourceOnly: false);
        completed.CompleteCase("full.consumer-artifact");
        break;
    case "ordinary-artifact":
        RejectCallerMutation(consumer: false, sourceOnly: false);
        completed.CompleteCase("full.ordinary-artifact");
        break;
    case "consumer-source":
        RejectCallerMutation(consumer: true, sourceOnly: true);
        completed.CompleteCase("full.consumer-source");
        break;
    case "consumer-shadow":
        RejectCallerMutation(consumer: true, sourceOnly: false, shadow: true);
        completed.CompleteCase("full.consumer-shadow");
        break;
}
if (cohort == "checks")
{
    try
    {
        Rebundle(File.ReadAllText(producerProof), staleClosure: true);
        Reject("Full source bundle export statement or closure binding mismatch");
        completed.CompleteCase("full.stale-closure");
    }
    finally
    {
        File.WriteAllText(sidecar, originalSidecar);
        ExtractApp();
    }
    try
    {
        JsonObject forged = JsonNode.Parse(originalSidecar)!.AsObject();
        forged["certifications"]![0]!["statementDigest"] = new string('0', 64);
        File.WriteAllText(sidecar, forged.ToJsonString());
        ExtractApp();
        Reject("Full source bundle export statement or closure binding mismatch");
        completed.CompleteCase("full.statement-digest");
    }
    finally
    {
        File.WriteAllText(sidecar, originalSidecar);
        ExtractApp();
    }
    try
    {
        File.WriteAllText(caller, originalCaller.Replace("theorem correctness :", "theorem correctness (extra : False) :", StringComparison.Ordinal));
        Reject("Theorem statement mismatch: ExampleProof.correctness");
        completed.CompleteCase("full.extra-premise");
    }
    finally { File.WriteAllText(caller, originalCaller); }
}
if (cohort == "theorems")
{
    try
    {
        Rebundle("import Extracted\nimport PublishedArithmetic\nnamespace LibProof\ntheorem correctness : True := True.intro\nend LibProof\n");
        Reject("Type mismatch");
        completed.CompleteCase("full.producer-true");
        Rebundle(File.ReadAllText(producerProof).Replace("theorem correctness", "def correctness", StringComparison.Ordinal));
        Reject("Expected a theorem");
        completed.CompleteCase("full.producer-definition");
    }
    finally
    {
        File.WriteAllText(sidecar, originalSidecar);
        ExtractApp();
    }
}

if (cohort == "composition")
{
    try
    {
        string forgedTransfer = """

    macro_rules
      | `(theorem $name:ident : $type:term := $_proof:term) => do
          if name.getId.toString != "certified" || type.raw.isIdent then Lean.Macro.throwUnsupported
          `(theorem $name:ident : True := True.intro)
    """;
        string captureForgery = "\nmacro_rules\n  | `(IO.FS.writeFile $path:term $source:term) =>\n" +
            "      `(_root_.IO.FS.writeFile $path ($source ++ " + JsonSerializer.Serialize(forgedTransfer) + "))\n";
        Rebundle(File.ReadAllText(producerProof) + captureForgery);
        Reject("Theorem statement mismatch: LeanCILFullComposition.certified");
        completed.CompleteCase("full.composition-true");
    }
    finally
    {
        File.WriteAllText(sidecar, originalSidecar);
        ExtractApp();
    }
    Console.WriteLine("PASS a forged transfer macro cannot replace the composed caller claim with True");
}
completed.Finish();
