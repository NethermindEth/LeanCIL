#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ConsumerTraceDirectory.cs

using System.Diagnostics;
using System.Text.Json;

if (args is not ([] or ["--measure-baseline"]))
    throw new ArgumentException("Usage: dotnet run --file Tests/CliImportedKernelAudit.cs -- [--measure-baseline]");
var baseline = args.Length != 0;
var cli = new[] { "dotnet", At("Extractor/bin/Nethermind.LeanCIL.dll") };
var assembly = At("Examples/Assembly/bin/Examples.dll");
var trace = ConsumerTraceDirectory.Create(At("artifacts"), "CliImportedKernelAuditTrace");
Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
var timer = Stopwatch.StartNew();

// Helpers outside the CIL aggregate compile only after the isolated base library audit.
var importedRoot = At("artifacts/CliImportedKernelAudit-" + Guid.NewGuid().ToString("N"));
var importedTool = Path.Combine(importedRoot, "tool");
CopyTree(Path.GetDirectoryName(cli[1])!, importedTool);
var sources = Path.Combine(importedTool, "verification", "CIL");
File.WriteAllText(Path.Combine(sources, "AuditGood.lean"),
    "import Lean\nnamespace AuditGood\ntheorem helper : True := True.intro\nend AuditGood\n");
File.WriteAllText(Path.Combine(sources, "AuditBad.lean"), """
    import Lean
    set_option debug.skipKernelTC true
    run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
      name := `AuditBad.helper
      levelParams := []
      type := Lean.mkConst ``False
      value := Lean.mkConst ``True.intro
    })
    """);
var importedCli = new[] { "dotnet", Path.Combine(importedTool, Path.GetFileName(cli[1])) };
var importedOutput = Path.Combine(importedRoot, "output");
Run([.. importedCli, "extract", assembly, "Arithmetic::Add(ulong,ulong)", importedOutput]);
var importedProof = Path.Combine(importedRoot, "Proof.lean");
File.WriteAllText(importedProof,
    "import Extracted\nimport CIL.AuditGood\ntheorem ExampleProof.correctness : True := AuditGood.helper\n");
// This corpus deliberately differs from CI's shared certified library. Build
// and replay it from source rather than accepting that library's certificate.
var uncertified = new Dictionary<string, string>
{
    ["LEANCIL_CERTIFIED_LIBRARY"] = "",
    ["LEANCIL_CERTIFIED_LIBRARY_SHA256"] = ""
};
var verificationEnvironment = uncertified;
if (!baseline)
{
    // Run the existing producer from this exact corpus, not the checkout's unmodified sources.
    var corpus = Path.Combine(importedTool, "verification");
    var scripts = Path.Combine(corpus, "scripts");
    Directory.CreateDirectory(scripts);
    Directory.CreateDirectory(Path.Combine(corpus, "Extractor"));
    foreach (var name in new[] { "PrepareLibrary.cs", "Verification.cs" })
        File.Copy(At("scripts/" + name), Path.Combine(scripts, name));
    foreach (var name in new[] { "global.json", "Directory.Build.props", "Directory.Packages.props", ".editorconfig" })
        File.Copy(At(name), Path.Combine(corpus, name));
    var prepared = Path.Combine(importedRoot, "prepared");
    var preparation = Run(["dotnet", "run", "--file", Path.Combine(scripts, "PrepareLibrary.cs"), "--", prepared],
        progress: "Preparing modified CLI library once", environment: uncertified);
    const string digestPrefix = "Certified library manifest SHA256: ";
    var digest = preparation.Split('\n').Single(line => line.StartsWith(digestPrefix))[digestPrefix.Length..].Trim();
    if (digest.Length != 64 || digest != Sha(Path.Combine(prepared, "cache-manifest.json")))
        throw new InvalidOperationException("Modified library producer did not return its manifest digest.");
    verificationEnvironment = new Dictionary<string, string>
    {
        ["LEANCIL_CERTIFIED_LIBRARY"] = prepared,
        ["LEANCIL_CERTIFIED_LIBRARY_SHA256"] = digest
    };

    // A valid certificate for this corpus must fail against the unmodified packaged sources.
    var mismatched = Execute([.. cli, "verify", importedOutput, "--proof", importedProof, "--fresh"],
        environment: verificationEnvironment);
    if (mismatched.Code != 1 || !mismatched.Stderr.Contains("Certified library identity or integrity mismatch") ||
        File.Exists(Path.Combine(importedOutput, "verified.json")))
        throw new InvalidOperationException("Modified library authorized unmodified sources: " + mismatched.Output);
}
var validImported = Execute([.. importedCli, "verify", importedOutput, "--proof", importedProof, "--fresh"],
    progress: "Checking valid imported helper against modified library", environment: verificationEnvironment);
if (validImported.Code != 0 || validImported.Stderr.Length != 0 ||
    !validImported.Stdout.StartsWith("Verified: ExampleProof.correctness"))
    throw new InvalidOperationException("Valid imported CIL helper rejected: " + validImported.Output);
File.WriteAllText(importedProof,
    "import Extracted\nimport CIL.AuditBad\ntheorem ExampleProof.correctness : False := AuditBad.helper\n");
var invalidImported = Execute([.. importedCli, "verify", importedOutput, "--proof", importedProof, "--fresh"],
    progress: "Rejecting forged imported helper against modified library", environment: verificationEnvironment);
if (invalidImported.Code != 1 || invalidImported.Stdout.Length != 0 ||
    !invalidImported.Stderr.Contains("Stage: kernel replay") ||
    !invalidImported.Stderr.Contains("AuditBad.helper") ||
    File.Exists(Path.Combine(importedOutput, "verified.json")))
    throw new InvalidOperationException("Unchecked imported CIL helper bypassed replay: " + invalidImported.Output);
Console.WriteLine("PASS CLI replay covers valid and forged CIL helpers outside the base aggregate");

var stages = Directory.EnumerateFiles(trace, "*.jsonl").SelectMany(File.ReadLines)
    .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
int Count(string name) => stages.Count(stage => stage.GetProperty("stage").GetString() == name);
double Seconds(string name) => stages.Where(stage => stage.GetProperty("stage").GetString() == name)
    .Sum(stage => stage.GetProperty("durationSeconds").GetDouble());
const string buildStage = "Building fresh Lean verification library";
const string replayStage = "Joint kernel replay of fresh Lean verification library";
const string copyStage = "Copying certified Lean verification library";
if (Count(buildStage) != (baseline ? 2 : 1) || Count(replayStage) != (baseline ? 2 : 1) ||
    Count(copyStage) != (baseline ? 0 : 2))
    throw new InvalidOperationException("Imported helper checks repeated or skipped their certified base preparation.");
var measurements = new
{
    baseline, wallSeconds = timer.Elapsed.TotalSeconds,
    freshBuilds = Count(buildStage), freshBuildSeconds = Seconds(buildStage),
    baseReplays = Count(replayStage), baseReplaySeconds = Seconds(replayStage),
    privateCopies = Count(copyStage), privateCopySeconds = Seconds(copyStage)
};
File.WriteAllText(Path.Combine(importedRoot, "timings.json"), JsonSerializer.Serialize(measurements, Json));
Console.WriteLine("PASS CLI imported helper preparation counts: " + JsonSerializer.Serialize(measurements));

