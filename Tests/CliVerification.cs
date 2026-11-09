#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.Json.Nodes;

var cli = args.Length == 0
    ? new[] { "dotnet", At("Extractor/bin/Nethermind.LeanCIL.dll") }
    : new[] { Path.GetFullPath(args[0]) };
var output = At("artifacts/CliVerification");
var assembly = At("Examples/Assembly/bin/Examples.dll");
var proof = At("Examples/Proofs/Add.lean");
var settingsPath = Path.Combine(output, "verification.json");

void Verified(params string[] options)
{
    var result = Execute([.. cli, "verify", output, .. options]);

    if (result.Code != 0 || WithoutStageProgress(result.Stderr).Length != 0 || !result.Stdout.StartsWith("Verified: ExampleProof.correctness") ||
        !result.Stdout.Contains("Statement:") || !result.Stdout.Contains("BitVec.toNat") ||
        !result.Stdout.Contains("(x y : CIL.W64)"))
        throw new InvalidOperationException("CLI proof failed: " + result.Output);

    // Authors read the statement in Lean notation, as Unicode, and the proof's own `#print` output.
    var entry = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "identity.json")))
        .GetProperty("entry").GetString();
    var stdout = result.Stdout.ReplaceLineEndings("\n");
    if (!stdout.Contains("\u2203 result,") || stdout.Contains("Exists fun") || stdout.Contains("HMod.hMod") ||
        !stdout.Contains($"  Subject: {entry} (method 0) via CIL.Safety.invoke\n") ||
        !stdout.Contains($"  Extraction entry: {entry}\n") || stdout.Contains("  Entry:") ||
        !stdout.Contains("Add.lean:15:0: info: 'ExampleProof.correctness' depends on axioms"))
        throw new InvalidOperationException(
            "CLI verification did not print the readable statement, subject and messages: " + result.Output);

    var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
    if (report.GetProperty("schema").GetInt32() != 4 ||
        !report.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid"))
        throw new InvalidOperationException("Missing mandatory extraction certificate audit in report.");

    if (report.GetProperty("theorem").GetString() != "ExampleProof.correctness")
        throw new InvalidOperationException("Wrong theorem in CLI verification report.");

    if (!report.GetProperty("inputs").TryGetProperty("settings:" + Path.GetFullPath(settingsPath), out _))
        throw new InvalidOperationException("Verification settings are not bound to the report.");
}

// Build a disposable copy so the demonstration tests an actual source edit and rebuild.
var fixture = At("artifacts/CliDemoSource");
var demoAssembly = Path.Combine(fixture, "bin", "Examples.dll");
var addition = "Add(ulong x, ulong y) => unchecked(x + y)";
var subtraction = "Add(ulong x, ulong y) => unchecked(x - y)";
// Copies keep their sources' old timestamps, so an output an aborted run built from an edit would
// look current to MSBuild; staging starts from an empty directory instead.
void StageFixture()
{
    if (Directory.Exists(fixture)) Directory.Delete(fixture, true);
    Directory.CreateDirectory(fixture);
    foreach (var path in Directory.EnumerateFiles(At("Examples/Assembly")))
        if (Path.GetExtension(path) is ".cs" or ".csproj")
            File.Copy(path, Path.Combine(fixture, Path.GetFileName(path)), true);
    Run(["dotnet", "build", fixture, "-c", "Release"]);
}
// Leave what an aborted run leaves behind, so the proof below fails if restaging keeps its output.
StageFixture();
var editedMethods = Path.Combine(fixture, "Methods.cs");
File.WriteAllText(editedMethods, File.ReadAllText(editedMethods).Replace(addition, subtraction));
Run(["dotnet", "build", fixture, "-c", "Release"]);
StageFixture();

// Explicit proof selection becomes portable settings, separate from the generated report.
Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", output]);
Verified("--proof", proof);
Verified("--fresh");
var settings = File.ReadAllText(settingsPath);
if (Path.IsPathRooted(JsonSerializer.Deserialize<JsonElement>(settings).GetProperty("proof").GetString()!))
    throw new InvalidOperationException("Expected a relative proof path in verification settings.");
Console.WriteLine("PASS CLI proof selection, persistent settings and theorem statement");

// Elaborator acceptance and an empty axiom list do not establish kernel validity.
// Test both a forged selected theorem and a normally checked theorem using a forged helper.
var auditOutput = At("artifacts/CliKernelAudit");
Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", auditOutput]);
foreach (var transitive in new[] { false, true })
{
    var maliciousProof = Path.Combine(auditOutput, "Unchecked.lean");
    var forgedName = transitive ? "ExampleProof.helper" : "ExampleProof.correctness";
    File.WriteAllText(maliciousProof, $$"""
        import Extracted
        import Lean
        set_option debug.skipKernelTC true
        run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
          name := `{{forgedName}}
          levelParams := []
          type := Lean.mkConst ``False
          value := Lean.mkConst ``True.intro
        })
        set_option debug.skipKernelTC false
        {{(transitive ? "theorem ExampleProof.correctness : False := ExampleProof.helper" : "")}}
        """);
    // A failed attempt must also invalidate an earlier report.
    File.WriteAllText(Path.Combine(auditOutput, "verified.json"), "stale report");
    var invalid = Execute([.. cli, "verify", auditOutput, "--proof", maliciousProof]);
    if (invalid.Code != 1 || invalid.Stdout.Length != 0 ||
        !invalid.Stderr.Contains("Stage: kernel replay") ||
        !invalid.Stderr.Contains("while replaying declaration") ||
        File.Exists(Path.Combine(auditOutput, "verified.json")))
        throw new InvalidOperationException("Unchecked theorem bypassed kernel replay: " + invalid.Output);
}
Console.WriteLine("PASS CLI kernel replay rejects unchecked theorems and transitive helpers");

// The unchanged addition contract must fail after changing + to - and rebuilding.
var methodsPath = Path.Combine(fixture, "Methods.cs");
var methods = File.ReadAllText(methodsPath);
File.WriteAllText(methodsPath, methods.Replace(addition, subtraction));
Run(["dotnet", "build", fixture, "-c", "Release"]);
var stale = Execute([.. cli, "check", output]);
if (stale.Code != 1 || !stale.Stderr.Contains("assembly has changed") || !stale.Stderr.Contains("Next: Rerun leancil extract"))
    throw new InvalidOperationException("Missing actionable stale-assembly diagnostic: " + stale.Output);

Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", output]);
var rejected = Execute([.. cli, "verify", output]);

if (rejected.Code != 1 || rejected.Stdout.Length != 0 || !WithoutStageProgress(rejected.Stderr).StartsWith("Invalid:") ||
    !rejected.Stderr.Contains("Lean errors (") || !rejected.Stderr.Contains("Stage: proof checking") ||
    !rejected.Stderr.Contains("Next:") || File.Exists(Path.Combine(output, "verified.json")) ||
    File.ReadAllText(settingsPath) != settings)
    throw new InvalidOperationException("Incorrect implementation was not rejected by the proof: " + rejected.Output);
RequireSourceLocations(rejected.Stderr, "Examples/Proofs/Add.lean:");
// Tools read `--format json` instead: one record per Lean error, the same exit code, nothing on stderr.
RequireReport(Execute([.. cli, "verify", output, "--format", "json"]), 1, "WrongAdd.json", (output, "<output>"),
    (proof, "<proof>"));

Console.WriteLine("PASS CLI incorrect implementation rejected without a successful report");

// Fixing the implementation needs no repeated proof arguments or previous success report.
File.WriteAllText(methodsPath, methods);
Run(["dotnet", "build", fixture, "-c", "Release"]);
Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", output]);
Verified();
Console.WriteLine("PASS CLI verification settings survive failure and support recovery");
RequireReport(Execute([.. cli, "verify", output, "--format", "json"]), 0, "Verified.json", (output, "<output>"),
    (proof, "<proof>"));

// A loop proof missing its invariant reports the open obligation by its tag, and a loop tactic that stops
// reports the method, pc and instruction it reached and what differs, read from its failure record.
var loopOutput = At("artifacts/CliLoopReports");
Run([.. cli, "extract", demoAssembly, "Examples.Loops::Countdown(uint)", loopOutput]);
var countdown = File.ReadAllText(At("Examples/Proofs/Countdown.lean")).ReplaceLineEndings("\n");
var noInvariant = Path.Combine(loopOutput, "NoInvariant.lean");
File.WriteAllText(noInvariant, Edited(countdown, "    case invariant => trivial\n", ""));
RequireReport(Execute([.. cli, "verify", loopOutput, "--proof", noInvariant, "--format", "json"]), 1,
    "MissingInvariant.json", (loopOutput, "<output>"), (noInvariant, "<proof>"));
var wrongHead = Path.Combine(loopOutput, "WrongHead.lean");
File.WriteAllText(wrongHead, Edited(countdown, "cil_loop_continue \u27e8x - 1, updated, next\u27e9",
    "cil_loop_continue \u27e8x - 2, updated, next\u27e9"));
RequireReport(Execute([.. cli, "verify", loopOutput, "--proof", wrongHead, "--format", "json"]), 1,
    "LoopHeadMismatch.json", (loopOutput, "<output>"), (wrongHead, "<proof>"));
// The record is requested only by `--format json`; the default report is the error alone.
var wrongHeadText = Execute([.. cli, "verify", loopOutput, "--proof", wrongHead]);
if (wrongHeadText.Code != 1 || !wrongHeadText.Stderr.Contains("cil_loop_steps: target state not matched at pc 8") ||
    wrongHeadText.Stderr.Contains("[LeanCIL failure"))
    throw new InvalidOperationException("The default report changed for a loop failure: " + wrongHeadText.Output);
Console.WriteLine("PASS CLI --format json reports each failure with its obligation, pc and state, and success");

// `--trace` passes each step the proof takes through, apart from the proof's messages, in text and in JSON,
// with each tactic's step count and the obligations it left; without it the report has no trace.
var countdownProof = At("Examples/Proofs/Countdown.lean");
var traced = Execute([.. cli, "verify", loopOutput, "--proof", countdownProof, "--trace"]);
var tracedText = traced.Stdout.ReplaceLineEndings("\n");
var tracedMessages = tracedText[..Math.Max(0, tracedText.IndexOf("  Trace (", StringComparison.Ordinal))];
if (traced.Code != 0 || !tracedText.Contains("  Trace (") || tracedText.Contains("Untraced") ||
    !tracedText.Contains("Countdown.lean:31:8: [CIL.step] pc 0: CIL.Op.arg 0\n") ||
    !tracedText.Contains("[CIL.step] cil_loop_steps took ") || tracedMessages.Contains("[CIL.step]") ||
    // The tactic sits in a `refine` term Lean elaborates more than once; only the attempt it kept is traced.
    tracedText.Split("Countdown.lean:31:8: [CIL.step] cil_loop_steps took ").Length != 2)
    throw new InvalidOperationException("verify --trace did not report the steps apart: " + traced.Output);
var tracedReport = JsonNode.Parse(Execute([.. cli, "verify", loopOutput, "--proof", countdownProof, "--trace",
    "--format", "json"]).Stdout) as JsonObject;
var steps = tracedReport?["trace"]?.AsArray().Select(step => step!["text"]!.GetValue<string>()).ToArray() ?? [];
if (steps.Length == 0 || !steps.All(step => step.StartsWith("[CIL.step] ", StringComparison.Ordinal)) ||
    tracedReport!["unknown"]!.AsObject().Count != 0 ||
    tracedReport["messages"]!.AsArray().Any(message => message!["text"]!.GetValue<string>().Contains("[CIL.step]")))
    throw new InvalidOperationException("verify --trace --format json did not report the steps in `trace`: " +
        tracedReport?.ToJsonString());
var untraced = Execute([.. cli, "verify", loopOutput, "--proof", countdownProof]);
if (untraced.Code != 0 || untraced.Stdout.Contains("[CIL.step]") || untraced.Stdout.Contains("Trace ("))
    throw new InvalidOperationException("verify without --trace printed a trace: " + untraced.Output);
Console.WriteLine("PASS CLI --trace reports each step apart from the proof's messages, and only when asked");

// A proof stuck on a class instance names the object fact it lacks: the entry of `DepositBoth` checks each
// account argument before its `callvirt` can throw, so an account with no formation fact stops it.
var objectOutput = At("artifacts/CliObjectReports");
Run([.. cli, "extract", demoAssembly, "Examples.Objects::DepositBoth(Examples.Account,Examples.Account,ulong)",
    objectOutput]);
var depositBothProof = At("Examples/Proofs/DepositBoth.lean");
var unformed = Path.Combine(objectOutput, "UnformedAccount.lean");
File.WriteAllText(unformed, Edited(File.ReadAllText(depositBothProof).ReplaceLineEndings("\n"),
    "  cil_checked_steps [secondLive.formed]\n", "  cil_checked_steps []\n"));
RequireReport(Execute([.. cli, "verify", objectOutput, "--proof", unformed, "--theorem",
    "ExampleProof.first_null_throws", "--format", "json"]), 1, "UnformedAccount.json", (objectOutput, "<output>"),
    (unformed, "<proof>"));
// The trace shows the receiver-checked call and the exception it throws on a null receiver.
var objectTrace = Execute([.. cli, "verify", objectOutput, "--proof", depositBothProof, "--theorem",
    "ExampleProof.first_null_throws", "--trace"]).Stdout.ReplaceLineEndings("\n");
if (!objectTrace.Contains("[CIL.step] pc 2: CIL.Op.callInstance 1 2\n") ||
    !objectTrace.Contains("changes faults: ExecutionFault.thrown \"System.NullReferenceException\"\n"))
    throw new InvalidOperationException("verify --trace did not show the null receiver's call: " + objectTrace);
Console.WriteLine("PASS CLI reports a proof stuck on a class instance and traces its receiver-checked call");

// This theorem proves invalid memory access cannot produce a successful execution.
var memoryOutput = At("artifacts/CliMemory");
Run([.. cli, "extract", assembly, "Arithmetic::PastEnd(ulong&)", memoryOutput]);
var memory = Execute([.. cli, "verify", memoryOutput, "--proof", At("Examples/Proofs/PastEnd.lean")]);
if (memory.Code != 0 || WithoutStageProgress(memory.Stderr).Length != 0 || !memory.Stdout.Contains("Statement:") ||
    !memory.Stdout.Contains("fuel") || !memory.Stdout.Contains("Except.ok"))
    throw new InvalidOperationException("Missing checked invalid-access theorem: " + memory.Output);
Console.WriteLine("PASS CLI invalid memory-access theorem");

// The tool ships only CIL; a proof importing a repository fixture must name it, not fail inside Lake.
foreach (var module in new[] { "Tests.Support", "Examples.Support" })
{
    var fixtureProof = Path.Combine(auditOutput, "Fixture.lean");
    File.WriteAllText(fixtureProof, $"import Extracted\nimport {module}\n");
    var fixtureImport = Execute([.. cli, "verify", auditOutput, "--proof", fixtureProof]);
    var failure = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(auditOutput, "failed.json")));
    if (fixtureImport.Code != 1 || !fixtureImport.Stderr.Contains("Stage: proof selection") ||
        !fixtureImport.Stderr.Contains($"imports {module}, a LeanCIL repository module") ||
        failure.GetProperty("kind").GetString() != "invalid-request")
        throw new InvalidOperationException("Repository fixture import was not rejected by name: " + fixtureImport.Output);
}
Console.WriteLine("PASS CLI rejects proofs importing repository fixtures the tool does not ship");

// Query commands are how authors explore the API: their output must survive a failed audit, located
// in the author's file, and long output must say where the rest is rather than vanish.
var queryProof = Path.Combine(auditOutput, "Query.lean");
File.WriteAllText(queryProof, "import Extracted\n#check CIL.Safety.invoke\n" +
    string.Concat(Enumerable.Range(0, 70).Select(i => $"#eval {i} + 1000\n")));
var query = Execute([.. cli, "verify", auditOutput, "--proof", queryProof]);
var queryErrors = query.Stderr.ReplaceLineEndings("\n");
var fullMessages = Path.Combine(auditOutput, "proof-messages.txt");
if (query.Code != 1 || !queryErrors.Contains("Stage: theorem audit") ||
    !queryErrors.Contains("Query.lean:2:0: info: CIL.Safety.invoke (program : CIL.Program) (fuel method : Nat)") ||
    !queryErrors.Contains("Except CIL.Safety.LocatedFault (CIL.Safety.Memory \u00d7 List CIL.Safety.Value)\n") ||
    !queryErrors.Contains("Query.lean:3:0: info: 1000\n") || queryErrors.Contains("info: 1069\n") ||
    !queryErrors.Contains(" more lines in artifacts/CliKernelAudit/proof-messages.txt\n") ||
!File.ReadAllText(fullMessages).Contains("info: 1069\n"))
    throw new InvalidOperationException("Proof query output was not shown with its location: " + query.Output);
Console.WriteLine("PASS CLI shows located #check and #eval output and keeps long output in proof-messages.txt");

// The report names the method a theorem is about, not the extraction entry, and claims nothing for an open index.
var subjectOutput = At("artifacts/CliSubjects");
Run([.. cli, "extract", demoAssembly, "Examples.Loops::TallyTwice(uint)", subjectOutput]);
var subjectProof = Path.Combine(subjectOutput, "Subjects.lean");
File.WriteAllText(subjectProof, """
    import Extracted
    import CIL.MethodIdentity
    import CIL.Safety.MethodContract
    namespace ExampleProof
    bind_method tally tallyBody := "System.UInt32 Examples.Loops::TallyTwice(System.UInt32)"
    bind_callee addTwo addTwoBody := "System.UInt32 Examples.Loops::AddTwo(System.UInt32)" from tallyBody
    theorem helper (contract : CIL.Safety.MethodContract CIL.W32 CIL.W32)
        (holds : contract.Holds Extracted.program addTwo) : contract.Holds Extracted.program addTwo := holds
    theorem unfixed (contract : CIL.Safety.MethodContract CIL.W32 CIL.W32) (method : Nat)
        (holds : contract.Holds Extracted.program method) : contract.Holds Extracted.program method := holds
    end ExampleProof
    """);
const string addTwo =
    "System.UInt32 Examples.Loops::AddTwo(System.UInt32) (method 1) via CIL.Safety.MethodContract.Holds";
var helper = Execute([.. cli, "verify", subjectOutput, "--proof", subjectProof, "--theorem", "ExampleProof.helper"])
    .Stdout.ReplaceLineEndings("\n");
if (!helper.Contains($"  Subject: {addTwo}\n") || !helper.Contains($"  Premise: {addTwo}\n") ||
    helper.Contains("Subject: System.UInt32 Examples.Loops::TallyTwice") ||
    !helper.Contains("  Extraction entry: System.UInt32 Examples.Loops::TallyTwice(System.UInt32)\n"))
    throw new InvalidOperationException("Helper theorem was not labelled by its subject: " + helper);
var unfixed = Execute([.. cli, "verify", subjectOutput, "--theorem", "ExampleProof.unfixed"])
    .Stdout.ReplaceLineEndings("\n");
if (!unfixed.Contains("  Subject: a method index the statement does not fix via CIL.Safety.MethodContract.Holds\n") ||
    unfixed.Contains("Examples.Loops::AddTwo") || unfixed.Contains("Subject: System.UInt32"))
    throw new InvalidOperationException("An unfixed method index was labelled as a specific method: " + unfixed);
Console.WriteLine("PASS CLI labels a theorem by the methods its statement names");

// A proof checked inside a consumer package is read by its author exactly like a standalone one, fresh or cached.
var consumerRoot = At("artifacts/CliConsumer");
if (Directory.Exists(consumerRoot)) DeleteTree(consumerRoot);
var consumerPackage = Path.Combine(consumerRoot, "Package");
Directory.CreateDirectory(Path.Combine(consumerPackage, "Proofs"));
var revision = Execute(["git", "-C", Root, "rev-parse", "HEAD"]).Stdout.Trim();
File.WriteAllText(Path.Combine(consumerPackage, "lakefile.toml"), $$"""
    name = "consumer"
    [[require]]
    name = "leancil"
    git = {{JsonSerializer.Serialize(Root.Replace('\\', '/'))}}
    rev = "{{revision}}"
    [[lean_lib]]
    name = "Proofs"
    """);
File.Copy(At("lean-toolchain"), Path.Combine(consumerPackage, "lean-toolchain"));
var consumerProof = Path.Combine(consumerPackage, "Proofs", "Add.lean");
File.Copy(proof, consumerProof);
Run(["lake", "update"], consumerPackage);
var consumerOutput = Path.Combine(consumerRoot, "Extraction");
Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", consumerOutput]);
var consumerEntry = JsonSerializer.Deserialize<JsonElement>(
    File.ReadAllText(Path.Combine(consumerOutput, "identity.json"))).GetProperty("entry").GetString();
// A fresh run publishes nothing; the first ordinary run may reuse an earlier test run's result, the second must.
foreach (var (options, cached) in new[]
    { (new[] { "--fresh" }, (bool?)false), (Array.Empty<string>(), null), (Array.Empty<string>(), true) })
{
    var consumer = Execute([.. cli, "verify", consumerOutput, "--proof", consumerProof,
        "--proof-root", consumerPackage, .. options]);
    var consumerText = consumer.Stdout.ReplaceLineEndings("\n");
    var libraryBuild = JsonSerializer.Deserialize<JsonElement>(
        File.ReadAllText(Path.Combine(consumerOutput, "verified.json"))).GetProperty("libraryBuild").GetString();
    if (consumer.Code != 0 || (cached is { } reused && (libraryBuild == "consumer-proof-cache") != reused) ||
        !consumerText.Contains("∃ result,") || consumerText.Contains("Exists fun") ||
        consumerText.Contains("Subject: not identified") ||
        !consumerText.Contains($"  Subject: {consumerEntry} (method 0) via CIL.Safety.invoke\n") ||
        !consumerText.Contains("  Lean messages (1):\n") ||
        !consumerText.Contains("Add.lean:15:0: info: 'ExampleProof.correctness' depends on axioms"))
        throw new InvalidOperationException(
            "Consumer verification did not print the readable statement, subject and messages: " + consumer.Output);
}
Console.WriteLine("PASS CLI prints the readable statement, subject and Lean messages for --proof-root proofs");

// Query output is what an author reads while a proof is unfinished, so a failed check must still show it.
// Messages are proof-authored, so a terminal escape or carriage return must not overwrite report lines.
var unfinishedProof = Path.Combine(consumerPackage, "Proofs", "Unfinished.lean");
File.WriteAllText(unfinishedProof, "import Extracted\n#eval 1000 + 234\n" +
    "#eval IO.println \"kept\\x1b[2K\\rVerified\"\n" +
    "theorem ExampleProof.correctness : False := by\n  exact trivial\n");
var unfinished = Execute([.. cli, "verify", consumerOutput, "--proof", unfinishedProof,
    "--proof-root", consumerPackage]);
var unfinishedText = unfinished.Stderr.ReplaceLineEndings("\n");
if (unfinished.Code != 1 || !unfinishedText.Contains("Stage: proof checking") ||
    !unfinishedText.Contains("  Lean messages (2):\n") ||
    !unfinishedText.Contains("Unfinished.lean:2:0: info: 1234\n") ||
    !unfinishedText.Contains("Unfinished.lean:3:0: info: kept\\u001B[2K\\u000DVerified\n") ||
    unfinishedText.Contains('\u001B') || unfinishedText.Contains('\r'))
    throw new InvalidOperationException("A failed --proof-root check hid or passed through the proof's messages: " +
        unfinished.Output);
RequireSourceLocations(unfinishedText,
    "artifacts/CliConsumer/Package/Proofs/Unfinished.lean:5:2 (building Proofs.Unfinished)");
// A --proof-root report cites the package's own file and module, as the text report does.
var unfinishedJson = Execute([.. cli, "verify", consumerOutput, "--proof", unfinishedProof,
    "--proof-root", consumerPackage, "--format", "json"]);
var unfinishedFailure = (JsonNode.Parse(unfinishedJson.Stdout) as JsonObject)?["failures"]?[0];
if (unfinishedJson.Code != 1 || WithoutStageProgress(unfinishedJson.Stderr).Length != 0 ||
    unfinishedFailure?["module"]?.GetValue<string>() != "Proofs.Unfinished" ||
    unfinishedFailure["source"]?["file"]?.GetValue<string>() != Path.GetFullPath(unfinishedProof))
    throw new InvalidOperationException("A --proof-root JSON report did not cite the package's file: " +
        unfinishedJson.Output);

// `verify-batch --format json` prints one document with each request's `verify --format json` report, and
// `--trace` adds each request's steps; the rejected request is last, so the output keeps its settings.
var batchManifest = Path.Combine(consumerRoot, "requests.json");
File.WriteAllText(batchManifest, JsonSerializer.Serialize(new
{
    schema = 1, proofRoot = consumerPackage, requests = new object[]
    {
        new { output = consumerOutput, proof = consumerProof, theorem = "ExampleProof.correctness" },
        new { output = consumerOutput, proof = unfinishedProof, theorem = "ExampleProof.correctness",
            expect = "rejected" }
    }
}));
var batch = Execute([.. cli, "verify-batch", batchManifest, "--format", "json", "--trace"]);
var batchReport = JsonNode.Parse(batch.Stdout) as JsonObject;
var batchRequests = batchReport?["requests"]?.AsArray();
if (batch.Code != 0 || WithoutStageProgress(batch.Stderr).Length != 0 || batchReport?["schema"]?.GetValue<int>() != 1 ||
    batchReport["passed"]?.GetValue<int>() != 2 || batchRequests is not { Count: 2 } ||
    batchRequests[0]!["status"]!.GetValue<string>() != "verified" ||
    batchRequests[0]!["report"]!["result"]!.GetValue<string>() != "verified" ||
    batchRequests[0]!["report"]!["trace"] is not JsonArray { Count: > 0 } verifiedSteps ||
    !verifiedSteps.All(step => step!["text"]!.GetValue<string>().StartsWith("[CIL.step] ", StringComparison.Ordinal)) ||
    batchRequests[1]!["status"]!.GetValue<string>() != "rejected" ||
    batchRequests[1]!["report"]!["result"]!.GetValue<string>() != "failed" ||
    batchRequests[1]!["report"]!["failures"]?[0]?["source"]?["file"]?.GetValue<string>() !=
        Path.GetFullPath(unfinishedProof))
    throw new InvalidOperationException("verify-batch --format json --trace did not print one report per request: " +
        batch.Output);
var batchText = Execute([.. cli, "verify-batch", batchManifest, "--trace"]);
if (batchText.Code != 0 || !batchText.Stdout.Contains("PASS verified") || !batchText.Stdout.Contains("  Trace (") ||
    !batchText.Stdout.Contains("Batch: 2 passed, 0 failed of 2 requests."))
    throw new InvalidOperationException("verify-batch --trace did not print each request's trace: " + batchText.Output);
Console.WriteLine("PASS CLI verify-batch reports each request as JSON and traces each request's steps");
Console.WriteLine("PASS CLI shows Lean messages, with control characters escaped, when a --proof-root proof fails");

// A starting proof must elaborate yet be refused until its holes are filled, must never replace a
// file, and must refuse a stale extraction or a shape it cannot state rather than write a guess.
var outlines = At("artifacts/CliOutline");
if (Directory.Exists(outlines)) Directory.Delete(outlines, true);
var outlined = Path.Combine(outlines, "Add");
Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", outlined]);
var addOutline = Path.Combine(outlines, "AddProof.lean");
var written = Execute([.. cli, "new-proof", outlined, addOutline]);
if (written.Code != 0 || !written.Stdout.StartsWith("Wrote ") ||
    !written.Stdout.Contains("Holes: 3 obligations, 0 paths not outlined"))
    throw new InvalidOperationException("new-proof did not write the Add outline: " + written.Output);
var outlineText = File.ReadAllText(addOutline);
var refusedOutline = Execute([.. cli, "verify", outlined, "--proof", addOutline]);
if (refusedOutline.Code == 0 || !refusedOutline.Output.Contains("Unapproved proof axioms: sorryAx") ||
    refusedOutline.Output.Contains(": error"))
    throw new InvalidOperationException("The unedited Add outline was not refused for its holes alone: " +
        refusedOutline.Output);
var overwrite = Execute([.. cli, "new-proof", outlined, addOutline]);
if (overwrite.Code == 0 || !overwrite.Stderr.Contains("already exists; new-proof never overwrites a proof") ||
    File.ReadAllText(addOutline) != outlineText)
    throw new InvalidOperationException("new-proof replaced an existing file: " + overwrite.Output);
var packet = Path.Combine(outlines, "Packet");
Run([.. cli, "extract", demoAssembly, "Arguments::Struct(Examples.Packet)", packet]);
var packetOutline = Path.Combine(outlines, "PacketProof.lean");
var packetOutlined = Execute([.. cli, "new-proof", packet, packetOutline]);
if (packetOutlined.Code != 0 || !File.ReadAllText(packetOutline).Contains("Vector (BitVec 8) 12") ||
    !packetOutlined.Stdout.Contains("0 paths not outlined"))
    throw new InvalidOperationException("new-proof did not bind a struct parameter: " + packetOutlined.Output);
File.AppendAllText(Path.Combine(outlined, "Extracted.lean"), "\n-- edited\n");
var staleOutline = Path.Combine(outlines, "StaleProof.lean");
var staleOutlined = Execute([.. cli, "new-proof", outlined, staleOutline]);
if (staleOutlined.Code == 0 || File.Exists(staleOutline) ||
    !staleOutlined.Stderr.Contains("Stage: extraction integrity"))
    throw new InvalidOperationException("new-proof outlined a stale extraction: " + staleOutlined.Output);
Console.WriteLine("PASS CLI new-proof outline is refused until filled and never overwrites or guesses");

// Consumers pin the framework from this report, so it must name the commit the tool was built from.
var version = Execute([.. cli, "--version"]);
var head = Execute(["git", "-C", Root, "rev-parse", "HEAD"]).Stdout.Trim();
if (version.Code != 0 || !version.Stdout.Contains($"LeanCIL revision: {head}") ||
    !version.Stdout.Contains($"rev = \"{head}\"") ||
    !version.Stdout.Contains("Lean toolchain: " + File.ReadAllText(At("lean-toolchain")).Trim()))
    throw new InvalidOperationException("Version report does not name the built revision: " + version.Output);
Console.WriteLine("PASS CLI version names the framework revision and toolchain");

// A user checks `leancil --version` against the package they installed, so a development pack reports
// its own prerelease version rather than the version prefix it was stamped from.
if (args.Length == 0)
{
    var packages = Path.Combine(output, "packages");
    if (Directory.Exists(packages)) Directory.Delete(packages, true);
    Run(["dotnet", "pack", At("Extractor"), "-c", "Release", "-o", packages], progress: "CLI development pack");
    var package = Directory.GetFiles(packages, "Nethermind.LeanCIL.*.nupkg").Single();
    var packageVersion = Path.GetFileNameWithoutExtension(package)["Nethermind.LeanCIL.".Length..];
    var unpacked = Path.Combine(packages, "unpacked");
    System.IO.Compression.ZipFile.ExtractToDirectory(package, unpacked);
    var packedVersion = Execute(["dotnet", Path.Combine(unpacked, "tools/net10.0/any/Nethermind.LeanCIL.dll"),
        "--version"]);
    var reported = packedVersion.Stdout.ReplaceLineEndings("\n").Split('\n')[0];
    if (packedVersion.Code != 0 || !packageVersion.Contains("-dev.") || reported != "leancil " + packageVersion)
        throw new InvalidOperationException(
            $"A development pack of {packageVersion} reports another version: " + packedVersion.Output);
    Console.WriteLine("PASS CLI version of a development pack is the package version");
}

if (args.Length == 0)
    Run(["dotnet", "run", "--file", At("Tests/CliImportedKernelAudit.cs")],
        streamOutput: true, progress: "CLI imported helper kernel audit");

// A golden report pins every field a tool reads; paths and hashes vary by machine and are named instead.
static void RequireReport((int Code, string Output, string Stdout, string Stderr) run, int code, string golden,
    params (string Path, string Name)[] paths)
{
    var report = JsonNode.Parse(run.Stdout) as JsonObject;
    if (run.Code != code || WithoutStageProgress(run.Stderr).Length != 0 || report?["schema"]?.GetValue<int>() != 1)
        throw new InvalidOperationException($"verify --format json did not exit {code} with one report: " + run.Output);
    var actual = Normalized(report, paths)!.ToJsonString(new JsonSerializerOptions
    {
        WriteIndented = true, Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping
    }).ReplaceLineEndings("\n") + "\n";
    var expected = At("Tests/CliReports/" + golden);
    if (File.Exists(expected) && File.ReadAllText(expected).ReplaceLineEndings("\n") == actual) return;
    var written = At("artifacts/CliReports/" + golden);
    Directory.CreateDirectory(Path.GetDirectoryName(written)!);
    File.WriteAllText(written, actual);
    throw new InvalidOperationException($"verify --format json differs from Tests/CliReports/{golden}; see {written}");
}

static JsonNode? Normalized(JsonNode? node, (string Path, string Name)[] paths) => node switch
{
    JsonObject entries => new JsonObject(entries.Select(entry =>
        KeyValuePair.Create(entry.Key, Normalized(entry.Value, paths)))),
    JsonArray items => new JsonArray([.. items.Select(item => Normalized(item, paths))]),
    JsonValue value when value.TryGetValue<string>(out var text) => JsonValue.Create(Named(text, paths)),
    _ => node?.DeepClone()
};

static string Named(string text, (string Path, string Name)[] paths) =>
    // A longer path first, since a proof inside the output directory starts with the output's path.
    System.Text.RegularExpressions.Regex.Replace(paths.Select(path => (Full: Path.GetFullPath(path.Path), path.Name))
        .OrderByDescending(path => path.Full.Length).Aggregate(text, (current, path) =>
            current.Replace(path.Full, path.Name).Replace(path.Full.Replace('\\', '/'), path.Name)),
        @"\b[0-9a-f]{64}\b", "<sha256>");

// A test edit that no longer applies would test the unedited proof.
static string Edited(string text, string original, string replacement) =>
    text.Contains(original, StringComparison.Ordinal) ? text.Replace(original, replacement)
        : throw new InvalidOperationException("The proof no longer contains: " + original);

// Editors, terminals and problem matchers follow a diagnostic's path, so a failed proof must cite the file the
// developer edits, never the deleted workspace copy, and print each Lean error once.
static void RequireSourceLocations(string stderr, string location)
{
    var text = stderr.ReplaceLineEndings("\n");
    var headers = text.Split('\n').Where(line => line.StartsWith("  ", StringComparison.Ordinal) &&
        !line.StartsWith("   ", StringComparison.Ordinal) && line.Contains(".lean:", StringComparison.Ordinal) &&
        !line.Contains(": info:", StringComparison.Ordinal)).ToArray();
    if (!text.Contains("Lean errors (", StringComparison.Ordinal) || headers.Length == 0 ||
        !headers.Any(header => header.TrimStart().StartsWith(location, StringComparison.Ordinal)) ||
        headers.Distinct().Count() != headers.Length ||
        System.Text.RegularExpressions.Regex.IsMatch(text, @"proof-[0-9a-f]{32}") ||
        text.Contains("LeanCILProof", StringComparison.Ordinal) ||
        text.Contains("leancil-consumer-", StringComparison.Ordinal) ||
        text.Contains(Path.GetTempPath().TrimEnd(Path.DirectorySeparatorChar), StringComparison.OrdinalIgnoreCase) ||
        text.Contains("Command failed", StringComparison.Ordinal))
        throw new InvalidOperationException(
            $"A failed proof did not cite {location} once, or named a temporary copy:\n{stderr}");
}
