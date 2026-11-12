#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

using System.Diagnostics;
using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

var cli = args.Length == 0
    ? new[] { "dotnet", At("Extractor/bin/Nethermind.LeanCIL.dll") }
    : new[] { Path.GetFullPath(args[0]) };
var output = At("artifacts/CliVerification");
var assembly = At("Examples/Assembly/bin/Examples.dll");
var proof = At("Examples/Proofs/Add.lean");
var settingsPath = Path.Combine(output, "verification.json");

// A run that does not exit as expected is reported with the tool's own output, not as the report file or
// JSON it never wrote.
var refused = (Code: 1, Output: "Invalid: boom\n  Stage: proof checking\n", Stdout: "", Stderr: "Invalid: boom\n");
if (FailureOf(() => Exited(refused, 0)) is not { } refusedMessage || !refusedMessage.Contains("exit code 0") ||
    !refusedMessage.Contains("got 1") || !refusedMessage.Contains("Invalid: boom\n  Stage: proof checking"))
    throw new InvalidOperationException("A run that failed was not reported with the tool's output.");

// Every assertion below runs against a prepared certified library, as CI supplies one, so the notices a
// first run prints while it builds the library never reach the stderr checks.
if (string.IsNullOrWhiteSpace(Environment.GetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY")))
{
    var preparedLibrary = At("artifacts/CliCertifiedLibrary");
    if (Directory.Exists(preparedLibrary)) DeleteTree(preparedLibrary);
    using var producer = new Program();
    producer.PrepareCertifiedFingerprints();
    Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY_SHA256", producer.PrepareLibrary(preparedLibrary));
    Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY", preparedLibrary);
}

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

// The prepared library serves a verification whose cache holds nothing: no notice on stderr, and no
// library built into the cache.
var emptyCache = At("artifacts/CliEmptyCache");
if (Directory.Exists(emptyCache)) DeleteTree(emptyCache);
var cold = Exited(Execute([.. cli, "verify", output], environment: new Dictionary<string, string>
    { ["LEANCIL_CACHE_DIR"] = emptyCache }), 0);
if (WithoutStageProgress(cold.Stderr).Length != 0 || !cold.Stdout.StartsWith("Verified: ExampleProof.correctness") ||
    // A library entry is a directory named by its key; only the verification results live beside it.
    Directory.Exists(emptyCache) &&
    Directory.EnumerateDirectories(emptyCache).Any(entry => Path.GetFileName(entry) != "success-v1"))
    throw new InvalidOperationException("A verification with an empty cache built or announced a library: " +
        cold.Output);
Console.WriteLine("PASS CLI verification with an empty library cache prints no first-run notice");

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
// The failure says how to see the goals, and `--goals` prints the goal before the tactic that failed in
// place of the proof's messages, which stay in their file.
const string GoalsHint = "  Goals: add --goals to print the goal at each `sorry` and failing tactic.\n";
var rejectedGoals = Execute([.. cli, "verify", output, "--goals"]);
var rejectedGoalsText = rejectedGoals.Stderr.ReplaceLineEndings("\n");
if (!rejected.Stderr.ReplaceLineEndings("\n").Contains(GoalsHint) || rejectedGoals.Code != 1 ||
    rejectedGoals.Stdout.Length != 0 || !rejectedGoalsText.Contains("  Stage: proof checking\n") ||
    rejectedGoalsText.Contains(GoalsHint) || !rejectedGoalsText.Contains("  Goals (1):\n") ||
    !Regex.IsMatch(rejectedGoalsText, @"^    Examples/Proofs/Add\.lean:\d+:\d+: failing tactic$",
        RegexOptions.Multiline) ||
    !rejectedGoalsText.Contains("      ⊢ Except.map Prod.snd") || rejectedGoalsText.Contains(": info: ") ||
    !rejectedGoalsText.Contains("  Lean messages (1): artifacts/CliVerification/proof-messages.txt\n") ||
    !File.ReadAllText(Path.Combine(output, "proof-messages.txt")).Contains("depends on axioms"))
    throw new InvalidOperationException("verify --goals did not print the goal of the failing tactic: " +
        rejected.Stderr + rejectedGoals.Output);
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

// A loop proof missing its invariant reports the open obligation by its tag, and a path that misses its loop
// head reports the method, pc and instruction it reached and what differs, read from its failure record.
var loopOutput = At("artifacts/CliLoopReports");
Run([.. cli, "extract", demoAssembly, "Examples.Loops::Countdown(uint)", loopOutput]);
var countdown = File.ReadAllText(At("Examples/Proofs/Countdown.lean")).ReplaceLineEndings("\n");
var noInvariant = Path.Combine(loopOutput, "NoInvariant.lean");
File.WriteAllText(noInvariant, Edited(countdown, "    case invariant => trivial\n    case measure =>",
    "    case measure =>"));
RequireReport(Execute([.. cli, "verify", loopOutput, "--proof", noInvariant, "--format", "json"]), 1,
    "MissingInvariant.json", (loopOutput, "<output>"), (noInvariant, "<proof>"));
// The span drain checks its entry path against a stated loop head, whose stack the edit misstates.
var spanOutput = At("artifacts/CliSpanReports");
Run([.. cli, "extract", demoAssembly, "Examples.Loops::Drain(System.ReadOnlySpan`1<System.Int32>)", spanOutput]);
var wrongHead = Path.Combine(spanOutput, "WrongHead.lean");
File.WriteAllText(wrongHead, Edited(File.ReadAllText(At("Examples/Proofs/SpanDrain.lean")).ReplaceLineEndings("\n"),
    "(BitVec.ofNat 32 state.val.length))], memory", "(BitVec.ofNat 32 (state.val.length + 1)))], memory"));
RequireReport(Execute([.. cli, "verify", spanOutput, "--proof", wrongHead, "--format", "json"]), 1,
    "LoopHeadMismatch.json", (spanOutput, "<output>"), (wrongHead, "<proof>"));
// The record is requested only by `--format json`; the default report is the error alone.
var wrongHeadText = Execute([.. cli, "verify", spanOutput, "--proof", wrongHead]);
if (wrongHeadText.Code != 1 || !wrongHeadText.Stderr.Contains("cil_loop_steps: target state not matched at pc 7") ||
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
    !tracedText.Contains("Countdown.lean:30:4: [CIL.step] pc 0: CIL.Instruction.arg 0\n") ||
    !tracedText.Contains("[CIL.step] cil_loop_finish took ") || tracedMessages.Contains("[CIL.step]") ||
    // Each tactic reports its step count once, at its own position.
    tracedText.Split("Countdown.lean:30:4: [CIL.step] cil_loop_recurse took ").Length != 2)
    throw new InvalidOperationException("verify --trace did not report the steps apart: " + traced.Output);
var tracedReport = JsonNode.Parse(Exited(Execute([.. cli, "verify", loopOutput, "--proof", countdownProof, "--trace",
    "--format", "json"]), 0).Stdout) as JsonObject;
var steps = tracedReport?["trace"]?.AsArray().Select(step => step!["text"]!.GetValue<string>()).ToArray() ?? [];
if (steps.Length == 0 || !steps.All(step => step.StartsWith("[CIL.step] ", StringComparison.Ordinal)) ||
    tracedReport!["unknown"]!.AsObject().ContainsKey("trace") ||
    tracedReport["messages"]!.AsArray().Any(message => message!["text"]!.GetValue<string>().Contains("[CIL.step]")))
    throw new InvalidOperationException("verify --trace --format json did not report the steps in `trace`: " +
        tracedReport?.ToJsonString());
var untraced = Execute([.. cli, "verify", loopOutput, "--proof", countdownProof]);
if (untraced.Code != 0 || untraced.Stdout.Contains("[CIL.step]") || untraced.Stdout.Contains("Trace ("))
    throw new InvalidOperationException("verify without --trace printed a trace: " + untraced.Output);
Console.WriteLine("PASS CLI --trace reports each step apart from the proof's messages, and only when asked");

// A proof stuck on a class instance names the object evidence it lacks: the entry of `DepositBoth` checks each
// account argument before its `callvirt` can throw, so an account the statement says nothing of stops it.
var objectOutput = At("artifacts/CliObjectReports");
Run([.. cli, "extract", demoAssembly, "Examples.Objects::DepositBoth(Examples.Account,Examples.Account,ulong)",
    objectOutput]);
var depositBothProof = At("Examples/Proofs/DepositBoth.lean");
var unformed = Path.Combine(objectOutput, "UnformedAccount.lean");
File.WriteAllText(unformed, Edited(File.ReadAllText(depositBothProof).ReplaceLineEndings("\n"),
    " (amount : W64)\n    (secondLive : LiveObject memory second) :\n", " (amount : W64) :\n"));
RequireReport(Execute([.. cli, "verify", objectOutput, "--proof", unformed, "--theorem",
    "ExampleProof.first_null_throws", "--format", "json"]), 1, "UnformedAccount.json", (objectOutput, "<output>"),
    (unformed, "<proof>"));
// The trace shows the receiver-checked call and the exception it throws on a null receiver.
var objectTrace = Exited(Execute([.. cli, "verify", objectOutput, "--proof", depositBothProof, "--theorem",
    "ExampleProof.first_null_throws", "--trace"]), 0).Stdout.ReplaceLineEndings("\n");
if (!objectTrace.Contains("[CIL.step] pc 2: CIL.Instruction.callInstance 1 2\n") ||
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
    var fixtureImport = Exited(Execute([.. cli, "verify", auditOutput, "--proof", fixtureProof]), 1);
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
var helper = Exited(Execute([.. cli, "verify", subjectOutput, "--proof", subjectProof, "--theorem",
    "ExampleProof.helper"]), 0).Stdout.ReplaceLineEndings("\n");
if (!helper.Contains($"  Subject: {addTwo}\n") || !helper.Contains($"  Premise: {addTwo}\n") ||
    helper.Contains("Subject: System.UInt32 Examples.Loops::TallyTwice") ||
    !helper.Contains("  Extraction entry: System.UInt32 Examples.Loops::TallyTwice(System.UInt32)\n"))
    throw new InvalidOperationException("Helper theorem was not labelled by its subject: " + helper);
var unfixed = Exited(Execute([.. cli, "verify", subjectOutput, "--theorem", "ExampleProof.unfixed"]), 0)
    .Stdout.ReplaceLineEndings("\n");
if (!unfixed.Contains("  Subject: a method index the statement does not fix via CIL.Safety.MethodContract.Holds\n") ||
    unfixed.Contains("Examples.Loops::AddTwo") || unfixed.Contains("Subject: System.UInt32"))
    throw new InvalidOperationException("An unfixed method index was labelled as a specific method: " + unfixed);
Console.WriteLine("PASS CLI labels a theorem by the methods its statement names");

// A reviewer reads what was proved from the report: the proof's own definitions the statement names are
// printed from their elaborated bodies and recorded in the certificate, so changing one changes both.
var specificationOutput = At("artifacts/CliSpecification");
Run([.. cli, "extract", demoAssembly, "Arithmetic::Add(ulong,ulong)", specificationOutput]);
var specifiedProof = Path.Combine(specificationOutput, "Specified.lean");
const string SumText = "def ExampleProof.Sum (x y : CIL.W64) : Nat := (BitVec.toNat x + BitVec.toNat y) % 2 ^ 64";
foreach (var (postcondition, evidence, printed) in new[]
    {
        ("result.toNat = Sum x y", "BitVec.toNat_add x y", "BitVec.toNat result = ExampleProof.Sum x y"),
        ("Sum x y = result.toNat", "(BitVec.toNat_add x y).symm", "ExampleProof.Sum x y = BitVec.toNat result")
    })
{
    File.WriteAllText(specifiedProof, $$"""
        import Extracted

        open CIL
        namespace ExampleProof

        def Sum (x y : W64) : Nat := (x.toNat + y.toNat) % 2^64

        def Postcondition (x y result : W64) : Prop := {{postcondition}}

        def unused : Nat := 0

        theorem correctness (x y : W64) :
            ∃ result : W64,
              (CIL.Safety.invoke Extracted.program 4 0
                [.scalar (.i64 x), .scalar (.i64 y)] Safety.Memory.empty).map Prod.snd =
                  .ok [.scalar (.i64 result)] ∧
              Postcondition x y result := by
          refine ⟨x + y, ?_, {{evidence}}⟩
          rfl

        #print axioms correctness
        end ExampleProof
        """);
    var postconditionText =
        $"def ExampleProof.Postcondition (x y result : CIL.W64) : Prop := {printed}";
    // The second run reuses the checked proof, which carries the specification with its statement.
    foreach (var reuse in new[] { false, true })
    {
        var specified = Exited(Execute([.. cli, "verify", specificationOutput, "--proof", specifiedProof]), 0);
        var recorded = JsonNode.Parse(File.ReadAllText(Path.Combine(specificationOutput, "verified.json")))!
            ["specification"]?.AsArray().Select(definition =>
                (definition!["name"]!.GetValue<string>(), definition["text"]!.GetValue<string>())).ToArray() ?? [];
        if (specified.Code != 0 || !specified.Stdout.ReplaceLineEndings("\n").Contains(
                $"  Specification:\n    {postconditionText}\n    {SumText}\n  Lean messages") ||
            specified.Stdout.Contains("unused") || !recorded.SequenceEqual(
                [("ExampleProof.Postcondition", postconditionText), ("ExampleProof.Sum", SumText)]))
            throw new InvalidOperationException(
                $"The report does not show the specification the theorem uses (reused: {reuse}): " +
                specified.Output + string.Join('\n', recorded));
    }
    var specifiedJson = JsonNode.Parse(Exited(Execute([.. cli, "verify", specificationOutput, "--proof",
        specifiedProof, "--format", "json"]), 0).Stdout)?["specification"]?.AsArray();
    if (specifiedJson is not { Count: 2 } || specifiedJson[0]!["text"]!.GetValue<string>() != postconditionText)
        throw new InvalidOperationException("verify --format json does not report the specification: " +
            specifiedJson?.ToJsonString());
}
Console.WriteLine("PASS CLI prints and records the specification a theorem is stated with, and a changed one");

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
    var consumer = Exited(Execute([.. cli, "verify", consumerOutput, "--proof", consumerProof,
        "--proof-root", consumerPackage, .. options]), 0);
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
// The failed package check reaches a reader that expected it to pass as the tool's output, not as a missing report.
if (FailureOf(() => Exited(unfinished, 0)) is not { } unfinishedFailureText ||
    !unfinishedFailureText.Contains("got 1") || !unfinishedFailureText.Contains("Stage: proof checking"))
    throw new InvalidOperationException("A failed --proof-root check was not reported with the tool's output.");
// A package's proof shows its goals as a standalone one does.
var unfinishedGoals = Execute([.. cli, "verify", consumerOutput, "--proof", unfinishedProof,
    "--proof-root", consumerPackage, "--goals"]).Stderr.ReplaceLineEndings("\n");
if (!unfinishedGoals.Contains("  Goals (1):\n" +
        "    artifacts/CliConsumer/Package/Proofs/Unfinished.lean:5:2: failing tactic\n      ⊢ False\n") ||
    unfinishedGoals.Contains("[LeanCIL goal"))
    throw new InvalidOperationException("verify --goals did not print a --proof-root proof's goal: " +
        unfinishedGoals);
// A hole in a package's proof is reported as open goals too, although the package's audit refuses it first.
var holeProof = Path.Combine(consumerPackage, "Proofs", "Hole.lean");
File.WriteAllText(holeProof, "import Extracted\ntheorem ExampleProof.correctness : 1 + 1 = 2 := by\n  sorry\n");
var hole = Execute([.. cli, "verify", consumerOutput, "--proof", holeProof, "--proof-root", consumerPackage,
    "--goals"]);
var holeText = hole.Stderr.ReplaceLineEndings("\n");
if (hole.Code != 1 ||
    !holeText.StartsWith("Invalid: 1 goal remains in artifacts/CliConsumer/Package/Proofs/Hole.lean.\n") ||
    !holeText.Contains("  Stage: open goals\n") || !holeText.Contains("  Goals (1):\n" +
        "    artifacts/CliConsumer/Package/Proofs/Hole.lean:3:2: sorry\n      ⊢ 1 + 1 = 2\n") ||
    JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(consumerOutput, "failed.json")))
        .GetProperty("kind").GetString() != "unsolved-goal")
    throw new InvalidOperationException("verify --goals did not report a --proof-root proof's hole as an open " +
        "goal: " + hole.Output);
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
// `--goals` prints the goal at each hole, once each in source order and without the proof's warnings, and
// stops before replay and audit, so it answers sooner than the verification that refuses the file.
var holes = Regex.Matches(outlineText.ReplaceLineEndings("\n"), @"(?<=:= |=> |^\s+)sorry\b", RegexOptions.Multiline)
    .Select(hole => outlineText.ReplaceLineEndings("\n")[..hole.Index].Split('\n'))
    .Select(before => (Line: before.Length, Column: before[^1].Length)).ToArray();
var refusal = Stopwatch.StartNew();
Execute([.. cli, "verify", outlined, "--proof", addOutline]);
refusal.Stop();
var answer = Stopwatch.StartNew();
var outlineGoals = Execute([.. cli, "verify", outlined, "--proof", addOutline, "--goals"]);
answer.Stop();
var outlineGoalsText = outlineGoals.Stderr.ReplaceLineEndings("\n");
var reportedHoles = Regex.Matches(outlineGoalsText, @"^    \S*AddProof\.lean:(\d+):(\d+): sorry$",
        RegexOptions.Multiline)
    .Select(goal => (Line: int.Parse(goal.Groups[1].Value), Column: int.Parse(goal.Groups[2].Value))).ToArray();
if (outlineGoals.Code != 1 || outlineGoals.Stdout.Length != 0 || holes.Length != 3 ||
    !reportedHoles.SequenceEqual(holes) || !outlineGoalsText.Contains("  Stage: open goals\n") ||
    !outlineGoalsText.StartsWith("Invalid: 3 goals remain in artifacts/CliOutline/AddProof.lean.\n") ||
    !outlineGoalsText.Contains("  Goals (3):\n") || !outlineGoalsText.Contains("      ⊢ Prop\n") ||
    outlineGoalsText.Contains("warning") || outlineGoalsText.Contains("Hint") ||
    outlineGoalsText.Contains("[LeanCIL goal") || File.Exists(Path.Combine(outlined, "verified.json")))
    throw new InvalidOperationException("verify --goals did not print one goal per hole in source order: " +
        outlineGoals.Output);
if (answer.Elapsed >= refusal.Elapsed)
    throw new InvalidOperationException($"verify --goals took {answer.Elapsed.TotalSeconds:F1}s, no less than " +
        $"the {refusal.Elapsed.TotalSeconds:F1}s of the verification that refuses the outline.");
var outlineGoalsJson = JsonNode.Parse(Exited(Execute([.. cli, "verify", outlined, "--proof", addOutline, "--goals",
    "--format", "json"]), 1).Stdout) as JsonObject;
var jsonGoals = outlineGoalsJson?["goals"]?.AsArray();
if (outlineGoalsJson?["result"]?.GetValue<string>() != "failed" ||
    outlineGoalsJson["stage"]?.GetValue<string>() != "open goals" ||
    outlineGoalsJson["failures"]?[0]?["kind"]?.GetValue<string>() != "unsolved-goal" ||
    jsonGoals is not { Count: 3 } || jsonGoals.Any(goal => goal!["kind"]!.GetValue<string>() != "sorry") ||
    !jsonGoals.Select(goal => (goal!["line"]!.GetValue<int>(), goal["column"]!.GetValue<int>())).SequenceEqual(holes) ||
    !jsonGoals[0]!["goal"]!.GetValue<string>().Contains("⊢ Prop") ||
    outlineGoalsJson["messages"]!.AsArray().Any(message =>
        message!["text"]!.GetValue<string>().Contains("[LeanCIL goal")) ||
    !outlineGoalsJson["rerun"]!.AsArray().Any(argument => argument!.GetValue<string>() == "--goals"))
    throw new InvalidOperationException("verify --goals --format json did not report each hole's goal: " +
        outlineGoalsJson?.ToJsonString());
Console.WriteLine($"PASS CLI --goals prints one goal per hole in source order in {answer.Elapsed.TotalSeconds:F1}s, " +
    $"under the {refusal.Elapsed.TotalSeconds:F1}s of the refused verification, and the goal of a failing tactic");
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

// A run that exited otherwise has not written the report the caller reads next, so its own output is what
// the failure must carry.
static (int Code, string Output, string Stdout, string Stderr) Exited(
    (int Code, string Output, string Stdout, string Stderr) run, int code) =>
    run.Code == code ? run
        : throw new InvalidOperationException($"Expected exit code {code}, got {run.Code}: " + run.Output);

static string? FailureOf(Action action)
{
    try { action(); return null; }
    catch (InvalidOperationException error) { return error.Message; }
}

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
