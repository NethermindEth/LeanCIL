#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Verification.cs
#:include LeanDiagnostics.cs
#:include FailureReports.cs
#:include VerifyReports.cs

static void Require(bool condition, string message, string? text = null)
{
    if (!condition)
        throw new InvalidOperationException(
            "Lean diagnostic summary regression: " + message + (text is null ? "" : "\n" + text));
}

// Shape of a failing `lake build +LeanCILProof:olean`: replayed modules print axiom
// reports and traces; the errors sit near the end between unrelated entries.
var replayed = string.Concat(Enumerable.Range(0, 400).Select(i =>
    $"\u2139 [{i}/420] Replayed CIL.Module{i}\n" +
    $"info: CIL/Module{i}.lean:3:0: 'CIL.lemma{i}' depends on axioms: [propext, Quot.sound]\n"));
const string failed = "\u2716";
var transcript = "Command failed (1): lake build +LeanCILProof:olean\n" + replayed + $"""
    {failed} [418/420] Building Client.Shared (2.1s)
    trace: .> LEAN_PATH=D:\work\.lake\build\lib\lean lean.exe D:\work\Client\Shared.lean -o D:\work\Shared.olean
    error: Client/Shared.lean:7:43: Tactic `rfl` failed: The left-hand side
      CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i64 x), .scalar (.i64 y)] memory
    is not definitionally equal to the right-hand side
      .ok (memory, [.scalar (.i64 (x - y))])

    error: Client/Shared.lean:9:0: unknown identifier 'missing'
    warning: Client/Shared.lean:11:0: declaration uses 'sorry'
    error: Lean exited with code 1
    {failed} [419/420] Building LeanCILProof1 (1.0s)
    error: LeanCILProof1.lean:4:2: unsolved goals of another request
    {failed} [420/420] Building LeanCILProof0 (1.0s)
    error: LeanCILProof0.lean:5:2: Application type mismatch: The argument
      rfl
    has type
      ?m.35 = ?m.35
    but is expected to have type
      Extracted.program[2]? = some (Full.fullBody Extracted.profile 9 5 7)
    error: D:\work\Generated.lean:1:0: Windows drive paths keep their location
    Some required targets logged failures:
    - Client.Shared
    - LeanCILProof0
    error: build failed
    """;

var errors = LeanDiagnostics.Errors(transcript, ["LeanCILProof1"]);
Require(errors.Count == 4, "expected the four located errors of the failing modules", string.Join("\n", errors));
Require(errors[0].Module == "Client.Shared" && errors[0].Location == "Client/Shared.lean:7:43",
    "location or module of the first error");
// The whole message block is kept, including unindented continuation lines.
Require(errors[0].Lines.Count == 4 && errors[0].Lines[3] == "  .ok (memory, [.scalar (.i64 (x - y))])",
    "first message block", string.Join("\n", errors[0].Lines));
Require(errors[1].Lines.Count == 1 && errors[1].Lines[0] == "unknown identifier 'missing'",
    "second block stops at the next entry");
Require(errors[2].Module == "LeanCILProof0" && errors[2].Lines[^1].Contains("Full.fullBody", StringComparison.Ordinal),
    "proof module block");
Require(errors[3].Location == @"D:\work\Generated.lean:1:0", "drive-letter location");
Require(errors.All(error => error.Module != "LeanCILProof1"), "other requests' proof modules are omitted");

var summary = LeanDiagnostics.Summarize(transcript, ["LeanCILProof1"])!.Text;
const string SummaryHeader =
    "Lean errors (4):\n  Client/Shared.lean:7:43 (building Client.Shared)\n    Tactic `rfl` failed";
Require(summary.StartsWith(SummaryHeader, StringComparison.Ordinal), "summary header", summary);
string[] omitted = ["depends on axioms", "trace:", "declaration uses 'sorry'", "Lean exited", "build failed"];
Require(omitted.All(text => !summary.Contains(text, StringComparison.Ordinal)),
    "summary carries only error diagnostics", summary);
Require(summary.Split('\n').Length < 25 && transcript.Split('\n').Length > 800,
    "summary is bounded relative to the transcript", summary);
Require(LeanDiagnostics.Summarize(transcript)!.Text.Contains("unsolved goals of another request",
        StringComparison.Ordinal),
    "a lone request keeps every module");

// Direct `lean` output uses the location-first format.
var direct = LeanDiagnostics.Errors("Batch.lean:3:4: error: type mismatch\n  h\nBatch.lean:9:0: warning: unused\n");
Require(direct.Count == 1 && direct[0].Location == "Batch.lean:3:4" && direct[0].Lines.Count == 2,
    "location-first format");

// Pathological messages are truncated in the summary only.
var goalLines = string.Concat(Enumerable.Range(0, 500).Select(i => $"goal line {i} " + new string('x', 1000) + "\n"));
var huge = "error: P.lean:1:0: unsolved goals\n" + goalLines +
    string.Concat(Enumerable.Range(0, 30).Select(i => $"error: P.lean:{i + 2}:0: e{i}\n"));
var boundedReport = LeanDiagnostics.Summarize(huge)!;
var bounded = boundedReport.Text;
var moreLines = $"... {501 - LeanDiagnostics.MaxLines} more lines under Details";
var moreErrors = $"... {31 - LeanDiagnostics.MaxErrors} more errors under Details";
Require(bounded.Contains(moreLines, StringComparison.Ordinal) &&
    bounded.Contains(moreErrors, StringComparison.Ordinal) &&
    bounded.Split('\n').All(line => line.Length <= LeanDiagnostics.MaxLineLength + 8),
    "truncation", bounded[..2000]);
// Each error is printed once: in full in the summary, or in full among the shortened errors.
var shortened = boundedReport.Shortened.Split('\n');
Require(shortened.Contains("P.lean:1:0") && shortened.Contains("goal line 499 " + new string('x', 1000)) &&
    !shortened.Contains("P.lean:2:0") && !shortened.Contains("e18") && shortened.Contains("P.lean:21:0") &&
    shortened.Contains("e29") && !bounded.Contains("e29", StringComparison.Ordinal),
    "shortened errors hold exactly the cut and omitted errors in full", boundedReport.Shortened[^200..]);
var copies = Path.Combine(Path.GetTempPath(), "leancil-copies-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(copies);
try
{
    var original = Path.Combine(copies, "Original.lean");
    var copy = Path.Combine(copies, "session", "Proof.lean");
    Directory.CreateDirectory(Path.GetDirectoryName(copy)!);
    File.WriteAllText(original, "theorem t : True := trivial\n");
    File.Copy(original, copy);
    var copySession = new SourceCopies(Path.GetDirectoryName(copy)!);
    Require(copySession.Add(copy, original) && copySession.Locate("Proof.lean:1:8") == original + ":1:8" &&
        copySession.Locate(copy + ":1:8") == original + ":1:8" &&
        copySession.Locate("Other.lean:1:8") == "Other.lean:1:8",
        "a recorded copy is cited by its original, relative or absolute, and other files keep their path");
    File.AppendAllText(copy, "-- edited\n");
    var changed = new SourceCopies(Path.GetDirectoryName(copy)!);
    Require(!changed.Add(copy, original) && changed.Locate("Proof.lean:1:8") == "Proof.lean:1:8",
        "a copy whose bytes differ is never mapped, since its lines would not be the original's");

    // The observed copy differs only by an import at the start of the first import line; every position maps back.
    File.WriteAllText(original, "/-! Proof. -/\nimport CIL\nimport Extracted\n\ntheorem t : True := trivial\n");
    var observed = ObservedProof.Insert(File.ReadAllBytes(original));
    Require(observed.Line == 2 && System.Text.Encoding.UTF8.GetString(observed.Bytes) ==
        "/-! Proof. -/\nimport CIL.Observe import CIL\nimport Extracted\n\ntheorem t : True := trivial\n",
        "the observer import starts the first import line and adds no line");
    File.WriteAllBytes(copy, observed.Bytes);
    var observedSession = new SourceCopies(Path.GetDirectoryName(copy)!);
    Require(!observedSession.Add(copy, original) && observedSession.AddObserved(copy, original) &&
        observedSession.Locate("Proof.lean:2:26") == original + ":2:7" &&
        observedSession.Locate("Proof.lean:2:3") == original + ":2:0" &&
        observedSession.Locate("Proof.lean:5:8") == original + ":5:8",
        "positions on the import line move back past the inserted import, and other lines keep theirs");
    var located = observedSession.Relocate(original, [
        new("info", 2, 26, "plain"),
        new("info", 5, 0, Program.FailureMarker + "{\"error\":{\"line\":2,\"column\":19},\"tactic\":\"t\"}")])!;
    Require(located[0] == new Program.ProofMessage("info", 2, 7, "plain") && located[1].column == 0 &&
        VerifyReports.Record(located[1].text)!["error"]!["column"]!.GetValue<int>() == 0,
        "messages and the errors their records cite are read in the original", string.Join("\n", located));
    File.AppendAllText(copy, "-- edited\n");
    Require(!new SourceCopies(Path.GetDirectoryName(copy)!).AddObserved(copy, original),
        "an observed copy with any other change is never mapped");

    // A failure with no Lean error prints its command; the deleted workspace never appears in it.
    var workspace = Path.GetDirectoryName(copy)!;
    var command = $"Command failed (1): lean --json --root={workspace} -o {Path.Combine(workspace, "Proof.olean")} " +
        $"{copy}\nPANIC at lean";
    var shown = observedSession.Displayed(command);
    Require(!shown.Contains(workspace, StringComparison.OrdinalIgnoreCase) && !shown.Contains("--root") &&
        shown.Contains(SourceCopies.Workspace) && shown.Contains("PANIC at lean"),
        "details show no path of the deleted workspace", shown);
}
finally { Directory.Delete(copies, true); }

Require(LeanDiagnostics.Summarize("Command failed (1): dotnet build\nerror CS1002: ; expected\n") is null,
    "non-Lean output has no summary");
Console.WriteLine("PASS Lean diagnostic summaries keep located error blocks of failing modules and stay bounded");

// A consumer session copies the package's sources and the request's proof; reports cite only those originals.
var work = Path.Combine(Path.GetTempPath(), "leancil-failures-" + Guid.NewGuid().ToString("N"));
var package = Path.Combine(work, "package");
var proof = Path.Combine(package, "Proofs", "Mix.lean");
var output = Path.Combine(work, "artifacts", "Mix");
var session = Path.Combine(work, "session");
var sessionCopies = new SourceCopies(session);
void Copied(string copy, string original)
{
    Directory.CreateDirectory(Path.GetDirectoryName(original)!);
    Directory.CreateDirectory(Path.GetDirectoryName(copy)!);
    if (!File.Exists(original)) File.WriteAllText(original, "-- " + Path.GetFileName(original) + "\n");
    File.Copy(original, copy, true);
    Require(sessionCopies.Add(copy, original), "a byte-identical copy is recorded");
}
Copied(Path.Combine(session, "Client", "Shared.lean"), Path.Combine(package, "Client", "Shared.lean"));
Copied(Path.Combine(session, "LeanCILProof.lean"), proof);
Copied(Path.Combine(session, "LeanCILProof0.lean"), proof);
FailureReports.Report Classify(string stage, string text, string[]? hidden = null, string? root = null) =>
    FailureReports.Classify(stage, text, hidden, "ExampleProof.correctness", proof, output, root ?? package,
        sessionCopies);
var goals = Classify("proof checking", transcript, ["LeanCILProof1"]);
Require(goals.kind == FailureReports.ElaborationError && goals.diagnostics.Length == 4 &&
    goals.diagnostics[0].module == "Client.Shared" &&
    goals.file == Path.Combine(package, "Client", "Shared.lean") && goals.line == 7 && goals.column == 43,
    "first error leads and keeps its package path");
Require(goals.diagnostics[2] is { kind: FailureReports.ElaborationError, module: "Proofs.Mix", line: 5, column: 2 } &&
    goals.diagnostics[2].file == proof && goals.message == transcript,
    "workspace proof copy maps to the request's proof, message verbatim");
var unsolved =
    Classify("proof checking", "error: LeanCILProof.lean:12:3: unsolved goals\nx : W64\n⊢ x * 3 + 1 = x * 3\n");
Require(unsolved is { kind: FailureReports.UnsolvedGoal, line: 12, column: 3, module: "Proofs.Mix" } &&
    unsolved.file == proof &&
    unsolved.diagnostics[0].message == "unsolved goals\nx : W64\n⊢ x * 3 + 1 = x * 3",
    "unsolved goal and its location");
var heartbeats = Classify("proof checking", "error: LeanCILProof.lean:8:0: (deterministic) timeout at `whnf`, " +
    "maximum number of heartbeats (1) has been reached\n");
Require(heartbeats is { kind: FailureReports.ResourceLimit, resource: "heartbeats", line: 8 }, "heartbeat limit");
var kernel = Classify("kernel replay", "error: LeanCILProof.lean:8:0: (kernel) deterministic timeout\n");
Require(kernel is { kind: FailureReports.ResourceLimit, resource: "heartbeats" },
    "kernel heartbeat limit precedes the stage");
var certificate = Classify("extraction certificate audit", "error: ExtractionAudit.lean:3:0: unsolved goals\n");
Require(certificate.kind == FailureReports.UnsupportedExtraction,
    "a rejected extraction certificate is unsupported extraction, not a proof goal");
var replay = Classify("kernel replay", "Kernel replay rejected Proofs.Mix:\n(kernel) declaration type mismatch");
Require(replay.kind == FailureReports.ReplayOrAuditRejected &&
    Classify("theorem audit", "Unapproved proof axioms: sorryAx").kind == FailureReports.ReplayOrAuditRejected,
    "replay and axiom audit");
const string CheckFailed = "Command failed (1): dotnet leancil check out\n";
var stale = Classify("extraction integrity", CheckFailed +
    "Invalid: Stale or mismatched verification artifact: assembly has changed since extraction.\n" +
    "  Stage: extraction integrity\n");
var unsupported = Classify("extraction integrity", CheckFailed +
    "Invalid: Unsupported opcode\n  Stage: metadata and CIL validation\n");
Require(stale is { kind: FailureReports.StaleInput, file: null, line: null } &&
    unsupported.kind == FailureReports.UnsupportedExtraction,
    "nested check stage separates stale artifacts from unsupported extraction");
Require(Classify("theorem audit", "Inputs changed during consumer verification").kind == FailureReports.StaleInput &&
    Classify("proof selection", "Proof file not found: P.lean").kind == FailureReports.InvalidRequest &&
    Classify("Lean library build", "Required command not found: lake").kind == FailureReports.Unclassified,
    "stage fallbacks");
var unrootedProof = Path.Combine(output, "proof-0123", "Proof.lean");
var directCopies = new SourceCopies(Path.GetDirectoryName(unrootedProof)!);
Directory.CreateDirectory(Path.GetDirectoryName(unrootedProof)!);
File.Copy(proof, unrootedProof);
Require(directCopies.Add(unrootedProof, proof), "the direct session's proof copy is recorded");
var unrooted = FailureReports.Classify("proof checking", unrootedProof + ":4:2: error: unsolved goals\n⊢ False\n",
    null, "ExampleProof.correctness", proof, output, null, directCopies);
var uncopied = FailureReports.Classify("proof checking", unrootedProof + ":4:2: error: unsolved goals\n⊢ False\n",
    null, "ExampleProof.correctness", proof, output, null);
Require(uncopied.file == unrootedProof, "a path the session did not record as a copy is never rewritten");
string[] expectedRerun = ["leancil", "verify", output, "--proof", proof, "--theorem", "ExampleProof.correctness"];
Require(unrooted is { kind: FailureReports.UnsolvedGoal, module: "Proof", line: 4, column: 2 } &&
    unrooted.file == proof && unrooted.rerun.SequenceEqual(expectedRerun),
    "unrooted proof copy and rerun");
const string Audit = "ExampleProof.correctness : ¬mixContract.Holds Extracted.program mix\n" +
    "'ExampleProof.correctness' depends on axioms: [propext]\n";
var refuted = FailureReports.Refuted(Audit + "LeanCIL refutes: CIL.Safety.MethodContract.Holds at 21:0\n",
    "ExampleProof.correctness", proof, output, package);
Require(refuted is { kind: FailureReports.Refutation, line: 21, column: 0, stage: "theorem audit" } &&
    refuted.file == proof && refuted.rerun[^2..].SequenceEqual(["--proof-root", package]),
    "verified refutation");
// The marker comes from the Lean audit only; statement text never makes a refutation.
Require(FailureReports.Refuted(Audit, "ExampleProof.correctness", proof, output, package) is null &&
    unsolved.kind != FailureReports.Refutation, "an unsolved goal or a negated statement alone is never a refutation");

// A build that Lake reports as successful while a tactic of the proof module read past the end of an array.
const string built = "\u2139";
var panicking = $"""
    {built} [214/215] Built Client.Shared (2.1s)
    info: Client/Shared.lean:3:0: 'Client.lemma' depends on axioms: [propext, Quot.sound]
    {built} [215/215] Built LeanCILProof0 (12s)
    info: LeanCILProof0.lean:55:0: Error: index out of bounds
    Error: index out of bounds
    warning: LeanCILProof0.lean:60:2: unused variable `x`
    Build completed successfully (215 jobs).

    """;
string[] lakeBuild = ["lake", "build", "+LeanCILProof0:olean"];
var internalErrors = LeanOutput.InternalErrors(panicking);
var logged = new LeanOutput.InternalError("LeanCILProof0", "LeanCILProof0.lean:55:0", "Error: index out of bounds");
Require(internalErrors.Count == 2 && internalErrors.All(error => error == logged),
    "each line of a panic Lean logged is at that message's position and module", string.Join("\n", internalErrors));
var rejected = LeanOutput.RejectedSuccess(lakeBuild, 0, panicking);
Require(rejected is not null && rejected.Message.StartsWith(
        "Lean reported an internal error (exit 0): lake build +LeanCILProof0:olean\n" +
        "Internal error: Error: index out of bounds (2 times) at LeanCILProof0.lean:55:0 (building LeanCILProof0)\n",
        StringComparison.Ordinal) && rejected.Message.EndsWith(panicking, StringComparison.Ordinal),
    "a successful Lean command that printed an internal error fails, naming the module and quoting the message",
    rejected?.Message);
// The summary lines repeat no error: the report reads the output below them.
Require(LeanOutput.InternalErrors(rejected!.Message).SequenceEqual(internalErrors),
    "summary lines are not read as further internal errors");
// Every form: Lean `panic!` with and without a declaration, runtime aborts, stack exhaustion and assertions.
string[] forms =
[
    "PANIC at Lean.Expr.appArg! Lean.Expr:1234:20: application expected",
    "PANIC at Init.Data.Option.BasicAux:16:14: value is none",
    "INTERNAL PANIC: unreachable code has been reached", "INTERNAL PANIC: out of memory",
    "Error: index out of bounds", "Stack overflow detected. Aborting.", "LEAN ASSERTION VIOLATION"
];
foreach (var form in forms)
{
    // Written to stderr, logged by Lake under `stderr:`, logged by Lean at a declaration, and in `--json` output.
    var json = System.Text.Json.JsonSerializer.Serialize(new
    {
        severity = "information", pos = new { line = 7, column = 0 }, fileName = "Proof.lean",
        data = form + "\nbacktrace:"
    });
    (string Output, string? Location)[] shapes =
    [
        (form + "\nbacktrace:\n", null), ($"info: stderr:\n{form}\nbacktrace:\n", null),
        ($"info: Proof.lean:7:0: {form}\n", "Proof.lean:7:0"), ($"Proof.lean:7:0: info: {form}\n", "Proof.lean:7:0"),
        (json + "\n", "Proof.lean:7:0")
    ];
    foreach (var (text, location) in shapes)
    {
        var found = LeanOutput.InternalErrors(text);
        Require(found.Count == 1 && found[0] == new LeanOutput.InternalError(null, location, form) &&
            LeanOutput.RejectedSuccess([@"C:\elan\bin\lean.exe", "Proof.lean"], 0, text) is not null &&
            LeanOutput.RejectedSuccess(["/opt/audit/leancil-audit", "--replay", "t.json"], 0, text) is not null,
            "internal-error form: " + form, text + "\n" + string.Join("\n", found));
        Require(Classify("proof checking", "Command failed (134): lean Proof.lean\n" + text) is
                { kind: FailureReports.InternalError, diagnostics: [{ kind: FailureReports.InternalError } first] } &&
            first.message == form,
            "a failed run that printed an internal error is an internal error, not a failed proof: " + form);
    }
}
// Ordinary output passes: axiom reports, warnings, a caller's own wording, and text another program quotes.
var ordinary = replayed + "warning: Client/Shared.lean:11:0: declaration uses 'sorry'\n" +
    "info: Client/Shared.lean:12:0: a panic is an internal error; index 3 is out of bounds for this list\n" +
    // The runtime's words inside a sentence, a goal or a quoted term are a message about them, at any severity.
    "info: Client/Shared.lean:13:0: the run printed Error: index out of bounds twice\n" +
    "warning: Client/Shared.lean:14:0: expected \"PANIC at Lean.Expr.appArg! Lean.Expr:1:2: no application\"\n" +
    "  Error: index out of bounds\n" +
    "error: Client/Shared.lean:15:2: unsolved goals\nh : message = \"INTERNAL PANIC: out of memory\"\n⊢ False\n" +
    "PANIC at lean\nBuild completed successfully (420 jobs).\n";
Require(LeanOutput.InternalErrors(ordinary).Count == 0 && LeanOutput.RejectedSuccess(lakeBuild, 0, ordinary) is null &&
    LeanOutput.RejectedSuccess(["dotnet", "run", "--file", "Tests/Fixture.cs"], 0, panicking) is null &&
    LeanOutput.RejectedSuccess(lakeBuild, 1, panicking) is null,
    "ordinary info and warning output passes, as does a program that only quotes an internal error");
// Resource limits Lean reports as errors keep their kind.
Require(Classify("proof checking", "error: LeanCILProof.lean:8:0: (kernel) deep recursion detected\n") is
        { kind: FailureReports.ResourceLimit, resource: "recursion" } &&
    Classify("proof checking", "error: LeanCILProof.lean:8:0: maximum recursion depth has been reached\n") is
        { kind: FailureReports.ResourceLimit, resource: "recursion" },
    "recursion limits stay resource limits");
var internalReport = Classify("proof checking", rejected.Message);
Require(internalReport is { kind: FailureReports.InternalError, stage: "proof checking", line: 55, column: 0,
        module: "Proofs.Mix", diagnostics.Length: 1 } && internalReport.file == proof &&
    internalReport.diagnostics[0] is { kind: FailureReports.InternalError, module: "Proofs.Mix",
        message: "Error: index out of bounds" } && internalReport.message == rejected.Message,
    "the report has its own kind, names the proof module and file, and quotes the message",
    System.Text.Json.JsonSerializer.Serialize(internalReport));
// An internal error leads the errors printed after it, which a tactic on a default value may have caused.
var mixed = Classify("proof checking", "Command failed (1): lake build\n" + panicking.Replace(
    "warning: LeanCILProof0.lean:60:2: unused variable `x`",
    "error: LeanCILProof0.lean:61:4: unsolved goals\n⊢ False"));
Require(mixed is { kind: FailureReports.InternalError, line: 55, diagnostics.Length: 2 } &&
    mixed.diagnostics[1] is { kind: FailureReports.UnsolvedGoal, line: 61 },
    "an internal error leads the Lean errors of the same run");
Require(Classify("proof checking", rejected.Message, ["LeanCILProof0"]).kind != FailureReports.InternalError &&
    LeanOutput.InternalErrors(panicking, ["LeanCILProof0"]).Count == 0,
    "another request's proof module does not make this request an internal error");
var internalSummary = LeanDiagnostics.Summarize(rejected.Message, null,
    location => sessionCopies.Locate(location))!.Text;
Require(internalSummary == $"Internal errors (1):\n  {proof}:55:0 (building LeanCILProof0)\n" +
        "    Error: index out of bounds (2 times)\n",
    "the summary shows each internal error once, at the user's file", internalSummary);
Directory.Delete(work, true);
Console.WriteLine("PASS failure reports classify stages and Lean diagnostics and map locations to the user's files");
Console.WriteLine("PASS internal errors of Lean fail a successful run with their own kind, and ordinary output passes");

// The JSON report reads Lean's records by these names; a renamed tag or marker would drop every record.
var obligationSource = File.ReadAllText(At("CIL/Safety/Obligations.lean"));
var recordSource = File.ReadAllText(At("CIL/Safety/FailureRecords.lean"));
var leanTags = "[" + string.Join(", ", VerifyReports.ObligationTags.Select(tag => "`" + tag)) + "]";
Require(obligationSource.Contains(leanTags) &&
    recordSource.Contains($"def failureMarker : String := \"{Program.FailureMarker}\""),
    "the report's obligation tags and record marker are Lean's");
var recordLine = new System.Text.Json.Nodes.JsonObject
{
    ["tactic"] = "cil_loop_steps", ["method"] = 0, ["pc"] = 1, ["instruction"] = "CIL.Op.add", ["stopped"] = false,
    ["error"] = new System.Text.Json.Nodes.JsonObject { ["line"] = 3, ["column"] = 2 },
    ["obligation"] = "invariant", ["reached"] = new System.Text.Json.Nodes.JsonObject { ["stack"] = "[]" },
    ["expected"] = new System.Text.Json.Nodes.JsonObject(), ["missing"] = "load",
    ["residual"] = new System.Text.Json.Nodes.JsonArray("r"),
    ["suggestions"] = new System.Text.Json.Nodes.JsonArray("s"),
    ["unknown"] = new System.Text.Json.Nodes.JsonObject()
}.ToJsonString();
// The C# statement of pc 1 starts at the sequence point of pc 0, the last at or before it.
VerifyReports.ManifestMethod[] manifest =
    [new("M", ["IL_0000: ldarg.0", "IL_0001: add"], [new(0, "Mix.cs", 12, 9), new(2, "Mix.cs", 13, 9)])];
var diagnostic = new FailureReports.Diagnostic(FailureReports.ElaborationError, null, "Proof", proof, 3, 2,
    "cil_loop_steps: stuck");
var records = VerifyReports.Records([("info", 3, 0, Program.FailureMarker + recordLine)]);
var stopped = VerifyReports.Failures(diagnostic, proof, manifest, records).Single();
Require(stopped["message"]!.GetValue<string>() == "cil_loop_steps: stuck" &&
    stopped["method"]!["signature"]!.GetValue<string>() == "M" &&
    stopped["cil"]!["ilOffset"]!.GetValue<int>() == 1 && stopped["cil"]!["instruction"]!.GetValue<string>() == "add" &&
    stopped["cil"]!["source"]!.ToJsonString() == """{"file":"Mix.cs","line":12,"column":9}""" &&
    stopped["obligations"]![0]!.GetValue<string>() == "invariant" &&
    stopped["missing"]!["shape"]!.GetValue<string>() == "load" &&
    stopped["suggestions"]![0]!.GetValue<string>() == "s" &&
    stopped["unknown"]!.AsObject().Count == 0, "a failure record fills the report's fields", stopped.ToJsonString());
// A record explains only the error at the position it cites; another error of the proof stays Lean's own.
var other = VerifyReports.Failures(diagnostic with { line = 4 }, proof, manifest, records).Single();
Require(other["tactic"] is null && other["unknown"]!["tactic"] is not null,
    "a record is paired with its own error only", other.ToJsonString());
var symbolFree = VerifyReports.Failures(diagnostic, proof, [manifest[0] with { Points = null }], records).Single();
Require(symbolFree["cil"]!["source"] is null &&
    symbolFree["unknown"]!["cil.source"]!.GetValue<string>() == VerifyReports.NoSymbols,
    "without symbols the C# location is null and says why", symbolFree.ToJsonString());
var open = VerifyReports.Failure(new(FailureReports.UnsolvedGoal, null, "Proof", proof, 3, 2,
    "unsolved goals\ncase invariant\nx : Nat\n\u22a2 True\n\ncase helper\n\u22a2 True"), manifest, null);
Require(open["obligations"]!.AsArray().Select(tag => tag!.GetValue<string>()).SequenceEqual(["invariant"]) &&
    open["cil"] is null && open["unknown"]!["cil"]!.GetValue<string>().Contains("left these goals open"),
    "unsolved goals report only LeanCIL obligation tags, and say why nothing else is known", open.ToJsonString());
Console.WriteLine("PASS verify --format json reads failure records and obligation tags, and explains each null");
