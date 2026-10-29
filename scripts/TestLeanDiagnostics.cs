#!/usr/bin/env dotnet
#:property PublishAot=false
#:include LeanDiagnostics.cs
#:include FailureReports.cs

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

var summary = LeanDiagnostics.Summarize(transcript, ["LeanCILProof1"])!;
const string SummaryHeader =
    "Lean errors (4):\n  Client/Shared.lean:7:43 (building Client.Shared)\n    Tactic `rfl` failed";
Require(summary.StartsWith(SummaryHeader, StringComparison.Ordinal), "summary header", summary);
string[] omitted = ["depends on axioms", "trace:", "declaration uses 'sorry'", "Lean exited", "build failed"];
Require(omitted.All(text => !summary.Contains(text, StringComparison.Ordinal)),
    "summary carries only error diagnostics", summary);
Require(summary.Split('\n').Length < 25 && transcript.Split('\n').Length > 800,
    "summary is bounded relative to the transcript", summary);
Require(LeanDiagnostics.Summarize(transcript)!.Contains("unsolved goals of another request", StringComparison.Ordinal),
    "a lone request keeps every module");

// Direct `lean` output uses the location-first format.
var direct = LeanDiagnostics.Errors("Batch.lean:3:4: error: type mismatch\n  h\nBatch.lean:9:0: warning: unused\n");
Require(direct.Count == 1 && direct[0].Location == "Batch.lean:3:4" && direct[0].Lines.Count == 2,
    "location-first format");

// Pathological messages are truncated in the summary only.
var goalLines = string.Concat(Enumerable.Range(0, 500).Select(i => $"goal line {i} " + new string('x', 1000) + "\n"));
var huge = "error: P.lean:1:0: unsolved goals\n" + goalLines +
    string.Concat(Enumerable.Range(0, 30).Select(i => $"error: P.lean:{i + 2}:0: e{i}\n"));
var bounded = LeanDiagnostics.Summarize(huge)!;
var moreLines = $"... {501 - LeanDiagnostics.MaxLines} more lines in the full output";
var moreErrors = $"... {31 - LeanDiagnostics.MaxErrors} more errors in the full output";
Require(bounded.Contains(moreLines, StringComparison.Ordinal) &&
    bounded.Contains(moreErrors, StringComparison.Ordinal) &&
    bounded.Split('\n').All(line => line.Length <= LeanDiagnostics.MaxLineLength + 8),
    "truncation", bounded[..2000]);

Require(LeanDiagnostics.Summarize("Command failed (1): dotnet build\nerror CS1002: ; expected\n") is null,
    "non-Lean output has no summary");
Console.WriteLine("PASS Lean diagnostic summaries keep located error blocks of failing modules and stay bounded");

var package = Path.GetFullPath("package");
var proof = Path.Combine(package, "Proofs", "Mix.lean");
var output = Path.GetFullPath("artifacts/Mix");
FailureReports.Report Classify(string stage, string text, string[]? hidden = null, string? root = null) =>
    FailureReports.Classify(stage, text, hidden, "ExampleProof.correctness", proof, output, root ?? package);
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
var unrooted = FailureReports.Classify("proof checking", unrootedProof + ":4:2: error: unsolved goals\n⊢ False\n",
    null, "ExampleProof.correctness", proof, output, null);
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
Console.WriteLine("PASS failure reports classify stages and Lean diagnostics and map locations to the user's files");
