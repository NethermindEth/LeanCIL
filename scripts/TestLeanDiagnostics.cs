#!/usr/bin/env dotnet
#:property PublishAot=false
#:include LeanDiagnostics.cs

static void Require(bool condition, string message, string? text = null)
{
    if (!condition) throw new InvalidOperationException("Lean diagnostic summary regression: " + message + (text is null ? "" : "\n" + text));
}

// Shape of a failing `lake build +LeanCILProof:olean`: replayed modules print axiom
// reports and traces; the errors sit near the end between unrelated entries.
var replayed = string.Concat(Enumerable.Range(0, 400).Select(i =>
    $"\u2139 [{i}/420] Replayed CIL.Module{i}\ninfo: CIL/Module{i}.lean:3:0: 'CIL.lemma{i}' depends on axioms: [propext, Quot.sound]\n"));
const string failed = "\u2716";
var transcript = "Command failed (1): lake build +LeanCILProof:olean\n" + replayed + $"""
    {failed} [418/420] Building Client.Shared (2.1s)
    trace: .> LEAN_PATH=D:\work\.lake\build\lib\lean lean.exe D:\work\Client\Shared.lean -o D:\work\Shared.olean
    error: Client/Shared.lean:7:43: Tactic `rfl` failed: The left-hand side
      CIL.invoke Extracted.program 4 0 [CIL.Value.i64 x, CIL.Value.i64 y] memory
    is not definitionally equal to the right-hand side
      some (memory, [CIL.Value.i64 (x - y)])

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
Require(errors[0].Module == "Client.Shared" && errors[0].Location == "Client/Shared.lean:7:43", "location or module of the first error");
// The whole message block is kept, including unindented continuation lines.
Require(errors[0].Lines.Count == 4 && errors[0].Lines[3] == "  some (memory, [CIL.Value.i64 (x - y)])", "first message block", string.Join("\n", errors[0].Lines));
Require(errors[1].Lines.Count == 1 && errors[1].Lines[0] == "unknown identifier 'missing'", "second block stops at the next entry");
Require(errors[2].Module == "LeanCILProof0" && errors[2].Lines[^1].Contains("Full.fullBody", StringComparison.Ordinal), "proof module block");
Require(errors[3].Location == @"D:\work\Generated.lean:1:0", "drive-letter location");
Require(errors.All(error => error.Module != "LeanCILProof1"), "other requests' proof modules are omitted");

var summary = LeanDiagnostics.Summarize(transcript, ["LeanCILProof1"])!;
Require(summary.StartsWith("Lean errors (4):\n  Client/Shared.lean:7:43 (building Client.Shared)\n    Tactic `rfl` failed", StringComparison.Ordinal), "summary header", summary);
Require(!summary.Contains("depends on axioms", StringComparison.Ordinal) && !summary.Contains("trace:", StringComparison.Ordinal) &&
    !summary.Contains("declaration uses 'sorry'", StringComparison.Ordinal) && !summary.Contains("Lean exited", StringComparison.Ordinal) &&
    !summary.Contains("build failed", StringComparison.Ordinal), "summary carries only error diagnostics", summary);
Require(summary.Split('\n').Length < 25 && transcript.Split('\n').Length > 800, "summary is bounded relative to the transcript", summary);
Require(LeanDiagnostics.Summarize(transcript)!.Contains("unsolved goals of another request", StringComparison.Ordinal), "a lone request keeps every module");

// Direct `lean` output uses the location-first format.
var direct = LeanDiagnostics.Errors("Batch.lean:3:4: error: type mismatch\n  h\nBatch.lean:9:0: warning: unused\n");
Require(direct.Count == 1 && direct[0].Location == "Batch.lean:3:4" && direct[0].Lines.Count == 2, "location-first format");

// Pathological messages are truncated in the summary only.
var huge = "error: P.lean:1:0: unsolved goals\n" + string.Concat(Enumerable.Range(0, 500).Select(i => $"goal line {i} " + new string('x', 1000) + "\n")) +
    string.Concat(Enumerable.Range(0, 30).Select(i => $"error: P.lean:{i + 2}:0: e{i}\n"));
var bounded = LeanDiagnostics.Summarize(huge)!;
Require(bounded.Contains($"... {501 - LeanDiagnostics.MaxLines} more lines in the full output", StringComparison.Ordinal) &&
    bounded.Contains($"... {31 - LeanDiagnostics.MaxErrors} more errors in the full output", StringComparison.Ordinal) &&
    bounded.Split('\n').All(line => line.Length <= LeanDiagnostics.MaxLineLength + 8), "truncation", bounded[..2000]);

Require(LeanDiagnostics.Summarize("Command failed (1): dotnet build\nerror CS1002: ; expected\n") is null, "non-Lean output has no summary");
Console.WriteLine("PASS Lean diagnostic summaries keep located error blocks of failing modules and stay bounded");
