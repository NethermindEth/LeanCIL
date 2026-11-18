#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs
#:include ../scripts/ProofCostReport.cs
#:include ../scripts/CertifiedLibraryDonor.cs
#:include ../scripts/ExportVerificationSuites.cs
#:include ../scripts/VerificationGroupRunner.cs
#:include ../scripts/VerificationSuites.cs

using System.Globalization;
using System.Text.RegularExpressions;

// Calls::Mutate{n} stores its argument in a local and passes the local by reference to Mutate n times. The proof of
// each size states the result twice: by stepping every call, and from Mutate's decoded summary at each call. The
// summary of Decrement in the loop of Examples.Loops::CountCalls is checked against mutations of its own, and the
// summary of the vector callee Examples.DivisionIntrinsics::UnsafeLow against a forged original.
int[] sizes = [1, 4, 16];
// Most times as much as a call costs through the summary from 1 to 4 calls that it may cost from 4 to 16.
const double AllowedCallGrowth = 1.6;
var directory = At("artifacts/SummaryCalls");
var source = Path.Combine(directory, "Assembly");
var proofs = Path.Combine(directory, "Proofs");
Directory.CreateDirectory(source);
Directory.CreateDirectory(proofs);
File.WriteAllText(Path.Combine(source, "Fixture.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net11.0</TargetFramework>
<Optimize>true</Optimize></PropertyGroup></Project>
""");
File.WriteAllText(Path.Combine(source, "Fixture.cs"), FixtureSource(sizes));
Run(["dotnet", "build", Path.Combine(source, "Fixture.csproj"), "-c", "Release"]);
var assembly = Path.Combine(source, "bin/Fixture.dll");
using var verification = new Program();
foreach (var calls in sizes)
{
    var proof = Path.Combine(proofs, $"Mutate{calls}.lean");
    File.WriteAllText(proof, MutateProof(calls));
    verification.Verify(assembly, "Fixture", $"System.UInt64 Calls::Mutate{calls}(System.UInt64)", proof,
        Path.Combine(directory, $"Mutate{calls}"));
    Console.WriteLine($"PASS Mutate{calls} by stepping every call and through the decoded summary of Mutate");
}

// Mutate's summary exists so that a caller pays for Mutate's body once: through it, the caller's proof costs about
// the same per call at any number of calls, and less than stepping every call. Counted heartbeats decide.
verification.Library(CommonInputs());
var measurement = ProofCostReport.Measure(At("."), verification.library, Path.Combine(directory, "Cost"),
    false, [directory], [], 2, "SummaryCalls", output => sizes.Any(calls => output == $"Mutate{calls}"));
if (measurement.Unmeasured.Count != 0)
    throw new InvalidOperationException("Unmeasured: " + string.Join("; ", measurement.Unmeasured));
long Cost(int calls, string theorem, string measure) => measurement.Rows.Single(row =>
    row.Group == $"Mutate{calls}/Proof" && row.Name == "ExampleProof." + theorem).Measures[measure];
if (SummaryCallGrowth(sizes, [.. sizes.Select(calls => (long)calls * calls)]) <= AllowedCallGrowth)
    throw new InvalidOperationException("The growth bound accepts a caller whose cost is quadratic in its calls");
foreach (var measure in new[] { "heartbeats", "kernelHeartbeats" })
{
    var growth = SummaryCallGrowth(sizes, [.. sizes.Select(calls => Cost(calls, "correctness", measure))]);
    if (growth > AllowedCallGrowth)
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Through the summary, a call costs {growth:F2} times as many {measure} from 4 to 16 calls as from 1 to " +
            $"4; the limit is {AllowedCallGrowth}"));
    var summarized = new[] { "correctness", "mutate_holds", "mutate_summary", "bodies_decode" }
        .Sum(theorem => Cost(sizes[^1], theorem, measure));
    var stepped = Cost(sizes[^1], "correctness_stepped", measure);
    if (summarized >= stepped)
        throw new InvalidOperationException(
            $"At {sizes[^1]} calls the proof through the summary costs {summarized} {measure}, stepping {stepped}");
    Console.WriteLine(string.Create(CultureInfo.InvariantCulture,
        $"PASS through the summary a call costs {growth:F2} times as many {measure} from 4 to 16 calls as from 1 " +
        $"to 4, and {sizes[^1]} calls cost {summarized} against {stepped} stepped"));
}

// The contract of Mutate without its write, and a caller that leaves Mutate's precondition unproved, are refused
// with an error in the declaration that needs them.
var mutate1 = File.ReadAllText(Path.Combine(proofs, "Mutate1.lean"));
ProofTarget mutateTarget = new(assembly, "Fixture", "System.UInt64 Calls::Mutate1(System.UInt64)");
RejectedProof("Mutate1Footprint", Changed(mutate1, "  footprint := fun (place, _) => [(place, 8)]",
    "  footprint _ := []"), mutateTarget, "mutate_holds", "unsolved goals");
RejectedProof("Mutate1Precondition", Changed(mutate1, "frame0.snapshots.read_word64 (index := 0) rfl rfl⟩", "?_⟩"),
    mutateTarget, "correctness", "unsolved goals");

// In the loop of CountCalls, a summary of Decrement that bounds its result without stating it still proves the
// call and the measure, and leaves the invariant unproved. A summary claimed for CountCalls' own token at the index
// the call enters is refused where the site check reads the call's token.
var countCalls = File.ReadAllText(At("Examples/Proofs/CountCallsSummary.lean"));
ProofTarget countTarget = new(At("Examples/Assembly/bin/Examples.dll"), "Examples",
    "System.UInt32 Examples.Loops::CountCalls(System.UInt32)");
var weakened = Changed(Changed(Changed(countCalls, "  post x _ _ v := v = x - 1",
        "  post x _ _ v := x ≠ 0 → v.toNat < x.toNat"),
    "refine MethodContract.Holds.intro m _ ?_ (Confined.refl _ m) rfl",
    "refine MethodContract.Holds.intro m (x - 1) ?_ (Confined.refl _ m) measure_falls"), """
        cil_loop_call summary.holds x at decrementSite
        -- The frame of the memory before the call is stale once `calledFrame` holds.
        clear frame
        cil_loop_recurse recurse (x - 1, count + 1)
        case invariant =>
          show count + 1 + (x - 1) = value
    """, """
        cil_loop_call keeping summary.holds x at decrementSite
        -- The frame of the memory before the call is stale once `calledFrame` holds.
        clear frame
        cil_loop_recurse recurse (output, count + 1)
        case invariant =>
          show count + 1 + output = value
    """);
weakened = Changed(weakened, "    case measure => exact measure_falls zero\n#print axioms terminates\n",
    "    case measure => exact returned zero\n#print axioms terminates\n");
RejectedProof("CountCallsWeakPost", weakened, countTarget, "terminates", "omega could not prove the goal",
    at: "bv_omega");
RejectedProof("CountCallsOtherToken", Changed(countCalls, "    token = Extracted.method1Original.token ∧",
    "    token = Extracted.method0Original.token ∧"), countTarget, "decrement_named", "Application type mismatch");

// With the original of Mutate forged to subtract, the body check refuses the record and Mutate's contract fails,
// so its decoded summary rests on sorryAx.
var summary = mutate1[mutate1.IndexOf("/-- `Mutate` adds two", StringComparison.Ordinal)..
    mutate1.IndexOf("/-- The caller returns `x` plus two per call and keeps all memory below its entry, applying",
        StringComparison.Ordinal)];
var forged = Path.Combine(proofs, "ForgedMutate.lean");
File.WriteAllText(forged, ForgeDecodedOriginal(File.ReadAllText(Path.Combine(directory, "Mutate1", "Extracted.lean")),
    1, "opcode := 88,", "opcode := 89,") + $$"""

    import Lean
    import CIL
    import CIL.MethodIdentity
    namespace ForgedSummary
    open CIL CIL.Safety CIL.Extraction
    bind_method mutate mutateBody := "System.Void Calls::Mutate(System.UInt64&)"
    {{summary}}
    open Lean in
    run_cmd do
      if (← collectAxioms ``mutate_summary).contains ``sorryAx then
        throwError "mutate_summary depends on sorryAx"
    end ForgedSummary
    """);
var rejected = new RejectedEvidence(Path.Combine(directory, "Rejected"));
rejected.Add(forged, "PASS a forged original of Mutate fails its body check, its contract and its decoded summary",
    "the decoded method does not match its body bytes or metadata", "unsolved goals",
    "mutate_summary depends on sorryAx");

// With the original of UnsafeLow forged to read lane 1 of the vector, its record claims a body other than its pinned
// bytes, so the body check refuses it and the decoded summary of Examples/Proofs/VectorSummary.lean rests on sorryAx.
var vectorProof = File.ReadAllText(At("Examples/Proofs/VectorSummary.lean"));
var lowSummary = vectorProof[vectorProof.IndexOf("/-- `UnsafeLow` returns its argument", StringComparison.Ordinal)..
    vectorProof.IndexOf("/-- The caller returns its argument plus one and keeps the caller memory, applying",
        StringComparison.Ordinal)];
var vectorExtraction = Path.Combine(directory, "VectorSummary");
Run(Extract("extract", At("Examples/Assembly/bin/Examples.dll"), "Examples",
    "System.UInt64 Examples.DivisionIntrinsics::UnsafeLowNext(System.UInt64)", vectorExtraction));
var forgedLow = Path.Combine(proofs, "ForgedUnsafeLow.lean");
File.WriteAllText(forgedLow, ForgeDecodedOriginal(File.ReadAllText(Path.Combine(vectorExtraction, "Extracted.lean")),
    1, "opcode := 22,", "opcode := 23,") + $$"""

    import Lean
    import CIL
    import CIL.MethodIdentity
    namespace ForgedSummary
    open CIL CIL.Safety CIL.Extraction
    bind_method low lowBody := "System.UInt64 Examples.DivisionIntrinsics::UnsafeLow(System.UInt64)"
    {{lowSummary}}
    open Lean in
    run_cmd do
      if (← collectAxioms ``low_summary).contains ``sorryAx then
        throwError "low_summary depends on sorryAx"
    end ForgedSummary
    """);
rejected.Add(forgedLow, "PASS a forged original of UnsafeLow fails its body check and its decoded summary",
    "the decoded method does not match its body bytes or metadata", "low_summary depends on sorryAx");
rejected.Check();

// How many times as much the caller costs per call between its last two sizes as between its first two. At 1, 4 and
// 16 calls a cost a n^2 + b n grows (20a + b) / (5a + b) times, more than the limit once a > b / 20.
static double SummaryCallGrowth(int[] calls, long[] costs) =>
    (double)(costs[2] - costs[1]) / (calls[2] - calls[1]) / ((double)(costs[1] - costs[0]) / (calls[1] - calls[0]));

// `text` with `before`, which must occur once, replaced by `after`.
static string Changed(string text, string before, string after) =>
    text.IndexOf(before, StringComparison.Ordinal) is var index && index >= 0 &&
        text.IndexOf(before, index + 1, StringComparison.Ordinal) < 0
        ? text.Replace(before, after, StringComparison.Ordinal)
        : throw new InvalidOperationException("Expected one occurrence of: " + before);

// Verifies `text` as the proof of `target` and requires it to fail with an error inside `theorem`, on the line `at`
// when given, whose message contains `diagnostic`, so an unrelated failure cannot pass as the rejection.
void RejectedProof(string name, string text, ProofTarget target, string theorem, string diagnostic, string? at = null)
{
    var proof = Path.Combine(proofs, $"{name}.lean");
    File.WriteAllText(proof, text);
    var lines = text.Split('\n');
    var start = Array.FindIndex(lines, line => line.StartsWith($"theorem {theorem} ", StringComparison.Ordinal)) + 1;
    var end = Array.FindIndex(lines, line => line == $"#print axioms {theorem}") + 1;
    try
    {
        verification.Verify(target.Assembly, target.Library, target.Entry, proof, Path.Combine(directory, name));
    }
    catch (InvalidOperationException error)
    {
        // The session checks a copy of the proof, with the same lines, as Proof.lean.
        var located = SummaryPatterns.ProofError().Matches(error.Message)
            .Select(match => (Line: int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture),
                Message: match.Groups[2].Value)).ToArray();
        if (start == 0 || end == 0 || !located.Any(found => found.Line >= start && found.Line <= end &&
                (at is null || lines[found.Line - 1].Trim() == at) &&
                found.Message.Contains(diagnostic, StringComparison.Ordinal)))
            throw new InvalidOperationException($"Expected {diagnostic} in {theorem} ({start}-{end})" +
                (at is null ? "" : " at " + at) + $":\n{error.Message}");
        Console.WriteLine($"PASS {name} refused in {theorem}");
        return;
    }
    throw new InvalidOperationException($"{name} was accepted");
}


// One public caller per size, each passing the same local to the private Mutate as often as its name says.
static string FixtureSource(int[] sizes)
{
    var callers = sizes.Select(calls => $$"""

            public static ulong Mutate{{calls}}(ulong x)
            {
                ulong local = x;
        {{string.Concat(Enumerable.Repeat("        Mutate(ref local);\n", calls))}}        return local;
            }
        """);
    return $$"""
        using System.Runtime.CompilerServices;

        public static class Calls
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            static void Mutate(ref ulong value) => value = unchecked(value + 2);
        {{string.Concat(callers)}}
        }

        """;
}

// The local's value after the given number of calls.
static string Value(int calls) => calls == 0 ? "x" : $"x + {2 * calls}";

// The value stepping computes from the value before the call: `x + 2#64` after the first.
static string SteppedValue(int calls) => calls == 1 ? "x + 2#64" : $"{Value(calls - 1)} + 2#64";

// Each store is stated with the value the next read returns and rewritten to the form stepping computes.
static string SteppedProof(int calls)
{
    var lines = new List<string>
    {
        "  obtain ⟨reference, entered, enter⟩ := entry.checked memory x wellFormed",
        "  have ready0 := enter.numeric0.writable",
        "  obtain ⟨memory0, write0, store0, read0, -⟩ := store_local_word64 x ready0"
    };
    for (var call = 1; call <= calls; call++)
    {
        lines.Add($"  have ready{call} := snapshot_access_after_write ready{call - 1} write{call - 1}");
        lines.Add($"  obtain ⟨memory{call}, write{call}, store{call}, read{call}⟩ := " +
            $"store_word64 ({Value(call)}) ready{call}");
        lines.Add($"  rw [← show {SteppedValue(call)} = {Value(call)} by bv_omega] at store{call}");
    }
    var below = "(write_preserves_memory_below _ _ _ _ _ _ enter.numeric0.fresh write0)";
    for (var call = 1; call <= calls; call++)
        below = $"({below}.trans\n      (write_preserves_memory_below _ _ _ _ _ _ enter.numeric0.fresh write{call}))";
    lines.Add($"  have below := MemoryBelow.frame_round_trip enter.setup\n    {below}");
    lines.Add("  suffices ran : ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =");
    lines.Add($"      .ok (leaveFrame (entry.frame memory reference) memory{calls}, " +
        $"[.scalar (.i64 ({Value(calls)}))]) by");
    lines.Add("    obtain ⟨fuel, ran⟩ := ran");
    lines.Add("    exact WP.adequate.mpr ⟨fuel, _, _, ran, rfl, below⟩");
    var range = Enumerable.Range(1, calls).ToArray();
    string[] facts =
    [
        "enter.setup", "entry.frame", "store0", "read0", .. range.Select(call => $"store{call}"),
        .. range.Select(call => $"read{call}"), $"load_local_word64_of_read read{calls}", "localAddress",
        .. range.Select(call => $"access_reference_valid _ _ _ _ _ ready{call}"),
        .. range.Select(call => $"checkedValue_address _ _ (access_reference_valid _ _ _ _ _ ready{call})"),
        "numericOfWidth"
    ];
    lines.Add($"  cil_checked_steps [{string.Join(",\n    ", facts)}]");
    return string.Join("\n", lines);
}

// Each call reads its precondition from the frame before it and leaves the next frame. Clearing the earlier frame
// keeps the context, and so the cost of each call, from growing with the calls before it.
static string SummaryProof(int calls)
{
    var lines = new List<string>
    {
        "  obtain ⟨record, -, summary⟩ := mutate_summary",
        "  obtain ⟨reference, entered, enter⟩ := entry.checked memory x wellFormed",
        "  apply WP.enter (by rfl) (by rfl) enter.setup",
        "  obtain ⟨initial, firstStore, frame0, -⟩ := (enter.frame []).store 0 (.i64 x) rfl",
        "  have permitted1 : mutateContract.pre (reference, x) initial :=",
        "    ⟨frame0.homes.writable_at (kind := .word64) (home := reference) (index := 0) rfl,",
        "      frame0.snapshots.read_word64 (index := 0) rfl rfl⟩"
    };
    for (var call = 1; call <= calls; call++)
    {
        var frame = $"frame{call - 1}";
        if (call > 1)
        {
            var post = call == 2 ? "mutated1.post"
                : $"show {Value(call - 2)} + 2 = {Value(call - 1)} by bv_omega ▸ mutated{call - 1}.post";
            lines.Add($"  have permitted{call} : mutateContract.pre (reference, {Value(call - 1)}) " +
                $"final{call - 1} :=");
            lines.Add($"    ⟨{frame}.homes.writable_at (kind := .word64) (home := reference) (index := 0) rfl,");
            lines.Add($"      {post}⟩");
        }
        lines.Add(call == 1 ? $"  cil_contract_steps [firstStore, localAddress, {frame}.form_home 0]"
            : $"  cil_contract_steps [localAddress, {frame}.form_home 0]");
        lines.Add("  apply WP.exists_execution");
        lines.Add($"  apply WP.local_call {frame} summary.holds (reference, {Value(call - 1)}) (by rfl) (by rfl)");
        lines.Add($"    (by cil_checked_step [localAddress, {frame}.form_home 0]) permitted{call} 0 .word64 " +
            "reference");
        lines.Add($"    rfl rfl (fun _ => .i64 ({Value(call)})) (fun _ => ({Value(call)}).toNat) (fun _ => rfl)");
        lines.Add(call == 1 ? "    (fun _ _ post => post)"
            : $"    (fun _ _ post => by rw [← show {Value(call - 1)} + 2 = {Value(call)} by bv_omega]; exact post)");
        lines.Add($"  intro final{call} values{call} mutated{call} frame{call}");
        lines.Add($"  clear {frame}");
    }
    lines.Add($"  have loaded := frame{calls}.snapshots.load (index := 0) (.i64 ({Value(calls)})) rfl");
    lines.Add($"    (body := Extracted.method0) (pc := {2 * calls + 2}) (args := [.scalar (.i64 x)]) (stack := [])");
    lines.Add("  cil_contract_steps [loaded]");
    lines.Add($"  exact ⟨rfl, frame{calls}.leave_kept enter.setup _ rfl⟩");
    return string.Join("\n", lines);
}

static string MutateProof(int calls) => $$"""
    import Extracted
    import CIL
    import CIL.MethodIdentity
    import CIL.Safety.LoopScaffold

    /-!
    # {{calls}} byref calls, stepped and through a decoded summary

    `Calls::Mutate{{calls}}` passes one local to `Mutate` {{calls}} times. `correctness_stepped` steps every
    call; `correctness` applies the decoded summary of `Mutate` at each call.
    -/

    namespace ExampleProof
    open CIL CIL.Safety CIL.Extraction

    bind_entry entry (memory : Safety.Memory) (x : W64) (wellFormed : memory.WellFormed) :=
      Extracted.method0 with [.scalar (.i64 x)] from memory allocating wellFormed
    bind_method mutate mutateBody := "System.Void Calls::Mutate(System.UInt64&)"

    /-- The caller returns `x` plus two per call and keeps all memory below its entry, stepping
        every call. -/
    theorem correctness_stepped (memory : Safety.Memory) (x : W64) (wellFormed : memory.WellFormed) :
        WP (Execution (fun fuel => invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory))
          (fun (final, values) => values = [.scalar (.i64 ({{Value(calls)}}))] ∧
            MemoryBelow memory.nextIdentity memory final) := by
    {{SteppedProof(calls)}}
    #print axioms correctness_stepped

    /-- `Mutate` adds two to the word its argument names and writes nothing else. -/
    def mutateContract : MethodContract (Reference × W64) Unit where
      args := fun (place, _) => [.reference (.address place)]
      results _ := []
      pre := fun (place, old) memory => access memory place 8 1 true = .ok () ∧
        read memory place 8 1 = .ok (numberBytes old.toNat 8)
      footprint := fun (place, _) => [(place, 8)]
      post := fun (place, old) _ final _ =>
        read final place 8 1 = .ok (numberBytes (old + 2).toNat 8)

    /-- `Mutate` meets its contract. -/
    theorem mutate_holds : mutateContract.Holds Extracted.program mutate := by
      rintro ⟨place, old⟩ memory ⟨ready, loaded⟩
      obtain ⟨final, written, stored, readback⟩ := store_word64 (old + 2) ready
      refine MethodContract.Holds.intro final () ?_
        (Confined.write written (by simp [mutateContract])) readback
      cil_checked_steps [loaded, stored, access_reference_valid _ _ _ _ _ ready,
        checkedValue_address _ _ (access_reference_valid _ _ _ _ _ ready)]
    #print axioms mutate_holds

    /-- Every record's pinned bytes decode to the method at its index of the extraction. -/
    theorem bodies_decode :
        decodedProgram? Extracted.profile Extracted.environment Extracted.methodEvidence =
          some Extracted.program :=
      decodedProgram?_eq_some
        (.cons ((Method.ofBody?_of_decodes Extracted.method0_body_validated).trans
            Extracted.method0_decoded)
          (.cons ((Method.ofBody?_of_decodes Extracted.method1_body_validated).trans
              Extracted.method1_decoded) .nil))
    #print axioms bodies_decode

    /-- The contract of `Mutate`, bound to its record and the bytes it decodes from. -/
    theorem mutate_summary : ∃ record, Extracted.methodEvidence[mutate]? = some record ∧
        DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
          Extracted.environment mutate record.assembly record.original.token record.arguments
          mutateContract :=
      ⟨_, rfl, .of_decoded bodies_decode rfl Extracted.method1_specialization_validated.1
        mutate_holds⟩
    #print axioms mutate_summary

    /-- The caller returns `x` plus two per call and keeps all memory below its entry, applying
        the summary of `Mutate` at each call. -/
    theorem correctness (memory : Safety.Memory) (x : W64) (wellFormed : memory.WellFormed) :
        WP (Execution (fun fuel => invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory))
          (fun (final, values) => values = [.scalar (.i64 ({{Value(calls)}}))] ∧
            MemoryBelow memory.nextIdentity memory final) := by
    {{SummaryProof(calls)}}
    #print axioms correctness

    end ExampleProof

    """;

// The assembly, library and entry a rejected proof is verified against.
record ProofTarget(string Assembly, string Library, string Entry);

/// <summary>The patterns that read Lean's report of a rejected proof.</summary>
static partial class SummaryPatterns
{
    [GeneratedRegex(@"Proof\.lean:(\d+):\d+: error(?:\([^)\r\n]*\))?: ([^\r\n]*)")]
    internal static partial Regex ProofError();
}
