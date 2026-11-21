import Changed
import CountCallsSummary
import CIL.Safety.RegionRun

/-! Reuse the compiled CountCalls loop after changing its initial accumulator to one. -/
namespace ChangedLoop
open CIL CIL.Safety CIL.Extraction

private abbrev region (method pc : Nat) := inStarts [(0, 3), (1, 0)] method pc = true

/-- Both the loop suffix and all entries it calls stay in the checked region. -/
private theorem closed : RegionClosed Extracted.program region :=
  RegionClosed.of_check (by decide +kernel)
#print axioms closed

/-- Only the constant that precedes the region changes. -/
private theorem agrees : AgreesOn Extracted.program Changed.program region := by
  apply AgreesOn.set Extracted.program_method0 Changed.method0.code
  intro pc inside
  exact code_agrees_of_drop (a := Changed.method0.code) (b := Extracted.method0.code)
    (lower := 3) rfl (by simpa [region, inStarts] using inside)
#print axioms agrees

/-- The live word locals retain a remaining count and the number of calls already counted. -/
abbrev State (remaining counted : Reference) :=
  FrameState [] Memory.empty [.word32, .word32] (W32 × W32)
    (fun _ => [.bytes .word32 remaining, .bytes .word32 counted])
    fun values => [some (.i32 values.1), some (.i32 values.2)]

/-- The producer proves termination by decreasing the remaining count. The
    destination agrees on the whole loop and the callee it reaches. -/
theorem fromGuard (args : List CIL.Safety.Value) (value : W32) {remaining counted : Reference}
    (state : State remaining counted) (total : state.values.2 + state.values.1 = value) :
    LoopTerminates Changed.program 0 args (fun _ values => values = [.scalar (.i32 value)])
      (ExampleProof.header remaining counted state) := by
  obtain ⟨record, _, summary⟩ := ExampleProof.decrement_summary
  obtain ⟨fuel, result, ran, post⟩ := ExampleProof.terminates summary args value state total
  refine ⟨fuel, result, ?_, post⟩
  have inside : region 0 (ExampleProof.header remaining counted state).pc := by
    change region 0 13
    decide +kernel
  exact (run_congr_region closed agrees fuel 0 _ args _ _ _ inside).trans ran
#print axioms fromGuard

/-- Starting the accumulator at one makes the compiled loop return its input plus one,
    with 32-bit wraparound, for every input. -/
theorem correctness : Ensures Changed.program 0
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Memory.empty)
    (fun args _ _ values => ∃ x : W32, args = [.scalar (.i32 x)] ∧
      values = [.scalar (.i32 (x + 1))]) := by
  apply ensures_of_loop
  rintro _ _ ⟨x, rfl, rfl⟩
  obtain ⟨remaining, counted, entered, enter⟩ := ExampleProof.entry.checked x
  obtain ⟨first, wroteFirst, firstFacts, -⟩ := (enter.frame []).store 0 (.i32 x) rfl
  obtain ⟨ready, wroteCount, facts, -⟩ := firstFacts.store 1 (.i32 1) rfl
  let state : State remaining counted := ⟨(x, 1), ready, facts⟩
  obtain ⟨fuel, result, ran, post⟩ := fromGuard [.scalar (.i32 x)] (x + 1) state
    (by change 1 + x = x + 1; bv_omega)
  refine ⟨Changed.method0, _, entered, Changed.program_method0, rfl, enter.setup,
    fuel + 6, result, ?_, x, rfl, post⟩
  change run Changed.program fuel 0 13 [.scalar (.i32 x)]
    (ExampleProof.entry.frame remaining counted) [.scalar (.i32 x)] ready = .ok result at ran
  change run Changed.program (fuel + 6) 0 0 [.scalar (.i32 x)]
    (ExampleProof.entry.frame remaining counted) [] entered = .ok result
  dsimp only [ExampleProof.entry.frame] at ran ⊢
  cil_checked_steps [wroteFirst, wroteCount, facts.load 0] <;> exact ran
#print axioms correctness
end ChangedLoop
