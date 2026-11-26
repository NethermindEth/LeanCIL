import Extracted
import CIL
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.LoopScaffold

/-!
# A counted loop through a decoded summary

`Examples.Loops::CountCalls` counts down its argument, calling `Decrement` once per iteration,
and returns how many calls it made. Both methods decode from their pinned bytes.
`correctness_stepped` steps `Decrement`'s body at the call of every iteration;
`correctness` proves the same statement from a `DecodedSummary` of `Decrement`, applied at
the call with `cil_loop_call`, without stepping its body in the loop.
-/

namespace ExampleProof
open CIL CIL.Safety CIL.Extraction

bind_method countCalls countBody := "System.UInt32 Examples.Loops::CountCalls(System.UInt32)"
bind_callee decrement decrementBody :=
  "System.UInt32 Examples.Loops::Decrement(System.UInt32)" from countBody
bind_call decrementSite := decrement from countBody

bind_entry entry (x : W32) := countBody with [.scalar (.i32 x)] from Memory.empty
  allocating Memory.empty_wellFormed
bind_loop loop := countBody

/-- The remaining count and the calls made so far, held by the frame's two locals. -/
private abbrev State (remaining counted : Reference) :=
  FrameState [] Memory.empty [.word32, .word32] (W32 × W32)
    (fun _ => [.bytes .word32 remaining, .bytes .word32 counted])
    fun values => [some (.i32 values.1), some (.i32 values.2)]

/-- The loop test, with the remaining count on the stack. -/
bind_cutpoint header (remaining counted : Reference) (state : State remaining counted) :=
  countBody at loop.latch matching (· matches .brtrue _)
  with entry.frame remaining counted, [.scalar (.i32 state.values.1)], state.memory

/-- `count + remaining` is the input. -/
private def invariant {remaining counted : Reference} (value : W32)
    (state : State remaining counted) : Prop :=
  state.values.2 + state.values.1 = value

/-- The remaining count falls by one in every iteration that does not exit. -/
private theorem measure_falls {x : W32} (zero : ¬x = 0) : (x - 1).toNat < x.toNat := by
  have positive : 0 < x.toNat := by
    have : x.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
    omega
  rw [BitVec.toNat_sub_of_le]
  · simp; omega
  · change 1 ≤ x.toNat
    omega
#print axioms measure_falls

/-- From every loop test, the loop returns its input, stepping `Decrement` at each call. -/
theorem terminates_stepped (args : List CIL.Safety.Value) (value : W32)
    {remaining counted : Reference} (state : State remaining counted)
    (valid : invariant value state) :
    LoopTerminates Extracted.program countCalls args
      (fun _ values => values = [.scalar (.i32 value)]) (header remaining counted state) := by
  apply loop_terminates_induction Extracted.program countCalls args (header remaining counted)
    (invariant value) (fun s => s.values.1.toNat) _ ?_ state valid
  rintro ⟨⟨x, count⟩, m, frame⟩ total recurse
  dsimp only [invariant] at total recurse
  by_cases zero : x = 0
  · subst x
    have same : count = value := by simpa using total
    subst same
    cil_loop_finish
  · cil_loop_advance
    unfold LoopTerminates LoopState.run
    -- Decrement's own body runs to its result, leaving the caller's memory as it was.
    refine WP.call (helperPost := fun result => result = (m, [.scalar (.i32 (x - 1))]))
      countCalls.found decrementSite.call (by cil_checked_step []) ?_ ?_
    · refine WP.exact_iff.mpr ?_
      dsimp only [Execution]
      cil_checked_steps []
    intro final values called
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj called
    change LoopTerminates Extracted.program countCalls args _ ⟨_, _, _, _⟩
    dsimp only [List.append_nil]
    cil_loop_recurse recurse (x - 1, count + 1)
    case invariant =>
      show count + 1 + (x - 1) = value
      rw [← total]
      bv_omega
    case measure => exact measure_falls zero
#print axioms terminates_stepped

/-- `CountCalls` returns its input for every `uint`, stepping `Decrement` at each call. -/
theorem correctness_stepped : CIL.Safety.Ensures Extracted.program countCalls
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Memory.empty)
    (fun args _ _ values => values = args) := by
  apply ensures_of_loop
  intro args initial permitted
  obtain ⟨x, rfl, rfl⟩ := permitted
  obtain ⟨remaining, counted, entered, enter⟩ := entry.checked x
  have started :
      LoopTerminates Extracted.program countCalls [.scalar (.i32 x)]
        (fun _ values => values = [.scalar (.i32 x)])
        ⟨0, entry.frame remaining counted, [], entered⟩ := by
    cil_loop_recurse (terminates_stepped [.scalar (.i32 x)] x) (x, 0)
    case invariant => simp [invariant]
  exact ⟨countBody, entry.frame remaining counted, entered, countCalls.found, rfl, enter.setup,
    started⟩
#print axioms correctness_stepped

/-- `Decrement` returns its argument less one and changes no memory. -/
def decrementContract : MethodContract W32 W32 where
  args x := [.scalar (.i32 x)]
  results v := [.scalar (.i32 v)]
  pre _ _ := True
  footprint _ := []
  post x _ _ v := v = x - 1

/-- `Decrement` meets its contract. -/
theorem decrement_holds : decrementContract.Holds Extracted.program decrement := by
  rintro x m -
  refine MethodContract.Holds.intro m _ ?_ (Confined.refl _ m) rfl
  cil_checked_steps
#print axioms decrement_holds

/-- Every record's pinned bytes decode to the method at its index of the extraction. -/
theorem bodies_decode :
    decodedProgram? Extracted.profile Extracted.environment Extracted.methodEvidence =
      some Extracted.program :=
  decodedProgram?_eq_some Extracted.translation_valid.programBindingsValid
    (.cons ((Method.ofBody?_of_decodes Extracted.method0_body_validated).trans
        Extracted.method0_decoded)
      (.cons ((Method.ofBody?_of_decodes Extracted.method1_body_validated).trans
          Extracted.method1_decoded) .nil))
#print axioms bodies_decode

/-- The contract of `Decrement`, bound to its record and the bytes it decodes from. -/
theorem decrement_summary : ∃ record, Extracted.methodEvidence[decrement]? = some record ∧
    DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment decrement record.assembly record.original.token record.arguments
      [] decrementContract :=
  ⟨_, rfl, .of_decoded bodies_decode rfl ⟨_, Extracted.method1_body_validated⟩
    Extracted.method1_specialization_validated.1 decrement_holds
    (.of_sites [decrement] (by decide) (by decide) rfl)⟩
#print axioms decrement_summary

/-- Every summary of the index the loop's call enters is for the method that call names:
    `Decrement`'s metadata token, with no type arguments. -/
theorem decrement_named {pin : AssemblyPin} {token : Nat} {arguments : List TypeExpr}
    {models : List ModelledCall}
    (summary : DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment decrement pin token arguments models decrementContract) :
    token = Extracted.method1Original.token ∧ arguments = [] :=
  summary.site Extracted.method0_calls_validated decrementSite.call rfl rfl rfl rfl
    decrementSite.link
#print axioms decrement_named

/-- A summary of the loop's callee index bound to `CountCalls`' own token is refuted at the
    call. -/
theorem caller_token_refused {pin : AssemblyPin} {models : List ModelledCall}
    (summary : DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment decrement pin Extracted.method0Original.token [] models
      decrementContract) :
    False :=
  absurd (decrement_named summary).1 (by decide)
#print axioms caller_token_refused

/-- From every loop test, the loop returns its input, applying `summary` at each call. -/
theorem terminates {pin : AssemblyPin} {token : Nat} {arguments : List TypeExpr}
    (summary : DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment decrement pin token arguments [] decrementContract)
    (args : List CIL.Safety.Value) (value : W32) {remaining counted : Reference}
    (state : State remaining counted) (valid : invariant value state) :
    LoopTerminates Extracted.program countCalls args
      (fun _ values => values = [.scalar (.i32 value)]) (header remaining counted state) := by
  apply loop_terminates_induction Extracted.program countCalls args (header remaining counted)
    (invariant value) (fun s => s.values.1.toNat) _ ?_ state valid
  rintro ⟨⟨x, count⟩, m, frame⟩ total recurse
  dsimp only [invariant] at total recurse
  by_cases zero : x = 0
  · subst x
    have same : count = value := by simpa using total
    subst same
    cil_loop_finish
  · cil_loop_advance
    -- The callee may change only its empty footprint, so both locals survive the call.
    cil_loop_call (summary.holds (.nil _)) x at decrementSite
    -- The frame of the memory before the call is stale once `calledFrame` holds.
    clear frame
    cil_loop_recurse recurse (x - 1, count + 1)
    case invariant =>
      show count + 1 + (x - 1) = value
      rw [← total]
      bv_omega
    case measure => exact measure_falls zero
#print axioms terminates

/-- `CountCalls` returns its input for every `uint`, given only `Decrement`'s decoded
    summary. -/
theorem correctness : CIL.Safety.Ensures Extracted.program countCalls
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Memory.empty)
    (fun args _ _ values => values = args) := by
  obtain ⟨record, -, summary⟩ := decrement_summary
  apply ensures_of_loop
  intro args initial permitted
  obtain ⟨x, rfl, rfl⟩ := permitted
  obtain ⟨remaining, counted, entered, enter⟩ := entry.checked x
  have started :
      LoopTerminates Extracted.program countCalls [.scalar (.i32 x)]
        (fun _ values => values = [.scalar (.i32 x)])
        ⟨0, entry.frame remaining counted, [], entered⟩ := by
    cil_loop_recurse (terminates summary [.scalar (.i32 x)] x) (x, 0)
    case invariant => simp [invariant]
  exact ⟨countBody, entry.frame remaining counted, entered, countCalls.found, rfl, enter.setup,
    started⟩
#print axioms correctness

end ExampleProof
