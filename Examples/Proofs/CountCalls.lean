import Extracted
import CIL.Verification
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.NumericLocals
import CIL.Safety.LoopContract
import CIL.Safety.LoopScaffold

open CIL.Safety
open CIL (W32)
namespace ExampleProof

bind_method countCalls countBody := "System.UInt32 Examples.Loops::CountCalls(System.UInt32)"
bind_callee decrement decrementBody :=
  "System.UInt32 Examples.Loops::Decrement(System.UInt32)" from countBody
bind_call decrementSite := decrement from countBody

def decrementContract : MethodContract W32 W32 where
  args x := [.scalar (.i32 x)]
  results v := [.scalar (.i32 v)]
  pre _ _ := True
  footprint _ := []
  post x _ _ v := v = x - 1

theorem decrement_holds : decrementContract.Holds Extracted.program decrement := by
  rintro x m -
  refine MethodContract.Holds.intro m _ ?_ (Confined.refl _ m) rfl
  cil_checked_steps

bind_entry entry (x : W32) := countBody with [.scalar (.i32 x)] from Memory.empty
  allocating Memory.empty_wellFormed
private def guard : Nat := instructionLocation countBody fun op =>
  match op with | .brnonzero _ => true | _ => false
/-- The remaining count and the calls made so far, held by the frame's two locals. -/
private abbrev State (remaining counted : Reference) :=
  FrameState [] Memory.empty [.word32, .word32] (W32 × W32)
    (fun _ => [.bytes .word32 remaining, .bytes .word32 counted])
    fun values => [some (.i32 values.1), some (.i32 values.2)]
/-- The loop head holds the remaining count on the stack. -/
private def header (remaining counted : Reference) (state : State remaining counted) : LoopState :=
  ⟨guard, entry.frame remaining counted, [.scalar (.i32 state.values.1)], state.memory⟩
/-- `count + remaining` is the input. -/
private def invariant {remaining counted : Reference} (value : W32)
    (state : State remaining counted) : Prop :=
  state.values.2 + state.values.1 = value

/-- Uses only `decrementContract` at the call site; the helper body is never unfolded. -/
theorem terminates (holds : decrementContract.Holds Extracted.program decrement)
    (args : List CIL.Safety.Value) (value : W32) {remaining counted : Reference}
    (state : State remaining counted) (valid : invariant value state) :
    LoopTerminates Extracted.program countCalls args
      (fun _ values => values = [.scalar (.i32 value)]) (header remaining counted state) := by
  apply loop_terminates_induction Extracted.program countCalls args (header remaining counted)
    (invariant value) (fun s => s.values.1.toNat) _ ?_ state valid
  rintro ⟨⟨x, count⟩, m, frame⟩ total recurse
  dsimp only [invariant] at total recurse
  have loaded0 := frame.load 0
  have loaded1 := frame.load 1
  by_cases zero : x = 0
  · subst x
    have same : count = value := by simpa using total
    subst same
    cil_loop_finish [entry.frame, header, loaded0, loaded1]
  · have nonzero : x ≠ 0#32 := zero
    cil_loop_advance [entry.frame, header, loaded0, nonzero]
    -- The callee may change only its empty footprint, so both locals survive in `calledFrame`.
    cil_loop_call holds x at decrementSite [entry.frame, loaded0]
    obtain ⟨m1, stored0, frame1, -⟩ := calledFrame.store 0 (.i32 (x - 1)) rfl
    obtain ⟨m2, stored1, frame2, -⟩ := frame1.store 1 (.i32 (count + 1)) rfl
    -- The next head is chosen only now, from the memory the contract returned.
    refine loop_reaches_terminates (target := header remaining counted ⟨(x - 1, count + 1), m2,
      frame2⟩) ?_ (recurse ⟨(x - 1, count + 1), m2, frame2⟩
        (show count + 1 + (x - 1) = value by rw [← total]; bv_omega) ?_)
    · cil_loop_steps [entry.frame, header, stored0, stored1, frame1.load 1, frame2.load 0]
    have positive : 0 < x.toNat := by
      have : x.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
      omega
    show (x - 1).toNat < x.toNat
    rw [BitVec.toNat_sub_of_le]
    · simp; omega
    · change 1 ≤ x.toNat
      omega

/-- `CountCalls` returns its input for every `uint`, given only the helper's contract. -/
theorem count_calls (holds : decrementContract.Holds Extracted.program decrement) :
    CIL.Safety.Ensures Extracted.program countCalls
      (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Memory.empty)
      (fun args _ _ values => values = args) := by
  apply ensures_of_loop
  intro args initial permitted
  obtain ⟨x, rfl, rfl⟩ := permitted
  obtain ⟨remaining, counted, entered, enter⟩ := entry.checked x
  obtain ⟨m1, stored0, frame1, -⟩ := (enter.frame []).store 0 (.i32 x) rfl
  obtain ⟨m2, stored1, frame2, -⟩ := frame1.store 1 (.i32 0) rfl
  have entryPath : LoopReaches Extracted.program countCalls [.scalar (.i32 x)]
      ⟨0, entry.frame remaining counted, [], entered⟩
      (header remaining counted ⟨(x, 0), m2, frame2⟩) := by
    cil_loop_steps [entry.frame, header, stored0, stored1, frame1.load 0, frame2.load 0]
  obtain ⟨fuel, final, values, executed, satisfied⟩ := loop_reaches_terminates entryPath
    (terminates holds [.scalar (.i32 x)] x ⟨(x, 0), m2, frame2⟩ (by simp [invariant]))
  exact ⟨countBody, entry.frame remaining counted, entered, countCalls.found, rfl, enter.setup,
    fuel, final, values, executed, satisfied⟩

theorem correctness : CIL.Safety.Ensures Extracted.program countCalls
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Memory.empty)
    (fun args _ _ values => values = args) :=
  count_calls decrement_holds

#print axioms correctness
end ExampleProof
