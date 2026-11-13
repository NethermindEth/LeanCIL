import Extracted
import CIL.Verification
import CIL.MethodIdentity
import CIL.StructuralLabels
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
  by_cases zero : x = 0
  · subst x
    have same : count = value := by simpa using total
    subst same
    cil_loop_finish
  · cil_loop_advance
    -- The callee may change only its empty footprint, so both locals survive the call.
    cil_loop_call holds x at decrementSite
    cil_loop_recurse recurse (x - 1, count + 1)
    case invariant =>
      show count + 1 + (x - 1) = value
      rw [← total]
      bv_omega
    case measure =>
      show (x - 1).toNat < x.toNat
      have positive : 0 < x.toNat := by
        have : x.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
        omega
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
  have started :
      LoopTerminates Extracted.program countCalls [.scalar (.i32 x)]
        (fun _ values => values = [.scalar (.i32 x)])
        ⟨0, entry.frame remaining counted, [], entered⟩ := by
    cil_loop_recurse (terminates holds [.scalar (.i32 x)] x) (x, 0)
    case invariant => simp [invariant]
  exact ⟨countBody, entry.frame remaining counted, entered, countCalls.found, rfl, enter.setup,
    started⟩

theorem correctness : CIL.Safety.Ensures Extracted.program countCalls
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Memory.empty)
    (fun args _ _ values => values = args) :=
  count_calls decrement_holds

#print axioms decrement_holds
#print axioms terminates
#print axioms count_calls
#print axioms correctness
end ExampleProof
