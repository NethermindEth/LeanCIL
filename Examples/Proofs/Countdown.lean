import Extracted
import CIL.Verification
import CIL.Safety.LoopScaffold

open CIL.Safety
open CIL (W32)
namespace ExampleProof

bind_entry entry (x : W32) := Extracted.method0 with [.scalar (.i32 x)] from Memory.empty
  allocating Memory.empty_wellFormed

/-- The remaining count, held by the frame's only local, with the frame facts. -/
private abbrev State (home : Reference) :=
  FrameState [] Memory.empty [.word32] W32 (fun _ => [.bytes .word32 home])
    fun x => [some (.i32 x)]

/-- The loop test, with the remaining count on the stack. It is found as the only conditional
    branch of the compiled code, so no instruction position or block order is assumed. -/
bind_cutpoint header (home : Reference) (state : State home) :=
  Extracted.method0 matching (fun op => match op with | .brtrue _ => true | _ => false)
  with entry.frame home, [.scalar (.i32 state.values)], state.memory

theorem correctness : CIL.Safety.Ensures Extracted.program 0
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Memory.empty)
    (fun _ _ _ values => values = [.scalar (.i32 0)]) := by
  rintro args initial ⟨x, rfl, rfl⟩
  obtain ⟨home, entered, enter⟩ := entry.checked x
  refine invoke_loop_satisfies Extracted.program_method0 rfl enter.setup (header home)
    (fun _ => True)
    (fun s => s.values.toNat) (fun start => ?_) ?_
  · cil_loop_recurse start x
    case invariant => trivial
  rintro ⟨x, m, frame⟩ - recurse
  by_cases zero : x = 0#32
  · cil_loop_finish [zero]
  · cil_loop_recurse recurse (x - 1)
    case invariant => trivial
    case measure =>
      show (x - 1).toNat < x.toNat
      have positive : 0 < x.toNat := by
        have : x.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
        omega
      rw [BitVec.toNat_sub_of_le]
      · simp; omega
      · change 1 ≤ x.toNat
        omega

#print axioms correctness

/-- From empty memory, every count returns zero. -/
def countdownContract : MethodContract W32 where
  args input := [.scalar (.i32 input)]
  pre _ memory := memory = Memory.empty
  footprint _ := []
  post _ _ _ values := values = [.scalar (.i32 0)]

/-- `correctness` as `countdownContract`, which also states that no caller storage changes. -/
theorem holds : countdownContract.Holds Extracted.program 0 := by
  rintro value _ rfl
  obtain ⟨fuel, final, values, ran, result⟩ := correctness _ _ ⟨value, rfl, rfl⟩
  exact ⟨fuel, (final, values), ran, by constructor <;> simp [Memory.empty], values, rfl, result⟩

#print axioms holds
end ExampleProof
