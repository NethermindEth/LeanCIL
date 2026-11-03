import Extracted
import CIL.Verification
import CIL.Safety.LoopVC
import CIL.Safety.LoopScaffold

open CIL.Safety
open CIL (W32)
namespace ExampleProof

bind_entry entry (x : W32) := Extracted.method0 with [.scalar (.i32 x)] from Memory.empty
  allocating Memory.empty_wellFormed
bind_cutpoint cutpoint (home : Reference) := Extracted.method0 matching
  (fun op => match op with | .brnonzero _ => true | _ => false) with entry.frame home
/-- The remaining count, held by the frame's only local, with the frame facts. -/
private abbrev State (home : Reference) :=
  FrameState [] Memory.empty [.word32] W32 (fun _ => [.bytes .word32 home])
    fun x => [some (.i32 x)]
private def header (home : Reference) (state : State home) : LoopState :=
  cutpoint home [.scalar (.i32 state.values)] state.memory

-- The invariant cutpoint is found in compiled code. Every path and its cost are
-- derived by checked stepping, so instruction positions and block order are not assumptions.
theorem correctness : CIL.Safety.Ensures Extracted.program 0
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Memory.empty)
    (fun _ _ _ values => values = [.scalar (.i32 0)]) := by
  rintro args initial ⟨x, rfl, rfl⟩
  obtain ⟨home, entered, setup, -, -, entryFrame⟩ := entry.checked x
  obtain ⟨started, stored, frame, -⟩ := (entryFrame []).store 0 (.i32 x) rfl
  refine invoke_loop_vc Extracted.lookup0 rfl setup (header home) (fun _ => True)
    (fun s => s.values.toNat) ⟨x, started, frame⟩
    (by cil_loop_steps [entry.frame, header, cutpoint, stored, frame.load 0]) trivial ?_
  rintro ⟨x, m, frame⟩ -
  have loaded := frame.load 0
  by_cases zero : x = 0
  · left
    subst x
    cil_loop_finish [entry.frame, header, cutpoint, loaded]
  · have nonzero : x ≠ 0#32 := zero
    obtain ⟨updated, stored, next, -⟩ := frame.store 0 (.i32 (x - 1)) rfl
    cil_loop_continue ⟨x - 1, updated, next⟩
      [entry.frame, header, cutpoint, loaded, stored, next.load 0, nonzero]
    · trivial
    · have positive : 0 < x.toNat := by
        have : x.toNat ≠ 0 := by intro h; exact zero (BitVec.eq_of_toNat_eq h)
        omega
      rw [BitVec.toNat_sub_of_le]
      · simp; omega
      · change 1 ≤ x.toNat
        omega

#print axioms correctness
end ExampleProof
