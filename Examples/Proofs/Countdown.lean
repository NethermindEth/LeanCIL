import Extracted
import Examples.Support
import CIL.Verification
import CIL.Safety.LoopVC
import CIL.Safety.LoopScaffold

open CIL.Safety
open CIL (W32)
namespace ExampleProof

bind_entry entry := Extracted.method0 with [] from Examples.empty
bind_cutpoint cutpoint := Extracted.method0 matching
  (fun op => match op with | .brnonzero _ => true | _ => false) with entry.frame
private def header (state : W32 × Memory) : LoopState :=
  cutpoint [.scalar (.i32 state.1)] state.2
private def invariant (state : W32 × Memory) : Prop :=
  loadLocal state.2 (.bytes .word32 entry.home0) = .ok (.scalar (.i32 state.1)) ∧
  access state.2 entry.home0 4 1 true = .ok ()

-- The invariant cutpoint is found in compiled code. Every path and its cost are
-- derived by checked stepping, so instruction positions and block order are not assumptions.
theorem correctness : CIL.Safety.Ensures Extracted.program 0
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Examples.empty)
    (fun _ _ _ values => values = [.scalar (.i32 0)]) := by
  rintro args initial ⟨x, rfl, rfl⟩
  have writable : access entry.memory entry.home0 4 1 true = .ok () := by rfl
  cil_store_vc updated stored readback nextWritable := .word32 (.i32 x) using writable
  refine invoke_loop_vc Extracted.lookup0 rfl entry.checked header invariant (fun s => s.1.toNat)
    (x, updated) (by cil_loop_steps [entry.frame, header, cutpoint, stored, readback])
    ⟨readback, nextWritable⟩ ?_
  rintro ⟨x, m⟩ ⟨loaded, writable⟩
  by_cases zero : x = 0
  · left
    subst x
    cil_loop_finish [entry.frame, header, cutpoint, loaded]
  · have nonzero : x ≠ 0#32 := zero
    cil_store_vc updated stored readback nextWritable := .word32 (.i32 (x - 1)) using writable
    cil_loop_continue (x - 1, updated)
      [entry.frame, header, cutpoint, loaded, stored, readback, nonzero]
    · exact ⟨readback, nextWritable⟩
    · have positive : 0 < x.toNat := by
        have : x.toNat ≠ 0 := by intro h; exact zero (BitVec.eq_of_toNat_eq h)
        omega
      rw [BitVec.toNat_sub_of_le]
      · simp; omega
      · change 1 ≤ x.toNat
        omega

#print axioms correctness
end ExampleProof
