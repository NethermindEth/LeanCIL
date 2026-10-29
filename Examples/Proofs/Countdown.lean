import Extracted
import Examples.Support
import CIL.Verification
import CIL.Safety.NumericLocals
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

private theorem terminates (args : List CIL.Safety.Value) (state : W32 × Memory)
    (valid : invariant state) :
    LoopTerminates Extracted.program 0 args (fun _ values => values = [.scalar (.i32 0)])
      (header state) := by
  apply loop_terminates Extracted.program 0 args header invariant (fun s => s.1.toNat)
    (fun _ values => values = [.scalar (.i32 0)]) ?_ state valid
  intro state valid
  obtain ⟨x, m⟩ := state
  obtain ⟨loaded, writable⟩ := valid
  by_cases zero : x = 0
  · left
    subst x
    cil_loop_finish [entry.frame, header, cutpoint, loaded]
  · right
    have nonzero : x ≠ 0#32 := zero
    obtain ⟨updated, written, stored, bytes⟩ := store_numeric_local .word32 (.i32 (x - 1))
      (x - 1).toNat rfl writable
    have readback := load_numeric_local .word32 (.i32 (x - 1)) (x - 1).toNat rfl bytes
    simp only [BitVec.ofNat_eq_ofNat] at stored readback
    obtain ⟨allocation, ready⟩ := access_requirements writable
    have path : LoopReaches Extracted.program 0 args (header (x, m)) (header (x - 1, updated)) := by
      cil_loop_steps [entry.frame, header, cutpoint, loaded, stored, readback, nonzero]
    obtain ⟨cost, segment⟩ := path
    refine ⟨(x - 1, updated), cost, ⟨readback, (ready.after_write written).access⟩, ?_, segment⟩
    have positive : 0 < x.toNat := by
      have : x.toNat ≠ 0 := by intro h; exact zero (BitVec.eq_of_toNat_eq h)
      omega
    rw [BitVec.toNat_sub_of_le]
    · simp; omega
    · change 1 ≤ x.toNat
      omega

-- The invariant cutpoint is found in compiled code. Every path and its cost are
-- derived by checked stepping, so instruction positions and block order are not assumptions.
theorem correctness : CIL.Safety.Ensures Extracted.program 0
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Examples.empty)
    (fun _ _ _ values => values = [.scalar (.i32 0)]) := by
  apply ensures_of_loop
  intro args initial permitted
  obtain ⟨x, rfl, rfl⟩ := permitted
  let entered := entry.memory
  have setup : enterFrame Extracted.method0 [.scalar (.i32 x)] Examples.empty = .ok (entry.frame, entered) := by
    rfl
  have writable : access entered entry.home0 4 1 true = .ok () := by rfl
  obtain ⟨updated, written, stored, bytes⟩ := store_numeric_local .word32 (.i32 x) x.toNat rfl writable
  have readback := load_numeric_local .word32 (.i32 x) x.toNat rfl bytes
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have entryPath : LoopReaches Extracted.program 0 [.scalar (.i32 x)]
      ⟨0, entry.frame, [], entered⟩ (header (x, updated)) := by
    cil_loop_steps [entry.frame, header, cutpoint, stored, readback]
  obtain ⟨fuel, final, values, executed, satisfied⟩ := loop_reaches_terminates entryPath
    (terminates [.scalar (.i32 x)] (x, updated) ⟨readback, (ready.after_write written).access⟩)
  exact ⟨Extracted.method0, entry.frame, entered, Extracted.lookup0, rfl, setup,
    fuel, final, values, executed, satisfied⟩

#print axioms correctness
end ExampleProof
