import Extracted
import Examples.Support
import CIL.Verification
import CIL.Safety.NumericLocals

open CIL.Safety
open CIL (W32)
namespace ExampleProof

private def frame : Frame := ⟨0, [.bytes .word32 ⟨0, 0⟩], [0], []⟩
private def header (state : W32 × Memory) : LoopState := ⟨7, frame, [], state.2⟩
private def invariant (state : W32 × Memory) : Prop :=
  loadLocal state.2 (.bytes .word32 ⟨0, 0⟩) = .ok (.scalar (.i32 state.1)) ∧
  access state.2 ⟨0, 0⟩ 4 1 true = .ok ()

private theorem load (pc : Nat) (args : List CIL.Safety.Value) (x : W32) (m : Memory)
    (loaded : loadLocal m (.bytes .word32 ⟨0, 0⟩) = .ok (.scalar (.i32 x))) :
    CIL.Safety.step Extracted.method0 (.local 0) pc args frame [] m =
      .ok (.next (pc + 1) [.scalar (.i32 x)] frame m) := by
  simp only [CIL.Safety.step, frame, List.getElem?_cons_zero, loaded,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem branch (args : List CIL.Safety.Value) (x : W32) (m : Memory) :
    CIL.Safety.step Extracted.method0 (.brnonzero 3) 8 args frame [.scalar (.i32 x)] m =
      .ok (.next (if x = 0 then 9 else 3) [] frame m) := by
  simp [CIL.Safety.step, pureArity, numericValue, scalars, CIL.step, CIL.truth,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem terminates (args : List CIL.Safety.Value) (state : W32 × Memory)
    (valid : invariant state) :
    LoopTerminates Extracted.program 0 args (fun _ values => values = [.scalar (.i32 0)])
      (header state) := by
  apply loop_terminates Extracted.program 0 args header invariant (fun s => s.1.toNat)
    (fun _ values => values = [.scalar (.i32 0)]) ?_ state valid
  intro state valid
  obtain ⟨x, m⟩ := state
  obtain ⟨loaded, writable⟩ := valid
  have h7 := load 7 args x m loaded
  have h8 := branch args x m
  by_cases zero : x = 0
  · left
    subst x
    refine ⟨4, leaveFrame frame m, [.scalar (.i32 0)], ?_, rfl⟩
    change CIL.Safety.run _ 4 0 7 args frame [] m = _
    rw [run_next Extracted.lookup0 Extracted.method0_instruction7 h7]
    simp only [ite_true] at h8
    rw [run_next Extracted.lookup0 Extracted.method0_instruction8 h8]
    rw [run_next Extracted.lookup0 Extracted.method0_instruction9 (load 9 args 0 m loaded)]
    rfl
  · right
    obtain ⟨updated, written, stored, bytes⟩ := store_numeric_local .word32 (.i32 (x - 1))
      (x - 1).toNat rfl writable
    have h6 : CIL.Safety.step Extracted.method0 (.setLocal 0) 6 args frame
        [.scalar (.i32 (x - 1))] m = .ok (.next 7 [] frame updated) := by
      simp only [CIL.Safety.step, frame, List.getElem?_cons_zero, stored,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      rfl
    have readback := load_numeric_local .word32 (.i32 (x - 1)) (x - 1).toNat rfl bytes
    obtain ⟨allocation, ready⟩ := access_requirements writable
    refine ⟨(x - 1, updated), 6, ⟨readback, (ready.after_write written).access⟩, ?_, ?_⟩
    · have positive : 0 < x.toNat := by
        have : x.toNat ≠ 0 := by intro h; exact zero (BitVec.eq_of_toNat_eq h)
        omega
      rw [BitVec.toNat_sub_of_le]
      · simp; omega
      · change 1 ≤ x.toNat
        omega
    · intro fuel
      change CIL.Safety.run _ (fuel + 6) 0 7 args frame [] m =
        CIL.Safety.run _ fuel 0 7 args frame [] updated
      rw [run_next Extracted.lookup0 Extracted.method0_instruction7 h7]
      simp only [zero, ite_false] at h8
      rw [run_next Extracted.lookup0 Extracted.method0_instruction8 h8]
      rw [run_next Extracted.lookup0 Extracted.method0_instruction3 (load 3 args x m loaded)]
      rw [run_next Extracted.lookup0 Extracted.method0_instruction4 (show
        CIL.Safety.step Extracted.method0 (.const32 1) 4 args frame [.scalar (.i32 x)] m =
          .ok (.next 5 [.scalar (.i32 1), .scalar (.i32 x)] frame m) from rfl)]
      rw [run_next Extracted.lookup0 Extracted.method0_instruction5 (show
        CIL.Safety.step Extracted.method0 .sub 5 args frame [.scalar (.i32 1), .scalar (.i32 x)] m =
          .ok (.next 6 [.scalar (.i32 (x - 1))] frame m) from rfl)]
      rw [run_next Extracted.lookup0 Extracted.method0_instruction6 h6]

-- Every uint input terminates, including zero and UInt32.MaxValue. The loop's
-- natural measure decreases before modular subtraction can wrap around.
theorem correctness : CIL.Safety.Ensures Extracted.program 0
    (fun args initial => ∃ x : W32, args = [.scalar (.i32 x)] ∧ initial = Examples.empty)
    (fun _ _ _ values => values = [.scalar (.i32 0)]) := by
  apply ensures_of_loop
  intro args initial permitted
  obtain ⟨x, rfl, rfl⟩ := permitted
  let entered := ((enterFrame Extracted.method0 [] Examples.empty).toOption.getD
    (frame, Examples.empty)).2
  have setup : enterFrame Extracted.method0 [.scalar (.i32 x)] Examples.empty = .ok (frame, entered) := by
    rfl
  have writable : access entered ⟨0, 0⟩ 4 1 true = .ok () := by rfl
  obtain ⟨updated, written, stored, bytes⟩ := store_numeric_local .word32 (.i32 x) x.toNat rfl writable
  have readback := load_numeric_local .word32 (.i32 x) x.toNat rfl bytes
  obtain ⟨allocation, ready⟩ := access_requirements writable
  obtain ⟨fuel, final, values, executed, satisfied⟩ :=
    terminates [.scalar (.i32 x)] (x, updated) ⟨readback, (ready.after_write written).access⟩
  refine ⟨Extracted.method0, frame, entered, Extracted.lookup0, rfl, setup,
    fuel + 3, final, values, ?_, satisfied⟩
  change CIL.Safety.run _ (fuel + 3) 0 0 [.scalar (.i32 x)] frame [] entered = _
  rw [run_next Extracted.lookup0 Extracted.method0_instruction0 (show
    CIL.Safety.step Extracted.method0 (.arg 0) 0 [.scalar (.i32 x)] frame [] entered =
      .ok (.next 1 [.scalar (.i32 x)] frame entered) from rfl)]
  have assigned : CIL.Safety.step Extracted.method0 (.setLocal 0) 1 [.scalar (.i32 x)] frame
      [.scalar (.i32 x)] entered = .ok (.next 2 [] frame updated) := by
    simp only [CIL.Safety.step, frame, List.getElem?_cons_zero, stored,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  rw [run_next Extracted.lookup0 Extracted.method0_instruction1 assigned]
  rw [run_next Extracted.lookup0 Extracted.method0_instruction2 (show
    CIL.Safety.step Extracted.method0 (.branch 7) 2 [.scalar (.i32 x)] frame [] updated =
      .ok (.next 7 [] frame updated) from rfl)]
  exact executed

#print axioms correctness
end ExampleProof
