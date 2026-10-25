import Extracted
import Examples.Support
import CIL.Safety.StepComposition

open CIL CIL.Safety
namespace ExampleProof

/-- A checked narrowing conversion preserves every representable natural value. -/
theorem correctness (x : W64) (fits : x.toNat < 2^32) :
    (CIL.Safety.invoke Extracted.program 3 0 [.scalar (.i64 x)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i32 (BitVec.ofNat 32 x.toNat))] := by
  have range : 0 ≤ (x.toNat : Int) ∧ (x.toNat : Int) < 2^32 := by omega
  have calculation : convertInteger 32 false true (.i64 x) =
      .ok (.i32 (BitVec.ofNat 32 x.toNat)) := by
    simp only [convertInteger,
      show (32 != 8 && 32 != 16 && 32 != 32 && 32 != 64) = false from rfl,
      Bool.false_eq_true, ite_false, ite_true]
    simp only [convertNumber, Bool.false_eq_true, ite_false]
    rw [ite_eq_left range]
    rfl
  let args : List CIL.Safety.Value := [.scalar (.i64 x)]
  let frame : Frame := ⟨0, [], [], [], 0⟩
  have loaded : CIL.Safety.step Extracted.method0 (.arg 0) 0 args frame [] Examples.empty =
      .ok (.next 1 [.scalar (.i64 x)] frame Examples.empty) := rfl
  have converted : CIL.Safety.step Extracted.method0 (.checkedConvert 32 false true) 1 args frame
      [.scalar (.i64 x)] Examples.empty =
      .ok (.next 2 [.scalar (.i32 (BitVec.ofNat 32 x.toNat))] frame Examples.empty) := by
    simp only [CIL.Safety.step, calculation]
    rfl
  have ran : CIL.Safety.run Extracted.program 3 0 0 args frame [] Examples.empty =
      .ok (Examples.empty, [.scalar (.i32 (BitVec.ofNat 32 x.toNat))]) := by
    rw [run_next Extracted.lookup0 Extracted.method0_instruction0 loaded]
    rw [run_next Extracted.lookup0 Extracted.method0_instruction1 converted]
    rfl
  have invoked := invoke_of_run (memory := Examples.empty) Extracted.lookup0 (by rfl) (by rfl) ran
  rw [invoked]
  rfl

#print axioms correctness
end ExampleProof
