import Extracted
import Examples.Support
import CIL.Safety.StepComposition


open CIL CIL.Safety
namespace ExampleProof

/-- The checked sum equals natural-number addition whenever it fits. -/
theorem correctness (x y : W32) (fits : x.toNat + y.toNat < 2^32) :
    (CIL.Safety.invoke Extracted.program 4 0
      [.scalar (.i32 x), .scalar (.i32 y)] Examples.empty).map Prod.snd =
        .ok [.scalar (.i32 (BitVec.ofNat 32 (x.toNat + y.toNat)))] := by
  have calculation : checkedValues .add false (.i32 x) (.i32 y) =
      .ok (.i32 (BitVec.ofNat 32 (x.toNat + y.toNat))) := by
    have range : 0 ≤ (x.toNat : Int) + y.toNat ∧ (x.toNat : Int) + y.toNat < 2^32 := by omega
    simp only [checkedValues, checkedBits, Bool.false_eq_true, ite_false]
    rw [ite_eq_left range]
    rfl
  let args : List CIL.Safety.Value := [.scalar (.i32 x), .scalar (.i32 y)]
  let frame : Frame := ⟨0, [], [], []⟩
  let result := BitVec.ofNat 32 (x.toNat + y.toNat)
  have executed : CIL.Safety.step Extracted.method0 (.checkedArithmetic .add false) 2 args frame
      [.scalar (.i32 y), .scalar (.i32 x)] Examples.empty =
      .ok (.next 3 [.scalar (.i32 result)] frame Examples.empty) := by
    simp only [CIL.Safety.step, calculation]
    rfl
  have first : CIL.Safety.step Extracted.method0 (.arg 0) 0 args frame [] Examples.empty =
      .ok (.next 1 [.scalar (.i32 x)] frame Examples.empty) := rfl
  have second : CIL.Safety.step Extracted.method0 (.arg 1) 1 args frame [.scalar (.i32 x)] Examples.empty =
      .ok (.next 2 [.scalar (.i32 y), .scalar (.i32 x)] frame Examples.empty) := rfl
  have ran : CIL.Safety.run Extracted.program 4 0 0 args frame [] Examples.empty =
      .ok (Examples.empty, [.scalar (.i32 result)]) := by
    rw [run_next Extracted.lookup0 Extracted.method0_instruction0 first]
    rw [run_next Extracted.lookup0 Extracted.method0_instruction1 second]
    rw [run_next Extracted.lookup0 Extracted.method0_instruction2 executed]
    rfl
  have invoked := invoke_of_run (memory := Examples.empty) Extracted.lookup0 (by rfl) (by rfl) ran
  rw [invoked]
  rfl

#print axioms correctness
end ExampleProof
