import Extracted
import Examples.Support
import CIL.Safety.SymbolicExecution

open CIL CIL.Safety
namespace ExampleProof

/-- The checked sum equals natural-number addition whenever it fits. -/
theorem correctness (memory : CIL.Safety.Memory) (x y : W64) (fits : x.toNat + y.toNat < 2^64) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0
      [.scalar (.i64 x), .scalar (.i64 y)] memory =
        .ok (memory, [.scalar (.i64 (BitVec.ofNat 64 (x.toNat + y.toNat)))]) := by
  have calculation : checkedValues .add false (.i64 x) (.i64 y) =
      .ok (.i64 (BitVec.ofNat 64 (x.toNat + y.toNat))) := by
    have range : 0 ≤ (x.toNat : Int) + y.toNat ∧ (x.toNat : Int) + y.toNat < 2^64 := by omega
    simp only [checkedValues, checkedBits, Bool.false_eq_true, ite_false]
    rw [ite_eq_left range]
    rfl
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [calculation]

#print axioms correctness
end ExampleProof
