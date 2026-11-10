import Extracted
import CIL.Safety.SymbolicExecution

open CIL CIL.Safety
namespace ExampleProof

/-- Every nonzero divisor yields the natural-number quotient, for all inputs. -/
theorem correctness (x y : W32) (nonzero : y ≠ 0) :
    (CIL.Safety.invoke Extracted.program 4 0
      [.scalar (.i32 x), .scalar (.i32 y)] Memory.empty).map Prod.snd =
        .ok [.scalar (.i32 (BitVec.ofNat 32 (x.toNat / y.toNat)))] := by
  have calculation : divideValues false false (.i32 x) (.i32 y) =
      .ok (.i32 (BitVec.ofNat 32 (x.toNat / y.toNat))) := by
    simp only [divideValues, divideBits, nonzero, ite_false]
    rfl
  have ran : CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i32 x), .scalar (.i32 y)]
      Memory.empty =
        .ok (Memory.empty, [.scalar (.i32 (BitVec.ofNat 32 (x.toNat / y.toNat)))]) := by
    cil_checked_steps [calculation]
  rw [ran]
  rfl

#print axioms correctness
end ExampleProof