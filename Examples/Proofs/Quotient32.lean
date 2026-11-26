import Extracted
import CIL.Safety.SymbolicExecution

open CIL CIL.Safety
namespace ExampleProof

/-- Every nonzero divisor yields the natural-number quotient and preserves caller memory. -/
theorem correctness_framed (memory : CIL.Safety.Memory) (x y : W32) (nonzero : y ≠ 0) :
    CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i32 x), .scalar (.i32 y)] memory =
      .ok (memory, [.scalar (.i32 (BitVec.ofNat 32 (x.toNat / y.toNat)))]) := by
  have calculation : divideValues false false (.i32 x) (.i32 y) =
      .ok (.i32 (BitVec.ofNat 32 (x.toNat / y.toNat))) := by
    simp only [divideValues, divideBits, nonzero, ite_false]
    rfl
  cil_checked_steps [calculation]

#print axioms correctness_framed

/-- Every nonzero divisor yields the natural-number quotient, for all inputs. -/
theorem correctness (x y : W32) (nonzero : y ≠ 0) :
    (CIL.Safety.invoke Extracted.program 4 0
      [.scalar (.i32 x), .scalar (.i32 y)] Memory.empty).map Prod.snd =
        .ok [.scalar (.i32 (BitVec.ofNat 32 (x.toNat / y.toNat)))] := by
  rw [correctness_framed Memory.empty x y nonzero]
  rfl

#print axioms correctness
end ExampleProof
