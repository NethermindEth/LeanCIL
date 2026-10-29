import Extracted
import Examples.Support

open CIL
namespace ExampleProof

theorem correctness (x y : W64) :
    ∃ result : W64,
      (CIL.Safety.invoke Extracted.program 4 0
        [.scalar (.i64 x), .scalar (.i64 y)] Examples.empty).map Prod.snd =
          .ok [.scalar (.i64 result)] ∧
      result.toNat = (x.toNat + y.toNat) % 2^64 := by
  refine ⟨x + y, ?_, BitVec.toNat_add x y⟩
  rfl

#print axioms correctness
end ExampleProof
