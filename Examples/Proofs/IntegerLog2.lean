import Extracted
import Examples.Support

namespace ExampleProof

/-- The extracted helper returns the natural-number floor logarithm, with log₂ 0 = 0. -/
theorem correctness (x : CIL.W64) :
    (CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 x)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i32 (BitVec.ofNat 32 x.toNat.log2))] := by
  rfl

#print axioms correctness
end ExampleProof
