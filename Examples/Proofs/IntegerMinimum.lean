import Extracted
import Examples.Support

namespace ExampleProof

/-- The compiled method returns the mathematical signed minimum for every input. -/
theorem correctness (x y : CIL.W64) :
    (CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 x), .scalar (.i64 y)]
      Examples.empty).map Prod.snd =
      .ok [.scalar (.i64 (BitVec.ofInt 64 (min x.toInt y.toInt)))] := by
  rfl

#print axioms correctness
end ExampleProof
