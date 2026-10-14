import Extracted
import Examples.Support

namespace ExampleProof

/-- A value constructor returns the byte representation of every 64-bit input. -/
theorem correctness (x : CIL.W64) :
    (CIL.Safety.invoke Extracted.program 16 0 [.scalar (.i64 x)] Examples.empty).map Prod.snd =
      .ok [.scalar (.aggregate (CIL.Safety.numberBytes x.toNat 8))] := by
  rfl

#print axioms correctness
end ExampleProof
