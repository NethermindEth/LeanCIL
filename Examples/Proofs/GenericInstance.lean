import Extracted
import Examples.Support

namespace ExampleProof

/-- Fixed-memory execution regression for the allocating generic struct instance.
    This does not assert preservation of arbitrary caller memory. -/
theorem correctness (x : CIL.W64) :
    (CIL.Safety.invoke Extracted.program 16 0 [.scalar (.i64 x)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i64 x)] := by
  rfl

#print axioms correctness
end ExampleProof
