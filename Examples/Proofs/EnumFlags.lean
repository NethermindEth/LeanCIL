import Extracted
import Examples.Support

namespace ExampleProof

/-- Setting the low flag preserves every other bit, including unnamed enum bits. -/
theorem correctness (x : CIL.W64) :
    (CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 x)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i64 (x ||| 1))] := by
  rfl

#print axioms correctness
end ExampleProof
