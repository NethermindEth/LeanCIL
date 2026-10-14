import Extracted
import Examples.Support

namespace ExampleProof

theorem correctness (x : CIL.W32) :
    (CIL.Safety.invoke Extracted.program 16 0 [.scalar (.i32 x)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i32 x)] := by
  rfl

#print axioms correctness
end ExampleProof
