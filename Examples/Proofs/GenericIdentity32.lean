import Extracted

namespace ExampleProof

theorem correctness (x : CIL.W32) :
    (CIL.Safety.invoke Extracted.program 16 0 [.scalar (.i32 x)]
      CIL.Safety.Memory.empty).map Prod.snd =
        .ok [.scalar (.i32 x)] := by
  rfl

#print axioms correctness
end ExampleProof
