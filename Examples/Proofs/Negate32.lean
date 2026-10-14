import Extracted
import Examples.Support

open CIL
namespace ExampleProof

-- Modular additive inverse, including the signed minimum value.
theorem correctness (x : W32) :
    ∃ result : W32,
      (CIL.Safety.invoke Extracted.program 3 0
        [.scalar (.i32 x)] Examples.empty).map Prod.snd =
          .ok [.scalar (.i32 result)] ∧ x + result = 0 := by
  refine ⟨-x, rfl, ?_⟩
  bv_decide

#print axioms correctness
end ExampleProof
