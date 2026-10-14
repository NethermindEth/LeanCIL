import Extracted
import Examples.Support

open CIL
namespace ExampleProof

theorem correctness (x : W64) :
    ∃ result : W64,
      (CIL.Safety.invoke Extracted.program 3 0
        [.scalar (.i64 x)] Examples.empty).map Prod.snd =
          .ok [.scalar (.i64 result)] ∧ x + result = 0 := by
  refine ⟨-x, rfl, ?_⟩
  bv_decide

#print axioms correctness
end ExampleProof
