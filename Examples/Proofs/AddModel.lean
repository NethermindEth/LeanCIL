import Extracted

/-!
Carries a theorem proved about a pure Lean model over to the compiled `Arithmetic.Add`.
`model` and `model_comm` stand in for an existing proof development that never mentions CIL;
`refines` ties the extracted method to `model`, and `correctness` follows from those two alone.
-/

open CIL
namespace ExampleProof

/-- The reference behavior: wrapping 64-bit addition, stated without CIL. -/
def model (x y : W64) : W64 := x + y

/-- A property of the model alone; its proof never inspects the compiled method. -/
theorem model_comm (x y : W64) : model x y = model y x := BitVec.add_comm x y

/-- For every input and caller memory, the compiled method succeeds and returns `model x y`. -/
theorem refines (x y : W64) (memory : CIL.Safety.Memory) :
    (CIL.Safety.invoke Extracted.program 4 0
      [.scalar (.i64 x), .scalar (.i64 y)] memory).map Prod.snd =
        .ok [.scalar (.i64 (model x y))] := rfl

/-- The compiled method succeeds with one result for both argument orders, derived only from
`refines` and `model_comm`. Success is stated because a method that always fails would also
return equal outcomes for both orders. -/
theorem correctness (x y : W64) (memory : CIL.Safety.Memory) :
    ∃ result : W64,
      (CIL.Safety.invoke Extracted.program 4 0
        [.scalar (.i64 x), .scalar (.i64 y)] memory).map Prod.snd =
          .ok [.scalar (.i64 result)] ∧
      (CIL.Safety.invoke Extracted.program 4 0
        [.scalar (.i64 y), .scalar (.i64 x)] memory).map Prod.snd =
          .ok [.scalar (.i64 result)] :=
  ⟨model x y, refines x y memory, by rw [refines, model_comm]⟩

#print axioms model_comm
#print axioms refines
#print axioms correctness
end ExampleProof
