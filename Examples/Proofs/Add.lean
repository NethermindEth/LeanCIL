import Extracted
import Examples.Support

open CIL
namespace ExampleProof

-- The specification is stated independently of the extracted instructions.
def AdditionSpec (x y : W64) (values : List Value) : Prop :=
  ∃ result : W64, values = [.i64 result] ∧
    result.toNat = (x.toNat + y.toNat) % 2^64

theorem execution (x y : W64) (memory : Memory) :
    invoke Extracted.program 4 0 [.i64 x, .i64 y] memory =
      some (memory, [.i64 (x + y)]) := by
  rfl

theorem arithmetic_correctness (x y : W64) (memory : Memory) :
    ∃ values, invoke Extracted.program 4 0 [.i64 x, .i64 y] memory = some (memory, values) ∧
      AdditionSpec x y values := by
  refine ⟨[.i64 (x + y)], execution x y memory, x + y, rfl, ?_⟩
  exact BitVec.toNat_add x y

-- Also establish the independent mathematical property in the checked model.
theorem correctness (x y : W64) :
    ∃ result : W64,
      (CIL.Safety.invoke Extracted.program 4 0
        [.scalar (.i64 x), .scalar (.i64 y)] Examples.empty).map Prod.snd =
          .ok [.scalar (.i64 result)] ∧
      result.toNat = (x.toNat + y.toNat) % 2^64 := by
  exact ⟨x + y, rfl, BitVec.toNat_add x y⟩

#print axioms correctness
end ExampleProof
