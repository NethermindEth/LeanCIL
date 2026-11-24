import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.MethodContract

open CIL
namespace ExampleProof

/-- Both canonical Boolean inputs choose the requested value and preserve every caller memory. -/
theorem correctness (memory : CIL.Safety.Memory) (flag : Bool) (x y : W64) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0
      [.scalar (.i32 (if flag then 1 else 0)), .scalar (.i64 x), .scalar (.i64 y)] memory =
      .ok (memory, [.scalar (.i64 (if flag then x else y))]) := by
  cases flag <;> cil_checked_steps [CIL.truth, CIL.NarrowKind.extend]

#print axioms correctness

open CIL.Safety

/-- The flag selects the first or second word, and caller memory is unchanged. -/
def chooseContract : MethodContract (Bool × W64 × W64) where
  args input :=
    [.scalar (.i32 (if input.1 then 1 else 0)), .scalar (.i64 input.2.1), .scalar (.i64 input.2.2)]
  pre _ _ := True
  footprint _ := []
  post input initial final values :=
    final = initial ∧ values = [.scalar (.i64 (if input.1 then input.2.1 else input.2.2))]

/-- Every caller memory and both flags meet `chooseContract`. -/
theorem holds : chooseContract.Holds Extracted.program 0 := by
  rintro ⟨flag, left, right⟩ memory -
  exact MethodContract.Holds.intro memory _ (correctness memory flag left right)
    (Confined.refl _ _) ⟨rfl, rfl⟩

#print axioms holds
end ExampleProof
