import Extracted
import CIL.Safety.MethodContract

/-! A counterexample to the addition contract for the subtracting `WrongAdd`: at `(0, 1)` it
    returns the wrapped difference, not the sum. -/

open CIL.Safety
namespace ExampleProof

/-- The addition contract `Add` meets: every pair of words returns their wrapping sum and leaves
    memory unchanged. -/
def addContract : MethodContract (CIL.W64 × CIL.W64) where
  args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
  pre _ _ := True
  footprint _ := []
  post input initial final values :=
    final = initial ∧ values = [.scalar (.i64 (input.1 + input.2))]

/-- The extracted method returns `0 - 1` for `(0, 1)`, which is not the sum `1`. -/
theorem refuted : addContract.Refuted Extracted.program 0 :=
  .of_return (input := (0, 1)) (initial := Memory.empty) trivial
    (rfl : invoke Extracted.program 16 0 [.scalar (.i64 0), .scalar (.i64 1)] Memory.empty = .ok _)
    (by rintro ⟨-, out, rfl, -, wrong⟩; revert wrong; decide)

#print axioms refuted
end ExampleProof
