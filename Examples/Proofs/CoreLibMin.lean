import Extracted
import CIL.Safety.MethodContract

/-! Signed 32-bit minimum in the .NET 11.0.0 Windows x64 NativeAOT pack's IL-only CoreLib. -/

namespace ExampleProof
open CIL CIL.Safety

/-- The smaller of the two signed Int32 values. -/
def minimum (left right : W32) : W32 := if left.toInt ≤ right.toInt then left else right

/-- The method returns the minimum without reading or changing caller memory. -/
def contract : MethodContract (W32 × W32) W32 where
  args input := [.scalar (.i32 input.1), .scalar (.i32 input.2)]
  results value := [.scalar (.i32 value)]
  pre _ _ := True
  footprint _ := []
  post input before after value := after = before ∧ value = minimum input.1 input.2

/-- Both successors of the signed comparison return their selected argument. -/
private theorem invokeMin (left right : W32) (memory : Safety.Memory) :
    invoke Extracted.program 8 0 (contract.args (left, right)) memory =
      .ok (memory, [.scalar (.i32 (minimum left right))]) := by
  change run Extracted.program 5 0 (if left.toInt ≤ right.toInt then 5 else 3)
    [.scalar (.i32 left), .scalar (.i32 right)] ⟨memory.nextIdentity, [], [], 0⟩ [] memory = _
  by_cases ordered : left.toInt ≤ right.toInt
  · rw [ite_eq_left ordered, minimum, ite_eq_left ordered]
    rfl
  · rw [ite_eq_right ordered, minimum, ite_eq_right ordered]
    rfl

/-- The extracted two-argument Math.Min satisfies the signed minimum contract. -/
theorem correctness : contract.Holds Extracted.program 0 := by
  rintro ⟨left, right⟩ memory _
  apply MethodContract.Holds.intro (c := contract) (input := (left, right)) memory
    (minimum left right) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
  exact ⟨8, invokeMin left right memory⟩

#print axioms correctness
end ExampleProof
