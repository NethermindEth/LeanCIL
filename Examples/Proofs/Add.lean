import Extracted
import CIL.Safety.MethodContract

open CIL
namespace ExampleProof

theorem correctness (x y : W64) :
    ∃ result : W64,
      (CIL.Safety.invoke Extracted.program 4 0
        [.scalar (.i64 x), .scalar (.i64 y)] Safety.Memory.empty).map Prod.snd =
          .ok [.scalar (.i64 result)] ∧
      result.toNat = (x.toNat + y.toNat) % 2^64 := by
  refine ⟨x + y, ?_, BitVec.toNat_add x y⟩
  rfl

#print axioms correctness

open CIL.Safety

/-- Addition returns the wrapping sum of every pair of words and leaves memory unchanged. -/
def addContract : MethodContract (W64 × W64) where
  args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
  pre _ _ := True
  footprint _ := []
  post input initial final values :=
    final = initial ∧ values = [.scalar (.i64 (input.1 + input.2))]

/-- Every caller memory meets `addContract`; `WrongAdd.lean` refutes this statement. -/
theorem holds : addContract.Holds Extracted.program 0 := by
  rintro ⟨x, y⟩ memory -
  exact MethodContract.Holds.intro memory [.scalar (.i64 (x + y))]
    ⟨4, rfl⟩ (Confined.refl _ _) ⟨rfl, rfl⟩

#print axioms holds
end ExampleProof
