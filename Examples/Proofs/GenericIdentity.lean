import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.MethodContract

namespace ExampleProof

/-- The compiled generic specialization and its caller return every input unchanged,
    preserving the entire caller memory. -/
theorem correctness (memory : CIL.Safety.Memory) (x : CIL.W64) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (memory, [.scalar (.i64 x)]) := by
  cil_checked_steps

#print axioms correctness

open CIL.Safety

/-- Every word is returned unchanged, and caller memory is unchanged. -/
def identityContract : MethodContract CIL.W64 where
  args input := [.scalar (.i64 input)]
  pre _ _ := True
  footprint _ := []
  post input initial final values := final = initial ∧ values = [.scalar (.i64 input)]

/-- Every caller memory meets `identityContract`. -/
theorem holds : identityContract.Holds Extracted.program 0 := by
  rintro value memory -
  exact MethodContract.Holds.intro memory _ (correctness memory value) (Confined.refl _ _)
    ⟨rfl, rfl⟩

#print axioms holds
end ExampleProof
