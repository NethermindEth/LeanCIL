import ExtractedImports
import CIL.Safety.MethodContract

/-! A caller consumes the third profile of a single exported family entry. -/
namespace ExampleProof
open CIL.Safety

/-- The caller forwards the imported query and its complete result contract. -/
theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
    (fun linked => FamilyContract.supported.Holds linked 0) := by
  intro linked links imported input memory formed
  have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
  have holds : FamilyContract.supported.Holds linked 1 := imported
  dsimp only [FamilyContract.supported, MethodContract.Returns]
  apply WP.enter found (by rfl) (by rfl)
  apply WP.call found (by rfl) (by cil_checked_step []) (holds input memory formed)
  rintro final values ⟨framed, output, rfl, result⟩
  change values = [.scalar (.i32 1)] at result
  subst values
  apply WP.returned found (by rfl) (by cil_checked_step []) (by rfl)
  exact ⟨framed, _, rfl, rfl⟩
#print axioms correctness

end ExampleProof
