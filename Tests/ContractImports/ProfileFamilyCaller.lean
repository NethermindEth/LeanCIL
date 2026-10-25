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
  refine invoke_exists_of_run found (by rfl) (by rfl) ?_
  refine run_call_of_contract holds input found
    (by rfl : Extracted.method0.code[0]? = some (.call 1 0)) (by cil_checked_step []) rfl formed ?_
  rintro final values _ framed returns
  obtain ⟨output, rfl, result⟩ := returns
  change values = [.scalar (.i32 1)] at result
  subst values
  refine run_return_exists found
    (by rfl : Extracted.method0.code[1]? = some (.ret (some .unsigned8)))
    (by cil_checked_step []) (by rfl) ?_
  exact ⟨framed, _, rfl, rfl⟩
#print axioms correctness

end ExampleProof
