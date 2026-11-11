import ExtractedImports

namespace TypedIdentityCaller
open CIL.Safety

theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
    (fun linked => TypedImportInterface.identity.Holds linked 0) := by
  intro linked links imported input memory formed
  have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
  have holds : TypedImportInterface.identity.Holds linked 1 := imported
  dsimp only [TypedImportInterface.identity, MethodContract.Returns]
  apply WP.enter found (by rfl) (by rfl)
  apply WP.step found (by rfl) (by cil_checked_step [])
  apply WP.call found (by rfl) (by cil_checked_step []) (holds input memory formed)
  rintro final values ⟨framed, output, rfl, post⟩
  apply WP.returned found (by rfl) (by cil_checked_step []) (by rfl)
  exact ⟨framed, output, rfl, post⟩

#print axioms correctness
end TypedIdentityCaller
