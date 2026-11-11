import ExtractedImports

namespace TypedCopyCaller
open CIL.Safety

theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
    (fun linked => TypedImportInterface.copy.Holds linked 0) := by
  rintro linked links imported ⟨source, destination, value⟩ memory ⟨formed, readable, writable⟩
  have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
  have holds : TypedImportInterface.copy.Holds linked 1 := imported
  have sourceForm := access_reference_valid _ _ _ _ _ (read_access readable)
  have destinationForm := access_reference_valid _ _ _ _ _ writable
  dsimp only [TypedImportInterface.copy, MethodContract.Returns]
  apply WP.enter found
    (by simp [checkedValue, formValue, checkedAt, sourceForm, destinationForm,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]) (by rfl)
  apply WP.step found (by rfl) (by cil_checked_step [sourceForm])
  apply WP.step found (by rfl) (by cil_checked_step [destinationForm])
  apply WP.call found (by rfl)
    (by cil_checked_step [sourceForm, destinationForm, TypedImportInterface.copy])
    (holds (source, destination, value) memory ⟨formed, readable, writable⟩)
  rintro final values ⟨framed, output, rfl, post⟩
  apply WP.returned found (by rfl) (by cil_checked_step []) (by rfl)
  exact ⟨framed, (), rfl, post⟩
#print axioms correctness
end TypedCopyCaller
