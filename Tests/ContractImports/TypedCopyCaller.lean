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
  refine invoke_exists_of_run found
    (by simp [checkedValue, formValue, checkedAt, sourceForm, destinationForm,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]) (by rfl) ?_
  refine run_next_exists _ found (by rfl : Extracted.method0.code[0]? = some (.arg 0))
    (by cil_checked_step [checkedValue, formValue, checkedAt, sourceForm, Except.mapError]) ?_
  refine run_next_exists _ found (by rfl : Extracted.method0.code[1]? = some (.arg 1))
    (by cil_checked_step [checkedValue, formValue, checkedAt, destinationForm, Except.mapError]) ?_
  refine run_call_of_contract holds (source, destination, value) found
    (by rfl : Extracted.method0.code[2]? = some (.call 1 2)) (by cil_checked_step []) rfl
    ⟨formed, readable, writable⟩ ?_
  rintro final values _ framed returns
  obtain ⟨output, rfl, copied⟩ := returns
  refine run_return_exists found (by rfl : Extracted.method0.code[3]? = some (.ret none))
    (by cil_checked_step []) (by rfl) ?_
  exact ⟨framed, (), rfl, copied⟩

#print axioms correctness
end TypedCopyCaller
