import ExtractedImports

/-! The consumer proof of `Sum(in left, in right, out sum) => Library.AddTo(...)`, from the
    published `addPublic` contract alone. The region footprint and the frame fact for `left`
    reach this caller only through the public contract; the library's exact 8-byte footprint
    and its proof stay unpublished. -/

namespace DerivedSumCaller
open CIL.Safety

/-- Every outcome of the caller follows from the imported public contract. -/
theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
    (fun linked => DerivedInterface.addPublic.Holds linked 0) := by
  rintro linked links imported ⟨left, right, sum, region, leftValue, rightValue⟩ memory
    ⟨formed, readLeft, readRight, writable, apart, within⟩
  have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
  have holds : DerivedInterface.addPublic.Holds linked 1 := imported
  have leftForm := access_reference_valid _ _ _ _ _ (read_access readLeft)
  have rightForm := access_reference_valid _ _ _ _ _ (read_access readRight)
  have sumForm := access_reference_valid _ _ _ _ _ writable
  dsimp only [DerivedInterface.addPublic, DerivedInterface.addArguments, MethodContract.Returns]
  refine invoke_exists_of_run found
    (by simp [checkedValue, formValue, checkedAt, leftForm, rightForm, sumForm,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]) (by rfl) ?_
  refine run_next_exists _ found Extracted.method0_instruction0
    (by cil_checked_step [checkedValue, formValue, checkedAt, leftForm, Except.mapError]) ?_
  refine run_next_exists _ found Extracted.method0_instruction1
    (by cil_checked_step [checkedValue, formValue, checkedAt, rightForm, Except.mapError]) ?_
  refine run_next_exists _ found Extracted.method0_instruction2
    (by cil_checked_step [checkedValue, formValue, checkedAt, sumForm, Except.mapError]) ?_
  refine run_call_of_contract holds ⟨left, right, sum, region, leftValue, rightValue⟩ found
    Extracted.method0_instruction3
    (by cil_checked_step [formValue, leftForm, rightForm, sumForm, DerivedInterface.addPublic,
      DerivedInterface.addArguments, Except.mapError]) rfl
    ⟨formed, readLeft, readRight, writable, apart, within⟩ ?_
  rintro final values _ framed ⟨output, rfl, rfl, stored, kept⟩
  refine run_return_exists found Extracted.method0_instruction4 (by cil_checked_step [])
    (by rfl) ?_
  exact ⟨framed, [], rfl, rfl, stored, kept⟩

#print axioms correctness

end DerivedSumCaller
