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
  apply WP.enter found
    (by simp [checkedValue, formValue, checkedAt, leftForm, rightForm, sumForm,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]) (by rfl)
  apply WP.step found Extracted.method0_instruction0 (by cil_checked_step [leftForm])
  apply WP.step found Extracted.method0_instruction1 (by cil_checked_step [rightForm])
  apply WP.step found Extracted.method0_instruction2 (by cil_checked_step [sumForm])
  apply WP.call found Extracted.method0_instruction3
    (by cil_checked_step [leftForm, rightForm, sumForm, DerivedInterface.addPublic,
      DerivedInterface.addArguments])
    (holds ⟨left, right, sum, region, leftValue, rightValue⟩ memory
      ⟨formed, readLeft, readRight, writable, apart, within⟩)
  rintro final values ⟨framed, output, rfl, rfl, stored, kept⟩
  apply WP.returned found Extracted.method0_instruction4 (by cil_checked_step []) (by rfl)
  exact ⟨framed, [], rfl, rfl, stored, kept⟩
#print axioms correctness

end DerivedSumCaller
