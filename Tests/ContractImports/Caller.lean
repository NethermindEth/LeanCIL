import ExtractedImports
import CIL.Safety.MethodContract

namespace ExampleProof
open CIL.Safety

theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
    (fun linked => ImportFixture.addOne.Holds linked 0) := by
  intro linked links imported input memory formed
  have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
  have holds : ImportFixture.addOne.Holds linked 1 := imported
  dsimp only [ImportFixture.addOne, MethodContract.Returns]
  refine invoke_exists_of_run found (by rfl) (by rfl) ?_
  refine run_next_exists found (by rfl : Extracted.method0.code[0]? = some (.arg 0))
    (by cil_checked_step) ?_
  refine run_call_of_contract holds input found
    (by rfl : Extracted.method0.code[1]? = some (.call 1 1)) (by cil_checked_step) rfl formed ?_
  rintro final values _ framed returns
  obtain ⟨output, rfl, result⟩ := returns
  refine run_return_exists found (by rfl : Extracted.method0.code[2]? = some (.ret none))
    (by cil_checked_step) (by rfl) ?_
  exact ⟨framed, output, rfl, result⟩

end ExampleProof
