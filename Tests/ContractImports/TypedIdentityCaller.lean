import ExtractedImports

namespace TypedIdentityCaller
open CIL.Safety

theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
    (fun linked => TypedImportInterface.identity.Holds linked 0) := by
  intro linked links imported input memory formed
  have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
  have holds : TypedImportInterface.identity.Holds linked 1 := imported
  dsimp only [TypedImportInterface.identity, MethodContract.Returns]
  apply WP.adequate.mpr
  refine invoke_exists_of_run found (by rfl) (by rfl) ?_
  refine run_next_exists _ found (by rfl : Extracted.method0.code[0]? = some (.arg 0))
    (by cil_checked_step []) ?_
  refine run_call_of_contract holds input found
    (by rfl : Extracted.method0.code[1]? = some (.call 1 1)) (by cil_checked_step []) rfl formed ?_
  intro final output call
  refine run_return_exists found (by rfl : Extracted.method0.code[2]? = some (.ret none))
    (by cil_checked_step []) (by rfl) ?_
  exact ⟨call.framed, output, rfl, call.post⟩

#print axioms correctness
end TypedIdentityCaller
