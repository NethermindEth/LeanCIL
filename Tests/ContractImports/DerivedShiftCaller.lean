import ExtractedImports

/-! The consumer proof of `Shift(value) => Library.Percent(value) + 1`, from the published
    `percentBounded` contract alone: it never sees the library's exact internal contract or its
    proof. Both outcomes are covered: above 100 the named `ArgumentOutOfRangeException`
    propagates, otherwise the public bound gives a result of at most 101. -/

namespace DerivedShiftCaller
open CIL.Safety

/-- `Shift` raises what `Percent` raises and otherwise returns at most 101. -/
def shiftContract : OutcomeContract CIL.W64 CIL.W64 where
  args value := [.scalar (.i64 value)]
  results output := [.scalar (.i64 output)]
  pre _ memory := memory.WellFormed
  footprint _ := []
  post _ _ _ output := output ≤ 101
  raises value _ := DerivedInterface.percentRaises value

/-- Every outcome of the caller follows from the imported public contract. -/
theorem correctness : HoldsGiven Extracted.program Extracted.ImportsHold
    (fun linked => shiftContract.Holds linked 0) := by
  intro linked links imported value memory formed
  have found : linked[0]? = some Extracted.method0 := links.found Extracted.lookup0
  have holds : DerivedInterface.percentBounded.Holds linked 1 := imported
  dsimp only [shiftContract]
  cases raised : DerivedInterface.percentRaises value with
  | some exception =>
    refine raises_of_run found (by rfl) (by rfl) ?_
    refine run_next_raises found Extracted.method0_instruction0 (by cil_checked_step []) ?_
    exact run_call_raises_of_contract holds value found Extracted.method0_instruction1
      (by cil_checked_step []) rfl (by rfl) formed raised
  | none =>
    apply WP.exists_execution
    apply WP.enter found (by rfl) (by rfl)
    apply WP.step found Extracted.method0_instruction0 (by cil_checked_step [])
    have returned := holds.returning (initial := memory) formed raised
    apply WP.call found Extracted.method0_instruction1 (by cil_checked_step [])
      ((WP.adequate (post := fun result => Confined [] memory result.1 ∧
        DerivedInterface.percentBounded.Returns value memory result.1 result.2)).mpr
        returned)
    rintro final values ⟨framed, output, rfl, bounded⟩
    apply WP.step found Extracted.method0_instruction2 (by cil_checked_step [])
    apply WP.step found Extracted.method0_instruction3 (by cil_checked_step [])
    apply WP.step found Extracted.method0_instruction4 (by cil_checked_step [])
    apply WP.returned found Extracted.method0_instruction5 (by cil_checked_step []) (by rfl)
    refine ⟨framed, output + 1, rfl, ?_⟩
    dsimp only [DerivedInterface.percentBounded] at bounded
    bv_omega

#print axioms correctness

end DerivedShiftCaller
