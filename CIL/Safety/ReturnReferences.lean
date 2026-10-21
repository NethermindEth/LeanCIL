import CIL.Safety.LiveValues

namespace CIL.Safety

theorem checkedValues_mapError_valid (m : Memory) (values result : List Value)
    (locate : ExecutionFault → α)
    (h : (values.mapM (checkedValue m)).mapError locate = .ok result) : ValuesValid m result := by
  cases hc : values.mapM (checkedValue m) <;> simp only [hc, Except.mapError] at h
  · cases h
  · cases h
    exact (checkedValues_valid _ _ _ hc).2

/-- Normal results have passed the reference check after frame expiration.
    This includes results returning through arbitrary nested call chains. -/

theorem run_result_valid (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    ValuesValid final values := by
  have trace := run_success_trace program fuel method pc args frame stack m final values h
  clear h
  induction trace with
  | returned _ checked => exact (checkedValues_valid _ _ _ checked).2
  | next _ _ ih | call _ _ _ _ _ _ _ ih | construct _ _ _ _ _ _ _ _ ih => exact ih

theorem invoke_result_valid (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory)
    (h : invoke program fuel method args m = .ok (final, values)) : ValuesValid final values := by
  obtain ⟨_, _, _, _, _, _, _, executed⟩ := invoke_success_setup h
  exact run_result_valid _ _ _ _ _ _ _ _ _ _ executed

#print axioms run_result_valid
#print axioms invoke_result_valid

end CIL.Safety
