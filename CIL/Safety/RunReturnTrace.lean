import CIL.Safety.RunningPrefixes

namespace CIL.Safety

/-- Every normal interpreter result comes from an actual fetched return reached
    through the running-prefix relation, followed by teardown and result checks. -/

theorem run_success_return_trace (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory) (values : List Value)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    ∃ lastPc lastFrame lastStack before returned raw,
      RunningVisits program fuel method pc args frame stack m args lastFrame lastStack before ∧
      ProgramStep program method lastPc args lastFrame lastStack before (.returned raw returned) ∧
      final = leaveFrame lastFrame returned ∧ raw.mapM (checkedValue final) = .ok values := by
  have trace := run_success_trace program fuel method pc args frame stack m final values h
  clear h
  induction trace with
  | returned step checked => exact ⟨_, _, _, _, _, _, .initial, step, rfl, checked⟩
  | next step _ ih =>
    obtain ⟨lp, lf, ls, before, returned, raw, visit, fetched, ended, checked⟩ := ih
    exact ⟨lp, lf, ls, before, returned, raw, .next step visit, fetched, ended, checked⟩
  | call step lookup enter finish _ _ _ ih =>
    obtain ⟨lp, lf, ls, before, returned, raw, visit, fetched, ended, checked⟩ := ih
    exact ⟨lp, lf, ls, before, returned, raw,
      .callContinue step lookup enter finish visit, fetched, ended, checked⟩
  | construct step lookup enter finish _ load _ _ ih =>
    obtain ⟨lp, lf, ls, before, returned, raw, visit, fetched, ended, checked⟩ := ih
    exact ⟨lp, lf, ls, before, returned, raw,
      .constructContinue step lookup enter finish load visit, fetched, ended, checked⟩

theorem run_success_live_return_trace (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory) (values : List Value)
    (state : LiveState program args frame stack m)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    ∃ lastPc lastFrame lastStack before returned raw,
      RunningVisits program fuel method pc args frame stack m args lastFrame lastStack before ∧
      LiveState program args lastFrame lastStack before ∧
      ProgramStep program method lastPc args lastFrame lastStack before (.returned raw returned) ∧
      final = leaveFrame lastFrame returned ∧ raw.mapM (checkedValue final) = .ok values ∧
      ReturnedState program final values := by
  obtain ⟨lastPc, lastFrame, lastStack, before, returned, raw, visit, fetched, ended, checked⟩ :=
    run_success_return_trace _ _ _ _ _ _ _ _ _ _ h
  exact ⟨lastPc, lastFrame, lastStack, before, returned, raw, visit,
    runningVisits_live_state visit state, fetched, ended, checked,
    run_returned_state _ _ _ _ _ _ _ _ _ _ state h⟩

#print axioms run_success_return_trace
#print axioms run_success_live_return_trace

end CIL.Safety
