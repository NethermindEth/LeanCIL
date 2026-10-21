import CIL.Safety.ExecutionInvariants
namespace CIL.Safety

/-- A nested call or constructor invokes exactly these captured arguments. -/
def FrameAction.child (action : FrameAction) (callee : Nat) (arguments : List Value) : Prop :=
  (∃ rest, action = .call callee arguments rest action.memory) ∨
  ∃ rest frame temporary kind, action = .construct callee arguments rest frame temporary kind action.memory

/-- Memory observations at CIL boundaries, including prefixes of executions
    which later fault. Continuation requires an actual successful child run. -/
inductive RunVisits (program : CIL.Program) : Nat → Nat → Nat → List Value → Frame →
    List Value → Memory → Memory → Prop where
  | initial {fuel method pc args frame stack m} :
      RunVisits program fuel method pc args frame stack m m
  | stepped {fuel method pc args frame stack m action}
      (step : ProgramStep program method pc args frame stack m action) :
      RunVisits program (fuel + 1) method pc args frame stack m action.memory
  | next {fuel method pc args frame stack m target values nextFrame updated observed}
      (step : ProgramStep program method pc args frame stack m (.next target values nextFrame updated))
      (later : RunVisits program fuel method target args nextFrame values updated observed) :
      RunVisits program (fuel + 1) method pc args frame stack m observed
  | entered {fuel method pc args frame stack m action callee arguments child childFrame childMemory}
      (step : ProgramStep program method pc args frame stack m action)
      (call : action.child callee arguments) (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments action.memory = .ok (childFrame, childMemory)) :
      RunVisits program (fuel + 1) method pc args frame stack m childMemory
  | child {fuel method pc args frame stack m action callee arguments child childFrame childMemory observed}
      (step : ProgramStep program method pc args frame stack m action)
      (call : action.child callee arguments) (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments action.memory = .ok (childFrame, childMemory))
      (later : RunVisits program fuel callee 0 arguments childFrame [] childMemory observed) :
      RunVisits program (fuel + 1) method pc args frame stack m observed
  | callContinue {fuel method pc args frame stack m callee arguments rest updated child
        childFrame childMemory returned result observed}
      (step : ProgramStep program method pc args frame stack m (.call callee arguments rest updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 arguments childFrame [] childMemory = .ok (returned, result))
      (later : RunVisits program fuel method (pc + 1) args frame (result ++ rest) returned observed) :
      RunVisits program (fuel + 1) method pc args frame stack m observed
  | constructContinue {fuel method pc args frame stack m callee arguments rest nextFrame temporary kind
        updated child childFrame childMemory returned value observed}
      (step : ProgramStep program method pc args frame stack m
        (.construct callee arguments rest nextFrame temporary kind updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 arguments childFrame [] childMemory = .ok (returned, []))
      (load : loadLocal returned (.bytes kind temporary) = .ok value)
      (later : RunVisits program fuel method (pc + 1) args nextFrame (value :: rest) returned observed) :
      RunVisits program (fuel + 1) method pc args frame stack m observed
  | expired {fuel method pc args frame stack m result updated}
      (step : ProgramStep program method pc args frame stack m (.returned result updated)) :
      RunVisits program (fuel + 1) method pc args frame stack m (leaveFrame frame updated)

theorem runVisits_wellFormed {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m observed : Memory}
    (visit : RunVisits program fuel method pc args frame stack m observed)
    (hm : m.WellFormed) : observed.WellFormed := by
  induction visit with
  | initial => exact hm
  | stepped step => exact programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step
  | next step later ih => exact ih (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
  | entered step call lookup enter =>
    exact enterFrame_preserves_wellFormed _ _ _ _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter
  | child step call lookup enter later ih =>
    exact ih (enterFrame_preserves_wellFormed _ _ _ _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter)
  | callContinue step lookup enter finish later ih =>
    exact ih (run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _
      (enterFrame_preserves_wellFormed _ _ _ _ _
        (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter) finish)
  | constructContinue step lookup enter finish load later ih =>
    exact ih (run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _
      (enterFrame_preserves_wellFormed _ _ _ _ _
        (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter) finish)
  | expired step =>
    exact leaveFrame_preserves_wellFormed _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)

#print axioms runVisits_wellFormed

theorem run_success_visits (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    RunVisits program fuel method pc args frame stack m final := by
  have trace := run_success_trace program fuel method pc args frame stack m final values h
  clear h
  induction trace with
  | next step _ ih => exact .next step ih
  | returned step _ => exact .expired step
  | call step lookup enter finish _ _ _ ih => exact .callContinue step lookup enter finish ih
  | construct step lookup enter finish _ load _ _ ih =>
    exact .constructContinue step lookup enter finish load ih

#print axioms run_success_visits
end CIL.Safety
