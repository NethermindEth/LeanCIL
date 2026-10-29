import CIL.Safety.Execution

/-!
# Successful runs as traces

`run` is defined by fuel recursion with an error path at every step. `RunTrace` is an
inductive view of only its successful executions: `run_success_trace` turns a successful run
into a trace and `RunTrace.success` turns it back, so invariants over whole runs (memory
well-formedness, caller allocations, static world) are proved by induction on the trace
instead of by unfolding `run`.
-/

namespace CIL.Safety

/-- A step at an actual fetched instruction, not an arbitrary instruction body. -/
def ProgramStep (program : CIL.Program) (method pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) (action : FrameAction) : Prop :=
  ∃ body op, program[method]? = some body ∧ body.code[pc]? = some op ∧
    step body op pc args frame stack m = .ok action

/-- Successful execution exposes the interpreter's control-flow cases. Child runs
    carry both their interpreter equation and an induction hypothesis, so clients
    can reuse existing contracts without reopening the interpreter's error paths. -/
inductive RunTrace (program : CIL.Program) : Nat → Nat → Nat → List Value → Frame →
    List Value → Memory → Memory → List Value → Prop where
  | next {fuel method pc args frame stack m target values nextFrame updated final result}
      (step : ProgramStep program method pc args frame stack m
        (.next target values nextFrame updated))
      (later : RunTrace program fuel method target args nextFrame values updated final result) :
      RunTrace program (fuel + 1) method pc args frame stack m final result
  | returned {fuel method pc args frame stack m raw updated values}
      (step : ProgramStep program method pc args frame stack m (.returned raw updated))
      (checked : raw.mapM (checkedValue (leaveFrame frame updated)) = .ok values) :
      RunTrace program (fuel + 1) method pc args frame stack m (leaveFrame frame updated) values
  | call {fuel method pc args frame stack m callee arguments rest updated child
        childFrame childMemory returned result final values}
      (step : ProgramStep program method pc args frame stack m
        (.call callee arguments rest updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 arguments childFrame [] childMemory =
        .ok (returned, result))
      (childTrace : RunTrace program fuel callee 0 arguments childFrame [] childMemory
        returned result)
      (later : RunTrace program fuel method (pc + 1) args frame (result ++ rest) returned
        final values) :
      RunTrace program (fuel + 1) method pc args frame stack m final values
  /-- A tail call retires its frame and delegates the result to an arity-compatible callee. -/
  | tailCall {fuel method pc args frame stack m callee arguments updated body child checked
        childFrame childMemory final values}
      (step : ProgramStep program method pc args frame stack m
        (.tailCall callee arguments updated))
      (bodyLookup : program[method]? = some body)
      (lookup : program[callee]? = some child)
      (returns : (child.returnsValue != body.returnsValue) = false)
      (check : arguments.mapM (checkedValue (leaveFrame frame updated)) = .ok checked)
      (enter : enterFrame child checked (leaveFrame frame updated) =
        .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 checked childFrame [] childMemory =
        .ok (final, values))
      (childTrace : RunTrace program fuel callee 0 checked childFrame [] childMemory
        final values) :
      RunTrace program (fuel + 1) method pc args frame stack m final values
  | construct {fuel method pc args frame stack m callee arguments rest nextFrame temporary kind
        updated child childFrame childMemory returned value final values}
      (step : ProgramStep program method pc args frame stack m
        (.construct callee arguments rest nextFrame temporary kind updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 arguments childFrame [] childMemory = .ok (returned, []))
      (childTrace : RunTrace program fuel callee 0 arguments childFrame [] childMemory returned [])
      (load : loadLocal returned (.bytes kind temporary) = .ok value)
      (later : RunTrace program fuel method (pc + 1) args nextFrame (value :: rest) returned
        final values) :
      RunTrace program (fuel + 1) method pc args frame stack m final values

/-- Every successful run has a trace. -/
theorem run_success_trace (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    RunTrace program fuel method pc args frame stack m final values := by
  induction fuel generalizing method pc args frame stack m final values with
  | zero => cases h
  | succ fuel ih =>
    cases hb : program[method]? with
    | none => simp [run, hb] at h
    | some body =>
      cases ho : body.code[pc]? with
      | none => simp [run, hb, ho] at h
      | some op =>
        cases hs : step body op pc args frame stack m with
        | error fault =>
          simp [run, hb, ho, hs, Except.mapError, Bind.bind, Except.bind] at h
        | ok action =>
          have actual : ProgramStep program method pc args frame stack m action :=
            ⟨body, op, hb, ho, hs⟩
          cases action with
          | next target nextStack nextFrame memory =>
            simp only [run, hb, ho, hs, Except.mapError, Bind.bind, Except.bind] at h
            exact .next actual (ih method target args nextFrame nextStack memory final values h)
          | returned result memory =>
            cases hr : result.mapM (checkedValue (leaveFrame frame memory)) <;>
              simp only [run, hb, ho, hs, hr, Except.mapError, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at h
            · cases h
            · cases h
              exact .returned actual hr
          | call callee arguments rest memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases he : enterFrame child arguments memory with
              | error fault =>
                simp [run, hb, ho, hs, hc, he, Except.mapError, Bind.bind, Except.bind] at h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault =>
                  simp [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                | ok returned =>
                  obtain ⟨childFinal, result⟩ := returned
                  simp only [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind,
                    Except.bind] at h
                  exact .call actual hc he hr
                    (ih callee 0 arguments childFrame [] childMemory childFinal result hr)
                    (ih method (pc + 1) args frame (result ++ rest) childFinal final values h)
          | tailCall callee arguments memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases returns : child.returnsValue != body.returnsValue with
              | true =>
                simp [run, hb, ho, hs, hc, returns, Except.mapError, Bind.bind, Except.bind] at h
              | false =>
                cases check : arguments.mapM (checkedValue (leaveFrame frame memory)) with
                | error fault =>
                  simp [run, hb, ho, hs, hc, returns, check, Except.mapError,
                    Bind.bind, Except.bind] at h
                | ok checked =>
                  cases enter : enterFrame child checked (leaveFrame frame memory) with
                  | error fault =>
                    simp [run, hb, ho, hs, hc, returns, check, enter, Except.mapError,
                      Bind.bind, Except.bind] at h
                  | ok entered =>
                    obtain ⟨childFrame, childMemory⟩ := entered
                    simp only [run, hb, ho, hs, hc, returns, check, enter, Except.mapError,
                      Bind.bind, Except.bind, Bool.false_eq_true, ite_false] at h
                    exact .tailCall actual hb hc returns check enter h
                      (ih callee 0 checked childFrame [] childMemory final values h)
          | construct callee arguments rest parentFrame temporary kind memory =>
            cases hc : program[callee]? with
            | none => simp [run, hb, ho, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
            | some child =>
              cases he : enterFrame child arguments memory with
              | error fault =>
                simp [run, hb, ho, hs, hc, he, Except.mapError, Bind.bind, Except.bind] at h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault =>
                  simp [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind, Except.bind] at h
                | ok returned =>
                  obtain ⟨childFinal, result⟩ := returned
                  simp only [run, hb, ho, hs, hc, he, hr, Except.mapError, Bind.bind,
                    Except.bind] at h
                  cases result with
                  | cons value rest' => simp at h
                  | nil =>
                    simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false] at h
                    cases hl : loadLocal childFinal (.bytes kind temporary) <;>
                      simp only [hl] at h
                    · cases h
                    · rename_i value
                      exact .construct actual hc he hr
                        (ih callee 0 arguments childFrame [] childMemory childFinal [] hr) hl
                        (ih method (pc + 1) args parentFrame (value :: rest) childFinal final values
                          h)

/-- The trace characterizes the existing interpreter, rather than replacing its
    semantics with a weaker execution relation. -/
theorem RunTrace.success {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m final : Memory}
    {values : List Value}
    (trace : RunTrace program fuel method pc args frame stack m final values) :
    run program fuel method pc args frame stack m = .ok (final, values) := by
  induction trace with
  | next step _ ih =>
    obtain ⟨body, op, hb, ho, hs⟩ := step
    simpa only [run, hb, ho, hs, Except.mapError, Bind.bind, Except.bind] using ih
  | returned step checked =>
    obtain ⟨body, op, hb, ho, hs⟩ := step
    simp only [run, hb, ho, hs, checked, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  | call step lookup enter finish _ _ _ ih =>
    obtain ⟨body, op, hb, ho, hs⟩ := step
    simpa only [run, hb, ho, hs, lookup, enter, finish, Except.mapError, Bind.bind,
      Except.bind] using ih
  | tailCall step bodyLookup lookup returns check enter finish _ ih =>
    obtain ⟨body, op, hb, ho, hs⟩ := step
    have same := Option.some.inj (hb.symm.trans bodyLookup)
    subst same
    simpa only [run, hb, ho, hs, lookup, returns, check, enter, Except.mapError,
      Bind.bind, Except.bind, Bool.false_eq_true, ite_false] using ih
  | construct step lookup enter finish _ load _ _ ih =>
    obtain ⟨body, op, hb, ho, hs⟩ := step
    simpa only [run, hb, ho, hs, lookup, enter, finish, load, Except.mapError, Bind.bind,
      Except.bind, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false] using ih

/-- Separate invocation setup from execution once, including checked arguments. -/
theorem invoke_success_setup {program : CIL.Program} {fuel method : Nat}
    {args values : List Value} {m final : Memory}
    (h : invoke program fuel method args m = .ok (final, values)) :
    ∃ body arguments frame entered,
      program[method]? = some body ∧ args.mapM (checkedValue m) = .ok arguments ∧
      enterFrame body arguments m = .ok (frame, entered) ∧
      run program fuel method 0 arguments frame [] entered = .ok (final, values) := by
  unfold invoke at h
  cases hb : program[method]? with
  | none => simp [hb] at h
  | some body =>
    cases ha : args.mapM (checkedValue m) <;>
      simp only [hb, ha, Except.mapError, Bind.bind, Except.bind] at h
    · cases h
    · rename_i arguments
      cases he : enterFrame body arguments m <;> simp only [he] at h
      · cases h
      · exact ⟨body, arguments, _, _, rfl, rfl, he, h⟩

#print axioms run_success_trace
#print axioms RunTrace.success
#print axioms invoke_success_setup

end CIL.Safety
