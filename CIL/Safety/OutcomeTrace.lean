import CIL.Safety.HandlerSteps

/-!
# Executions through exception handlers

`OutcomeTrace` views every execution of `runFaulting` over a program, ending in a result or in
the state a fault leaves, with one case for each way the interpreter continues or stops. A fault
caught by a handler resumes with the memory the fault left, so a property proved by induction on
the trace holds for runs through catch and finally handlers. `runFaulting_trace` gives the trace
of every run, without a premise on the program's exception clauses.
-/

namespace CIL.Safety

/-- A handler resumes with the memory `recover` is given. -/
theorem recover_ok_memory {method pc target : Nat} {body : CIL.Method} {frame resumed : Frame}
    {memory after : Memory} {state : FaultState} {values : List Value}
    (recovered : recover method body pc frame memory state = .ok (target, values, resumed, after)) :
    after = memory := by
  unfold recover at recovered
  split at recovered
  · cases recovered
  · split at recovered
    all_goals first
      | (cases recovered; done)
      | (split at recovered <;> first | (cases recovered; done) | (cases recovered; rfl))
#print axioms recover_ok_memory

/-- A handler resumes in the activation's own frame: only its pending resumptions change. -/
theorem recover_ok_frame {method pc target : Nat} {body : CIL.Method} {frame resumed : Frame}
    {memory after : Memory} {state : FaultState} {values : List Value}
    (recovered : recover method body pc frame memory state = .ok (target, values, resumed, after)) :
    resumed.activation = frame.activation ∧ resumed.locals = frame.locals ∧
      resumed.owned = frame.owned ∧ resumed.stackBytes = frame.stackBytes := by
  unfold recover at recovered
  split at recovered
  · cases recovered
  · split at recovered
    all_goals first
      | (cases recovered; done)
      | (split at recovered <;> first
          | (cases recovered; done)
          | (cases recovered; exact ⟨rfl, rfl, rfl, rfl⟩))
#print axioms recover_ok_frame

/-- A stopped state `recover` leaves is the state it was given, or a fault at `pc` in `memory`
    whose unwound storage expires `frame`. -/
theorem recover_error_state {method pc : Nat} {body : CIL.Method} {frame : Frame}
    {memory : Memory} {state stopped : FaultState}
    (recovered : recover method body pc frame memory state = .error stopped) :
    stopped = state ∨
      (stopped.memory = memory ∧ stopped.unwoundMemory = leaveFrame frame memory) := by
  unfold recover at recovered
  split at recovered
  · cases recovered
    exact .inl rfl
  · split at recovered
    all_goals first
      | (cases recovered; exact .inl rfl)
      | (cases recovered; exact .inr ⟨rfl, rfl⟩)
      | (split at recovered <;> first
          | (cases recovered; done)
          | (cases recovered; exact .inl rfl)
          | (cases recovered; exact .inr ⟨rfl, rfl⟩))
#print axioms recover_error_state

/-- `property` holds of the memory a run ends in: the result memory, or both memories of the
    state a fault leaves. -/
def OutcomeHolds (property : Memory → Prop) : Except FaultState (Memory × List Value) → Prop
  | .ok (final, _) => property final
  | .error state => property state.memory ∧ property state.unwoundMemory

/-- A property of every memory a run ends in gives each weaker property. -/
theorem OutcomeHolds.mono {property weaker : Memory → Prop}
    (implies : ∀ memory, property memory → weaker memory)
    {outcome : Except FaultState (Memory × List Value)} (holds : OutcomeHolds property outcome) :
    OutcomeHolds weaker outcome := by
  cases outcome with
  | ok result => exact implies _ holds
  | error state => exact ⟨implies _ holds.1, implies _ holds.2⟩

/-- Every execution of `program` from a state, by the arm of `runFaulting` it takes: a
    successful result or the stopped state of a fault, through caught faults and calls. -/
inductive OutcomeTrace (program : CIL.Program) :
    Nat → Nat → Nat → List Value → Frame → List Value → Memory →
    Except FaultState (Memory × List Value) → Prop where
  | exhausted {method pc args frame stack memory} :
      OutcomeTrace program 0 method pc args frame stack memory
        (.error ⟨⟨method, pc, .fuelExhausted⟩, memory, leaveFrame frame memory, none⟩)
  | missing {fuel method pc args frame stack memory}
      (absent : ∀ body, program[method]? = some body → body.code[pc]? = none) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, .invalidState⟩, memory, leaveFrame frame memory, none⟩)
  | faulted {fuel method pc args frame stack memory body op fault state}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (failed : step body op pc args frame stack memory = .error fault)
      (recovered : recover method body pc frame memory
        ⟨⟨method, pc, fault⟩, memory, leaveFrame frame memory, thrownReference memory op stack⟩ =
          .error state) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory (.error state)
  | caught {fuel method pc args frame stack memory body op fault target values resumed outcome}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (failed : step body op pc args frame stack memory = .error fault)
      (recovered : recover method body pc frame memory
        ⟨⟨method, pc, fault⟩, memory, leaveFrame frame memory, thrownReference memory op stack⟩ =
          .ok (target, values, resumed, memory))
      (later : OutcomeTrace program fuel method target args resumed values memory outcome) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory outcome
  | next {fuel method pc args frame stack memory body op target values nextFrame updated outcome}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.next target values nextFrame updated))
      (later : OutcomeTrace program fuel method target args nextFrame values updated outcome) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory outcome
  | raised {fuel method pc args frame stack memory body op location object raisedFrame updated
        state}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.raise location object raisedFrame updated))
      (recovered : recover method body pc raisedFrame updated
        ⟨location, updated, leaveFrame raisedFrame updated, object⟩ = .error state) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory (.error state)
  | raiseCaught {fuel method pc args frame stack memory body op location object raisedFrame
        updated target values resumed outcome}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.raise location object raisedFrame updated))
      (recovered : recover method body pc raisedFrame updated
        ⟨location, updated, leaveFrame raisedFrame updated, object⟩ =
          .ok (target, values, resumed, updated))
      (later : OutcomeTrace program fuel method target args resumed values updated outcome) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory outcome
  | callMissing {fuel method pc args frame stack memory body op callee arguments rest updated}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.call callee arguments rest updated))
      (absent : program[callee]? = none) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, .invalidState⟩, updated, leaveFrame frame updated, none⟩)
  | callUnentered {fuel method pc args frame stack memory body op callee arguments rest updated
        child fault}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.call callee arguments rest updated))
      (lookup : program[callee]? = some child)
      (refused : enterFrame child arguments updated = .error fault) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, fault⟩, updated, leaveFrame frame updated, none⟩)
  | called {fuel method pc args frame stack memory body op callee arguments rest updated child
        childFrame childMemory returned result outcome}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.call callee arguments rest updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (childTrace : OutcomeTrace program fuel callee 0 arguments childFrame [] childMemory
        (.ok (returned, result)))
      (later : OutcomeTrace program fuel method (pc + 1) args frame (result ++ rest) returned
        outcome) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory outcome
  | callFaulted {fuel method pc args frame stack memory body op callee arguments rest updated
        child childFrame childMemory childState state}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.call callee arguments rest updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (childTrace : OutcomeTrace program fuel callee 0 arguments childFrame [] childMemory
        (.error childState))
      (recovered : recover method body pc frame childState.unwoundMemory
        (childState.unwind frame) = .error state) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory (.error state)
  | callCaught {fuel method pc args frame stack memory body op callee arguments rest updated
        child childFrame childMemory childState target values resumed outcome}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.call callee arguments rest updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (childTrace : OutcomeTrace program fuel callee 0 arguments childFrame [] childMemory
        (.error childState))
      (recovered : recover method body pc frame childState.unwoundMemory
        (childState.unwind frame) = .ok (target, values, resumed, childState.unwoundMemory))
      (later : OutcomeTrace program fuel method target args resumed values
        childState.unwoundMemory outcome) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory outcome
  | tailMissing {fuel method pc args frame stack memory body op callee arguments updated}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory = .ok (.tailCall callee arguments updated))
      (absent : program[callee]? = none) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, .invalidState⟩, updated, leaveFrame frame updated, none⟩)
  | tailMismatched {fuel method pc args frame stack memory body op callee arguments updated child}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory = .ok (.tailCall callee arguments updated))
      (lookup : program[callee]? = some child)
      (returns : (child.returnsValue != body.returnsValue) = true) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, .invalidState⟩, updated, leaveFrame frame updated, none⟩)
  | tailUnchecked {fuel method pc args frame stack memory body op callee arguments updated child
        fault}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory = .ok (.tailCall callee arguments updated))
      (lookup : program[callee]? = some child)
      (returns : (child.returnsValue != body.returnsValue) = false)
      (refused : arguments.mapM (checkedValue (leaveFrame frame updated)) = .error fault) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, fault⟩, leaveFrame frame updated, leaveFrame frame updated, none⟩)
  | tailUnentered {fuel method pc args frame stack memory body op callee arguments updated child
        checked fault}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory = .ok (.tailCall callee arguments updated))
      (lookup : program[callee]? = some child)
      (returns : (child.returnsValue != body.returnsValue) = false)
      (check : arguments.mapM (checkedValue (leaveFrame frame updated)) = .ok checked)
      (refused : enterFrame child checked (leaveFrame frame updated) = .error fault) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, fault⟩, leaveFrame frame updated, leaveFrame frame updated, none⟩)
  | tailed {fuel method pc args frame stack memory body op callee arguments updated child checked
        childFrame childMemory outcome}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory = .ok (.tailCall callee arguments updated))
      (lookup : program[callee]? = some child)
      (returns : (child.returnsValue != body.returnsValue) = false)
      (check : arguments.mapM (checkedValue (leaveFrame frame updated)) = .ok checked)
      (enter : enterFrame child checked (leaveFrame frame updated) = .ok (childFrame, childMemory))
      (childTrace : OutcomeTrace program fuel callee 0 checked childFrame [] childMemory outcome) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory outcome
  | constructMissing {fuel method pc args frame stack memory body op callee arguments rest
        nextFrame temporary kind updated}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.construct callee arguments rest nextFrame temporary kind updated))
      (absent : program[callee]? = none) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, .invalidState⟩, updated, leaveFrame nextFrame updated, none⟩)
  | constructUnentered {fuel method pc args frame stack memory body op callee arguments rest
        nextFrame temporary kind updated child fault}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.construct callee arguments rest nextFrame temporary kind updated))
      (lookup : program[callee]? = some child)
      (refused : enterFrame child arguments updated = .error fault) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, fault⟩, updated, leaveFrame nextFrame updated, none⟩)
  | constructFaulted {fuel method pc args frame stack memory body op callee arguments rest
        nextFrame temporary kind updated child childFrame childMemory childState state}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.construct callee arguments rest nextFrame temporary kind updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (childTrace : OutcomeTrace program fuel callee 0 arguments childFrame [] childMemory
        (.error childState))
      (recovered : recover method body pc nextFrame childState.unwoundMemory
        (childState.unwind nextFrame) = .error state) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory (.error state)
  | constructCaught {fuel method pc args frame stack memory body op callee arguments rest
        nextFrame temporary kind updated child childFrame childMemory childState target values
        resumed outcome}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.construct callee arguments rest nextFrame temporary kind updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (childTrace : OutcomeTrace program fuel callee 0 arguments childFrame [] childMemory
        (.error childState))
      (recovered : recover method body pc nextFrame childState.unwoundMemory
        (childState.unwind nextFrame) = .ok (target, values, resumed, childState.unwoundMemory))
      (later : OutcomeTrace program fuel method target args resumed values
        childState.unwoundMemory outcome) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory outcome
  | constructValued {fuel method pc args frame stack memory body op callee arguments rest
        nextFrame temporary kind updated child childFrame childMemory returned result}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.construct callee arguments rest nextFrame temporary kind updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (childTrace : OutcomeTrace program fuel callee 0 arguments childFrame [] childMemory
        (.ok (returned, result)))
      (nonempty : (!result.isEmpty) = true) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, .invalidState⟩, returned, leaveFrame nextFrame returned, none⟩)
  | constructUnloaded {fuel method pc args frame stack memory body op callee arguments rest
        nextFrame temporary kind updated child childFrame childMemory returned fault}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.construct callee arguments rest nextFrame temporary kind updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (childTrace : OutcomeTrace program fuel callee 0 arguments childFrame [] childMemory
        (.ok (returned, [])))
      (refused : loadLocal returned (.bytes kind temporary) = .error fault) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, fault⟩, returned, leaveFrame nextFrame returned, none⟩)
  | constructed {fuel method pc args frame stack memory body op callee arguments rest nextFrame
        temporary kind updated child childFrame childMemory returned value outcome}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory =
        .ok (.construct callee arguments rest nextFrame temporary kind updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (childTrace : OutcomeTrace program fuel callee 0 arguments childFrame [] childMemory
        (.ok (returned, [])))
      (load : loadLocal returned (.bytes kind temporary) = .ok value)
      (later : OutcomeTrace program fuel method (pc + 1) args nextFrame (value :: rest) returned
        outcome) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory outcome
  | returnUnchecked {fuel method pc args frame stack memory body op raw updated fault}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory = .ok (.returned raw updated))
      (refused : raw.mapM (checkedValue (leaveFrame frame updated)) = .error fault) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.error ⟨⟨method, pc, fault⟩, leaveFrame frame updated, leaveFrame frame updated, none⟩)
  | returned {fuel method pc args frame stack memory body op raw updated values}
      (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
      (stepped : step body op pc args frame stack memory = .ok (.returned raw updated))
      (checked : raw.mapM (checkedValue (leaveFrame frame updated)) = .ok values) :
      OutcomeTrace program (fuel + 1) method pc args frame stack memory
        (.ok (leaveFrame frame updated, values))

/-- Every run of `program` has a trace that ends in the run's own outcome. -/
theorem runFaulting_trace (program : CIL.Program) (fuel method pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (memory : Memory) :
    OutcomeTrace program fuel method pc args frame stack memory
      (runFaulting (program[·]?) fuel method pc args frame stack memory) := by
  induction fuel generalizing method pc args frame stack memory with
  | zero => exact .exhausted
  | succ fuel ih =>
    cases found : program[method]? with
    | none =>
      simp only [runFaulting, found]
      exact .missing fun _ present => by rw [found] at present; cases present
    | some body =>
      cases fetched : body.code[pc]? with
      | none =>
        simp only [runFaulting, found, fetched]
        exact .missing fun _ present => by
          rw [found] at present
          cases present
          exact fetched
      | some op =>
        cases stepped : step body op pc args frame stack memory with
        | error fault =>
          simp only [runFaulting, found, fetched, stepped, Bind.bind, Except.bind]
          split
          · rename_i state recovered
            exact .faulted found fetched stepped recovered
          · rename_i resumed recovered
            obtain ⟨target, values, resumedFrame, after⟩ := resumed
            cases recover_ok_memory recovered
            exact .caught found fetched stepped recovered (ih ..)
        | ok action =>
          cases action with
          | next target values nextFrame updated =>
            simp only [runFaulting, found, fetched, stepped]
            exact .next found fetched stepped (ih ..)
          | raise location object raisedFrame updated =>
            simp only [runFaulting, found, fetched, stepped, Bind.bind, Except.bind]
            split
            · rename_i state recovered
              exact .raised found fetched stepped recovered
            · rename_i resumed recovered
              obtain ⟨target, values, resumedFrame, after⟩ := resumed
              cases recover_ok_memory recovered
              exact .raiseCaught found fetched stepped recovered (ih ..)
          | call callee arguments rest updated =>
            cases lookup : program[callee]? with
            | none =>
              simp only [runFaulting, found, fetched, stepped, lookup]
              exact .callMissing found fetched stepped lookup
            | some child =>
              cases enter : enterFrame child arguments updated with
              | error fault =>
                simp only [runFaulting, found, fetched, stepped, lookup, enter, Except.mapError,
                  Bind.bind, Except.bind]
                exact .callUnentered found fetched stepped lookup enter
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                have childTrace := ih callee 0 arguments childFrame [] childMemory
                cases childRun : runFaulting (program[·]?) fuel callee 0 arguments childFrame []
                    childMemory with
                | ok result =>
                  obtain ⟨returned, values⟩ := result
                  rw [childRun] at childTrace
                  simp only [runFaulting, found, fetched, stepped, lookup, enter, childRun,
                    Except.mapError, Bind.bind, Except.bind]
                  exact .called found fetched stepped lookup enter childTrace (ih ..)
                | error childState =>
                  rw [childRun] at childTrace
                  simp only [runFaulting, found, fetched, stepped, lookup, enter, childRun,
                    Except.mapError, Bind.bind, Except.bind]
                  split
                  · rename_i state recovered
                    exact .callFaulted found fetched stepped lookup enter childTrace recovered
                  · rename_i resumed recovered
                    obtain ⟨target, values, resumedFrame, after⟩ := resumed
                    cases recover_ok_memory recovered
                    exact .callCaught found fetched stepped lookup enter childTrace recovered
                      (ih ..)
          | tailCall callee arguments updated =>
            cases lookup : program[callee]? with
            | none =>
              simp only [runFaulting, found, fetched, stepped, lookup]
              exact .tailMissing found fetched stepped lookup
            | some child =>
              cases returns : child.returnsValue != body.returnsValue with
              | true =>
                simp only [runFaulting, found, fetched, stepped, lookup, returns, ite_true]
                exact .tailMismatched found fetched stepped lookup returns
              | false =>
                cases check : arguments.mapM (checkedValue (leaveFrame frame updated)) with
                | error fault =>
                  simp only [runFaulting, found, fetched, stepped, lookup, returns, check,
                    Bool.false_eq_true, ite_false, Except.mapError, Bind.bind, Except.bind]
                  exact .tailUnchecked found fetched stepped lookup returns check
                | ok checked =>
                  cases enter : enterFrame child checked (leaveFrame frame updated) with
                  | error fault =>
                    simp only [runFaulting, found, fetched, stepped, lookup, returns, check,
                      enter, Bool.false_eq_true, ite_false, Except.mapError, Bind.bind,
                      Except.bind]
                    exact .tailUnentered found fetched stepped lookup returns check enter
                  | ok entered =>
                    obtain ⟨childFrame, childMemory⟩ := entered
                    simp only [runFaulting, found, fetched, stepped, lookup, returns, check,
                      enter, Bool.false_eq_true, ite_false, Except.mapError, Bind.bind,
                      Except.bind]
                    exact .tailed found fetched stepped lookup returns check enter (ih ..)
          | construct callee arguments rest nextFrame temporary kind updated =>
            cases lookup : program[callee]? with
            | none =>
              simp only [runFaulting, found, fetched, stepped, lookup]
              exact .constructMissing found fetched stepped lookup
            | some child =>
              cases enter : enterFrame child arguments updated with
              | error fault =>
                simp only [runFaulting, found, fetched, stepped, lookup, enter, Except.mapError,
                  Bind.bind, Except.bind]
                exact .constructUnentered found fetched stepped lookup enter
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                have childTrace := ih callee 0 arguments childFrame [] childMemory
                cases childRun : runFaulting (program[·]?) fuel callee 0 arguments childFrame []
                    childMemory with
                | error childState =>
                  rw [childRun] at childTrace
                  simp only [runFaulting, found, fetched, stepped, lookup, enter, childRun,
                    Except.mapError, Bind.bind, Except.bind]
                  split
                  · rename_i state recovered
                    exact .constructFaulted found fetched stepped lookup enter childTrace recovered
                  · rename_i resumed recovered
                    obtain ⟨target, values, resumedFrame, after⟩ := resumed
                    cases recover_ok_memory recovered
                    exact .constructCaught found fetched stepped lookup enter childTrace recovered
                      (ih ..)
                | ok result =>
                  obtain ⟨returned, values⟩ := result
                  rw [childRun] at childTrace
                  cases values with
                  | cons value more =>
                    simp only [runFaulting, found, fetched, stepped, lookup, enter, childRun,
                      Except.mapError, Bind.bind, Except.bind, List.isEmpty_cons,
                      Bool.not_false, ite_true]
                    exact .constructValued found fetched stepped lookup enter childTrace rfl
                  | nil =>
                    cases load : loadLocal returned (.bytes kind temporary) with
                    | error fault =>
                      simp only [runFaulting, found, fetched, stepped, lookup, enter, childRun,
                        load, Except.mapError, Bind.bind, Except.bind, List.isEmpty_nil,
                        Bool.not_true, Bool.false_eq_true, ite_false]
                      exact .constructUnloaded found fetched stepped lookup enter childTrace load
                    | ok value =>
                      simp only [runFaulting, found, fetched, stepped, lookup, enter, childRun,
                        load, Except.mapError, Bind.bind, Except.bind, List.isEmpty_nil,
                        Bool.not_true, Bool.false_eq_true, ite_false]
                      exact .constructed found fetched stepped lookup enter childTrace load (ih ..)
          | returned raw updated =>
            cases checked : raw.mapM (checkedValue (leaveFrame frame updated)) with
            | error fault =>
              simp only [runFaulting, found, fetched, stepped, checked, Except.mapError,
                Bind.bind, Except.bind]
              exact .returnUnchecked found fetched stepped checked
            | ok values =>
              simp only [runFaulting, found, fetched, stepped, checked, Except.mapError,
                Bind.bind, Except.bind, Pure.pure, Except.pure]
              exact .returned found fetched stepped checked
#print axioms runFaulting_trace

/-- A run ends normally only through an actual fetched `ret`, after which its frame is retired and
    the returned values pass the result check against the memory it ends in. -/
theorem OutcomeTrace.returnedBy {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {memory final : Memory}
    {values : List Value} {outcome : Except FaultState (Memory × List Value)}
    (trace : OutcomeTrace program fuel method pc args frame stack memory outcome)
    (ended : outcome = .ok (final, values)) :
    ∃ (lastMethod lastPc : Nat) (lastArgs : List Value) (lastFrame : Frame)
      (lastStack : List Value) (before : Memory) (body : CIL.Method) (op : CIL.Instruction)
      (raw : List Value) (returned : Memory),
      program[lastMethod]? = some body ∧ body.code[lastPc]? = some op ∧
      step body op lastPc lastArgs lastFrame lastStack before = .ok (.returned raw returned) ∧
      final = leaveFrame lastFrame returned ∧ raw.mapM (checkedValue final) = .ok values := by
  induction trace with
  | returned found fetched stepped checked =>
    cases ended
    exact ⟨_, _, _, _, _, _, _, _, _, _, found, fetched, stepped, rfl, checked⟩
  | caught _ _ _ _ _ ih | next _ _ _ _ ih | raiseCaught _ _ _ _ _ ih
  | called _ _ _ _ _ _ _ _ ih | constructed _ _ _ _ _ _ _ _ _ ih
  | callCaught _ _ _ _ _ _ _ _ _ ih | constructCaught _ _ _ _ _ _ _ _ _ ih
  | tailed _ _ _ _ _ _ _ _ ih => exact ih ended
  | exhausted | missing | faulted | raised | callMissing | callUnentered | tailMissing
  | tailMismatched | constructMissing | constructUnentered | tailUnchecked | tailUnentered
  | returnUnchecked | callFaulted | constructFaulted | constructValued | constructUnloaded =>
    cases ended
#print axioms OutcomeTrace.returnedBy

/-- A successful run has a trace ending in its own result. -/
theorem run_ok_trace {program : CIL.Program} {fuel method pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {memory final : Memory} {values : List Value}
    (finished : run program fuel method pc args frame stack memory = .ok (final, values)) :
    OutcomeTrace program fuel method pc args frame stack memory (.ok (final, values)) := by
  have trace := runFaulting_trace program fuel method pc args frame stack memory
  rwa [runFaulting_of_run_ok finished] at trace
#print axioms run_ok_trace

end CIL.Safety
