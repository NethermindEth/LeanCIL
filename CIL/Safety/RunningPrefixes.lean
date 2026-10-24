import CIL.Safety.StepLiveState

/-!
# Running prefixes

`RunningVisits` relates the start of a run to every frame state it later passes through
while that frame is still running or suspended in a call. `LiveState` holds at each such
visit, and a successful run ends with a `ReturnedState`: well-formed memory, valid results
and an intact static world. `CIL.Safety.RunReturnTrace` uses this to locate the final return.
-/

namespace CIL.Safety

/-- The arguments a step passes to a callee or constructor are valid in the step's memory. -/
theorem FrameAction.child_arguments_valid {program : CIL.Program} {args : List Value}
    {frame : Frame} {action : FrameAction} {callee : Nat} {arguments : List Value}
    (valid : action.StateValid program args frame) (call : action.child callee arguments) :
    ValuesValid action.memory arguments := by
  rcases call with ⟨rest, equal⟩ | ⟨rest, nextFrame, temporary, kind, equal⟩
  · cases action <;> cases equal
    exact valid.2
  · cases action <;> cases equal
    exact valid.2

/-- A callee entered from a live state starts live, with an empty stack. -/
theorem enter_child_live_state {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    {callee : Nat} {arguments : List Value} {child : CIL.Method} {childFrame : Frame}
    {childMemory : Memory}
    (step : ProgramStep program method pc args frame stack m action)
    (state : LiveState program args frame stack m) (call : action.child callee arguments)
    (enter : enterFrame child arguments action.memory = .ok (childFrame, childMemory)) :
    LiveState program arguments childFrame [] childMemory :=
  enterFrame_live_state _ _ _ _ _ _
    (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ state.memory step)
    (FrameAction.child_arguments_valid (programStep_live_state step state) call)
    (programStep_preserves_static_world step state.memory state.statics) enter

/-- After a constructor returns, the parent resumes live with the constructed value loaded
    from its temporary and pushed. -/
theorem constructor_resume_live_state (program : CIL.Program) (fuel method : Nat)
    (body : CIL.Method) (childArgs args rest : List Value) (child parent : Frame)
    (temporary : Reference) (kind : CIL.LocalKind) (value : Value) (m entered final : Memory)
    (state : LiveState program args parent rest m)
    (setup : enterFrame body childArgs m = .ok (child, entered))
    (finish : run program fuel method 0 childArgs child [] entered = .ok (final, []))
    (load : loadLocal final (.bytes kind temporary) = .ok value) :
    LiveState program args parent (value :: rest) final := by
  have preserved := child_preserves_parent_state _ _ _ _ _ _ _ _ _ _ _ _ _ state setup finish
  exact { preserved with
    stack := ValuesValid.cons (loadLocal_result_valid _ _ _ load) preserved.stack }

/-- Actual running and suspended frame boundaries. Returned frames are absent:
    their private storage has expired and their result is checked separately.
    The last four indices are the observed arguments, frame, stack and memory. -/
inductive RunningVisits (program : CIL.Program) : Nat → Nat → Nat → List Value → Frame →
    List Value → Memory → List Value → Frame → List Value → Memory → Prop where
  /-- The starting state itself. -/
  | initial {fuel method pc args frame stack m} :
      RunningVisits program fuel method pc args frame stack m args frame stack m
  /-- A visit after one ordinary step in the same method. -/
  | next {fuel method pc args frame stack m target values nextFrame updated
        observedArgs observedFrame observedStack observed}
      (step : ProgramStep program method pc args frame stack m
        (.next target values nextFrame updated))
      (later : RunningVisits program fuel method target args nextFrame values updated
        observedArgs observedFrame observedStack observed) :
      RunningVisits program (fuel + 1) method pc args frame stack m
        observedArgs observedFrame observedStack observed
  /-- The caller as it is suspended across a call, with the arguments popped. -/
  | suspendedCall {fuel method pc args frame stack m callee arguments rest updated}
      (step : ProgramStep program method pc args frame stack m
        (.call callee arguments rest updated)) :
      RunningVisits program (fuel + 1) method pc args frame stack m args frame rest updated
  /-- The caller as it is suspended across a constructor call. -/
  | suspendedConstruct {fuel method pc args frame stack m callee arguments rest nextFrame
        temporary kind updated}
      (step : ProgramStep program method pc args frame stack m
        (.construct callee arguments rest nextFrame temporary kind updated)) :
      RunningVisits program (fuel + 1) method pc args frame stack m args nextFrame rest updated
  /-- A visit inside a callee or constructor entered by the step. -/
  | child {fuel method pc args frame stack m action callee arguments child childFrame
        childMemory observedArgs observedFrame observedStack observed}
      (step : ProgramStep program method pc args frame stack m action)
      (call : action.child callee arguments) (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments action.memory = .ok (childFrame, childMemory))
      (later : RunningVisits program fuel callee 0 arguments childFrame [] childMemory
        observedArgs observedFrame observedStack observed) :
      RunningVisits program (fuel + 1) method pc args frame stack m
        observedArgs observedFrame observedStack observed
  /-- A visit in the caller after a call returned and its results were pushed. -/
  | callContinue {fuel method pc args frame stack m callee arguments rest updated child
        childFrame childMemory returned result observedArgs observedFrame observedStack observed}
      (step : ProgramStep program method pc args frame stack m
        (.call callee arguments rest updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 arguments childFrame [] childMemory =
        .ok (returned, result))
      (later : RunningVisits program fuel method (pc + 1) args frame (result ++ rest) returned
        observedArgs observedFrame observedStack observed) :
      RunningVisits program (fuel + 1) method pc args frame stack m
        observedArgs observedFrame observedStack observed
  /-- A visit in the caller after a constructor returned and its value was loaded. -/
  | constructContinue {fuel method pc args frame stack m callee arguments rest nextFrame
        temporary kind updated child childFrame childMemory returned value
        observedArgs observedFrame observedStack observed}
      (step : ProgramStep program method pc args frame stack m
        (.construct callee arguments rest nextFrame temporary kind updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 arguments childFrame [] childMemory =
        .ok (returned, []))
      (load : loadLocal returned (.bytes kind temporary) = .ok value)
      (later : RunningVisits program fuel method (pc + 1) args nextFrame (value :: rest)
        returned observedArgs observedFrame observedStack observed) :
      RunningVisits program (fuel + 1) method pc args frame stack m
        observedArgs observedFrame observedStack observed

/-- Every running or suspended state reached from a live state is live. -/
theorem runningVisits_live_state {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory}
    {observedArgs : List Value} {observedFrame : Frame} {observedStack : List Value}
    {observed : Memory}
    (visit : RunningVisits program fuel method pc args frame stack m
      observedArgs observedFrame observedStack observed)
    (state : LiveState program args frame stack m) :
    LiveState program observedArgs observedFrame observedStack observed := by
  induction visit with
  | initial => exact state
  | next step later ih => exact ih (programStep_live_state step state)
  | suspendedCall step => exact (programStep_live_state step state).1
  | suspendedConstruct step => exact (programStep_live_state step state).1
  | child step call lookup enter later ih =>
    exact ih (enter_child_live_state step state call enter)
  | callContinue step lookup enter finish later ih =>
    exact ih (child_resume_live_state _ _ _ _ _ _ _ _ _ _ _ _ _
      (programStep_live_state step state).1 enter finish)
  | constructContinue step lookup enter finish load later ih =>
    exact ih (constructor_resume_live_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (programStep_live_state step state).1 enter finish load)

/-- A running visit is also a memory observation of the run (`RunVisits`). -/
theorem runningVisits_memory_observation {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory}
    {observedArgs : List Value} {observedFrame : Frame} {observedStack : List Value}
    {observed : Memory}
    (visit : RunningVisits program fuel method pc args frame stack m
      observedArgs observedFrame observedStack observed) :
    RunVisits program fuel method pc args frame stack m observed := by
  induction visit with
  | initial => exact .initial
  | next step later ih => exact .next step ih
  | suspendedCall step => exact .stepped step
  | suspendedConstruct step => exact .stepped step
  | child step call lookup enter later ih => exact .child step call lookup enter ih
  | callContinue step lookup enter finish later ih =>
    exact .callContinue step lookup enter finish ih
  | constructContinue step lookup enter finish load later ih =>
    exact .constructContinue step lookup enter finish load ih

/-- What a caller may rely on after a successful run: well-formed memory, valid results and
    a valid static world for the program's descriptors. -/
def ReturnedState (program : CIL.Program) (memory : Memory) (values : List Value) : Prop :=
  memory.WellFormed ∧ ValuesValid memory values ∧
    StaticWorldValid (programStaticDescriptors program) memory

/-- A successful run from a live state returns a `ReturnedState`. -/
theorem run_returned_state (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value)
    (state : LiveState program args frame stack m)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    ReturnedState program final values :=
  ⟨run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ state.memory h,
    run_result_valid _ _ _ _ _ _ _ _ _ _ h,
    run_preserves_static_world _ _ _ _ _ _ _ _ _ _ state.memory state.owned state.statics h⟩

#print axioms enter_child_live_state
#print axioms constructor_resume_live_state
#print axioms runningVisits_live_state
#print axioms runningVisits_memory_observation
#print axioms run_returned_state

end CIL.Safety
