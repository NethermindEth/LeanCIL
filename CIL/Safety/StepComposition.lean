import CIL.Safety.Execution
import CIL.Safety.StepAttribute
namespace CIL.Safety

section InstructionEquations

variable (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)

/-- Expose an argument load without expanding the instruction dispatcher. -/
@[cil_step] theorem step_argument_eq (index : Nat) (stack : List Value) :
    step body (.arg index) pc args frame stack memory = do
      let some value := args[index]? | .error .invalidState
      return FrameAction.next (pc + 1) ((← checkedValue memory value) :: stack) frame memory := rfl

/-- Expose return validation without expanding the instruction dispatcher. -/
@[cil_step] theorem step_return_eq (stack : List Value) :
    step body .ret pc args frame stack memory =
      if unspecifiedOperands 1 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else if stack.length = (if body.returnsValue then 1 else 0) then
        (do return FrameAction.returned (← stack.mapM (checkedValue memory)) memory)
      else .error .invalidState := by
  simp only [step, observerCount, Bool.or_false]

/-- A narrowed return of one i32 extends it to the declared width. -/
@[cil_step] theorem step_return_narrow_eq (kind : CIL.NarrowKind) (bits : CIL.W32) :
    step body (.ret (some kind)) pc args frame [.scalar (.i32 bits)] memory =
      if body.returnsValue then .ok (.returned [.scalar (.i32 (kind.extend bits))] memory)
      else .error .invalidState := rfl

@[cil_step] theorem step_brzero_i32_eq (target : Nat) (value : CIL.W32) (rest : List Value) :
    step body (.brzero target) pc args frame (.scalar (.i32 value) :: rest) memory = do
      let some taken := CIL.truth (.i32 value) | .error .invalidState
      return FrameAction.next (if taken then pc + 1 else target) rest frame memory := rfl

@[cil_step] theorem step_brzero_i64_eq (target : Nat) (value : CIL.W64) (rest : List Value) :
    step body (.brzero target) pc args frame (.scalar (.i64 value) :: rest) memory = do
      let some taken := CIL.truth (.i64 value) | .error .invalidState
      return FrameAction.next (if taken then pc + 1 else target) rest frame memory := rfl

@[cil_step] theorem step_brnonzero_i32_eq (target : Nat) (value : CIL.W32) (rest : List Value) :
    step body (.brnonzero target) pc args frame (.scalar (.i32 value) :: rest) memory = do
      let some taken := CIL.truth (.i32 value) | .error .invalidState
      return FrameAction.next (if taken then target else pc + 1) rest frame memory := rfl

@[cil_step] theorem step_brnonzero_i64_eq (target : Nat) (value : CIL.W64) (rest : List Value) :
    step body (.brnonzero target) pc args frame (.scalar (.i64 value) :: rest) memory = do
      let some taken := CIL.truth (.i64 value) | .error .invalidState
      return FrameAction.next (if taken then target else pc + 1) rest frame memory := rfl

/-- The dispatcher arm for an op that only touches the stack and memory. -/
def instructionStep (op : CIL.Op) (pc : Nat) (frame : Frame) (stack : List Value) (memory : Memory) :
    ExecutionResult FrameAction := do
  let (memory, values) ← instruction op stack memory
  return .next (pc + 1) values frame memory

-- One equation per op, so simp selects it by constructor without a side condition.
@[cil_step] theorem step_loadAggregate_eq {size} (stack : List Value) :
    step body (.loadAggregate size) pc args frame stack memory =
      instructionStep (.loadAggregate size) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_copyObject_eq {size} (stack : List Value) :
    step body (.copyObject size) pc args frame stack memory =
      instructionStep (.copyObject size) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 2 stack <;> rfl
@[cil_step] theorem step_storeAggregate_eq {size} (stack : List Value) :
    step body (.storeAggregate size) pc args frame stack memory =
      instructionStep (.storeAggregate size) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 2 stack <;> rfl
@[cil_step] theorem step_initAggregate_eq {size} (stack : List Value) :
    step body (.initAggregate size) pc args frame stack memory =
      instructionStep (.initAggregate size) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_loadScalar_eq {width signed} (stack : List Value) :
    step body (.loadScalar width signed) pc args frame stack memory =
      instructionStep (.loadScalar width signed) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_storeScalar_eq {width} (stack : List Value) :
    step body (.storeScalar width) pc args frame stack memory =
      instructionStep (.storeScalar width) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 2 stack <;> rfl
@[cil_step] theorem step_fieldAt_eq {offset width signed} (stack : List Value) :
    step body (.fieldAt offset width signed) pc args frame stack memory =
      instructionStep (.fieldAt offset width signed) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_fieldAddress_eq {offset} (stack : List Value) :
    step body (.fieldAddress offset) pc args frame stack memory =
      instructionStep (.fieldAddress offset) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_setFieldAt_eq {offset width} (stack : List Value) :
    step body (.setFieldAt offset width) pc args frame stack memory =
      instructionStep (.setFieldAt offset width) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 2 stack <;> rfl
@[cil_step] theorem step_aggregateFieldAt_eq {offset size} (stack : List Value) :
    step body (.aggregateFieldAt offset size) pc args frame stack memory =
      instructionStep (.aggregateFieldAt offset size) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_setAggregateFieldAt_eq {offset size} (stack : List Value) :
    step body (.setAggregateFieldAt offset size) pc args frame stack memory =
      instructionStep (.setAggregateFieldAt offset size) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 2 stack <;> rfl
@[cil_step] theorem step_lane_eq {index} (stack : List Value) :
    step body (.lane index) pc args frame stack memory =
      instructionStep (.lane index) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_laneAddress_eq {index} (stack : List Value) :
    step body (.laneAddress index) pc args frame stack memory =
      instructionStep (.laneAddress index) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_setLane_eq {index} (stack : List Value) :
    step body (.setLane index) pc args frame stack memory =
      instructionStep (.setLane index) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 2 stack <;> rfl
@[cil_step] theorem step_const32_eq {word} (stack : List Value) :
    step body (.const32 word) pc args frame stack memory =
      instructionStep (.const32 word) pc frame stack memory := rfl
@[cil_step] theorem step_const64_eq {word} (stack : List Value) :
    step body (.const64 word) pc args frame stack memory =
      instructionStep (.const64 word) pc frame stack memory := rfl
@[cil_step] theorem step_load64_eq (stack : List Value) :
    step body .load64 pc args frame stack memory =
      instructionStep .load64 pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_store64_eq (stack : List Value) :
    step body .store64 pc args frame stack memory =
      instructionStep .store64 pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 2 stack <;> rfl
@[cil_step] theorem step_dup_eq (stack : List Value) :
    step body .dup pc args frame stack memory =
      instructionStep .dup pc frame stack memory := rfl
@[cil_step] theorem step_pop_eq (stack : List Value) :
    step body .pop pc args frame stack memory =
      instructionStep .pop pc frame stack memory := rfl
@[cil_step] theorem step_skipInit_eq (stack : List Value) :
    step body .skipInit pc args frame stack memory =
      instructionStep .skipInit pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_asRef_eq (stack : List Value) :
    step body .asRef pc args frame stack memory =
      instructionStep .asRef pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_local_eq (index : Nat) (narrow : Option CIL.NarrowKind) (stack : List Value) :
    step body (.local index narrow) pc args frame stack memory = do
      let some slot := frame.locals[index]? | .error .invalidState
      return FrameAction.next (pc + 1) ((← loadLocal memory slot) :: stack) frame memory := rfl

@[cil_step] theorem step_vectorLocal_eq (index : Nat) (stack : List Value) :
    step body (.vectorLocal index) pc args frame stack memory = do
      let some slot := frame.locals[index]? | .error .invalidState
      return FrameAction.next (pc + 1) ((← loadLocal memory slot) :: stack) frame memory := rfl

@[cil_step] theorem step_localAddr_eq (index : Nat) (stack : List Value) :
    step body (.localAddr index) pc args frame stack memory = do
      let some slot := frame.locals[index]? | .error .invalidState
      return FrameAction.next (pc + 1) ((← localAddress memory slot) :: stack) frame memory := rfl

@[cil_step] theorem step_setLocal_eq (index : Nat) (narrow : Option CIL.NarrowKind) (value : Value)
    (rest : List Value) :
    step body (.setLocal index narrow) pc args frame (value :: rest) memory = do
      let some slot := frame.locals[index]? | .error .invalidState
      let (slot, memory) ← storeLocal memory slot value
      return FrameAction.next (pc + 1) rest { frame with locals := frame.locals.set index slot } memory := rfl

@[cil_step] theorem step_setVectorLocal_eq (index : Nat) (value : Value) (rest : List Value) :
    step body (.setVectorLocal index) pc args frame (value :: rest) memory = do
      let some slot := frame.locals[index]? | .error .invalidState
      let (slot, memory) ← storeLocal memory slot value
      return FrameAction.next (pc + 1) rest { frame with locals := frame.locals.set index slot } memory := rfl

@[cil_step] theorem step_memory_eq (operation : CIL.MemoryOp) (stack : List Value) :
    step body (.memory operation) pc args frame stack memory =
      if unspecifiedOperands operation.argumentCount stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let (memory, values) ← staticInstruction body pc operation stack memory
        return FrameAction.next (pc + 1) values frame memory := by
  simp only [step, observerCount, Bool.or_false]

@[cil_step] theorem step_intrinsic_eq (operation : CIL.Intrinsic) (argc : Nat) (stack : List Value) :
    step body (.intrinsic operation argc) pc args frame stack memory =
      if !operation.available body.profile then .error (.unsupported "Intrinsic unavailable in target profile")
      else if stack.length < argc then .error .invalidState else do
        let operands ← scalars (stack.take argc).reverse
        let value ← checkedIntrinsic operation operands
        return FrameAction.next (pc + 1) ((← checkedValue memory (.scalar value)) :: stack.drop argc) frame memory :=
  rfl

end InstructionEquations

/-- Compose checked argument/frame setup with execution. Keeping this boundary
    explicit avoids rechecking an expanded interpreter expression at every call. -/
theorem invoke_of_run {program : CIL.Program} {fuel method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered final : Memory} {result : List Value}
    (found : program[method]? = some body)
    (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (executed : run program fuel method 0 args frame [] entered = .ok (final, result)) :
    invoke program fuel method args memory = .ok (final, result) := by
  simp only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind]
  exact executed

theorem run_next {program : CIL.Program} {fuel method pc target : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory}
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next target values nextFrame updated)) :
    run program (fuel + 1) method pc args frame stack memory =
      run program fuel method target args nextFrame values updated := by
  simp only [run, methodFound, instructionFound, stepped, Except.mapError, Bind.bind, Except.bind]
#print axioms run_next

/-- Return through frame expiration and the checked result validation. -/
theorem run_return {program : CIL.Program} {fuel method pc : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame : Frame} {memory updated : Memory}
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.returned values updated))
    (checked : values.mapM (checkedValue (leaveFrame frame updated)) = .ok values) :
    run program (fuel + 1) method pc args frame stack memory =
      .ok (leaveFrame frame updated, values) := by
  simp only [run, methodFound, instructionFound, stepped, checked,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms run_return

/-- Compose one checked fetched step with a terminating continuation without
    fixing the continuation's fuel in the caller proof. -/
theorem run_next_exists {program : CIL.Program} {method pc target : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory}
    (post : Memory → List Value → Prop)
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next target values nextFrame updated))
    (continuation : ∃ fuel result returned,
      run program fuel method target args nextFrame values updated = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧
      post result returned := by
  obtain ⟨fuel, result, returned, finished, satisfied⟩ := continuation
  exact ⟨fuel + 1, result, returned,
    (run_next methodFound instructionFound stepped).trans finished, satisfied⟩

#print axioms run_next_exists
end CIL.Safety
