import CIL.Safety.Execution
import CIL.Safety.StepAttribute
import CIL.Safety.GuardNormalization

/-!
# Step equations and run composition

`cil_step` equations that state what `CIL.Safety.step` does for one opcode, so stepping
tactics rewrite a step without unfolding the whole dispatcher, and the `run_*` lemmas that
chain one fetched step onto the rest of a run of the checked interpreter
(`CIL/Safety/Execution.lean`). The exact right-hand sides are what consumers see after
stepping.
-/

namespace CIL.Safety

/-- Observing an unspecified operand faults before any instruction changes memory or state. -/
theorem step_unspecified {body : CIL.Method} {operation : CIL.Instruction} {pc : Nat}
    {args stack : List Value} {frame : Frame} {memory : Memory}
    (unknown : unspecifiedOperands (observerCount operation) stack = true) :
    step body operation pc args frame stack memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := by
  simp only [step, unknown, ite_true]
#print axioms step_unspecified

section InstructionEquations

variable (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)

-- Equations that hold by unfolding are closed by `id rfl`: simp applies a lemma proved by `rfl`
-- without a proof term, so the kernel would reduce `step` again at every use.

/-- Expose an argument load without expanding the instruction dispatcher; the read itself is
    `loadArgument`. Stepping uses this form only while the method's argument access is unknown,
    and the three equations below once it is known. -/
theorem step_ldarg_eq (index : Nat) (stack : List Value) :
    step body (.ldarg index) pc args frame stack memory = do
      return FrameAction.next (pc + 1) ((← loadArgument body index args frame memory) :: stack)
        frame memory :=
  id rfl

#print axioms step_ldarg_eq

attribute [cil_step] loadArgument

/-- An argument read without a home or narrowing pushes the checked incoming value. -/
theorem step_ldarg_value_eq (index : Nat) (stack : List Value)
    (access : body.argumentAccess index = .value none) :
    step body (.ldarg index) pc args frame stack memory = do
      let some value := args[index]? | .error .invalidState
      return FrameAction.next (pc + 1) ((← checkedValue memory value) :: stack) frame memory := by
  simp only [step_ldarg_eq, loadArgument, access]
  cases args[index]? <;> rfl

#print axioms step_ldarg_value_eq

/-- An argument of a narrow declared type faults on unspecified bits, and otherwise pushes its i32
    truncated and extended to that type. -/
theorem step_ldarg_narrow_eq (index : Nat) (stack : List Value) (kind : CIL.NarrowKind)
    (access : body.argumentAccess index = .value (some kind)) :
    step body (.ldarg index) pc args frame stack memory =
      if (args[index]?.map Value.hasUnspecified).getD false then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let some (.scalar (.i32 bits)) := args[index]? | .error .invalidState
        return FrameAction.next (pc + 1)
          ((← checkedValue memory (.scalar (.i32 (kind.extend bits)))) :: stack) frame memory := by
  simp only [step_ldarg_eq, loadArgument, access]
  cases args[index]? with
  | none => rfl
  | some value =>
    cases unknown : value.hasUnspecified
    · cases value
      case scalar inner => cases inner <;> rfl
      all_goals simp_all [Value.hasUnspecified] <;> rfl
    · simp [unknown]; rfl

#print axioms step_ldarg_narrow_eq

/-- A homed argument reads its frame slot, as `ldloc` of that slot does. -/
theorem step_ldarg_home_eq (index : Nat) (stack : List Value) (slot : Nat)
    (access : body.argumentAccess index = .home slot) :
    step body (.ldarg index) pc args frame stack memory = do
      let some home := frame.locals[slot]? | .error .invalidState
      return FrameAction.next (pc + 1) ((← loadLocal memory home) :: stack) frame memory := by
  simp only [step_ldarg_eq, loadArgument, access]
  cases frame.locals[slot]? <;> rfl

#print axioms step_ldarg_home_eq

/-- Expose an argument store without expanding the instruction dispatcher; the write itself is
    `storeArgument`. Stepping uses this form only while the method's argument access is unknown,
    and the two equations below once it is known. -/
theorem step_starg_eq (index : Nat) (value : Value) (rest : List Value) :
    step body (.starg index) pc args frame (value :: rest) memory = do
      let (frame, memory) ← storeArgument body index value frame memory
      return FrameAction.next (pc + 1) rest frame memory :=
  id rfl

attribute [cil_step] storeArgument

/-- A homed argument store writes its frame slot, as `stloc` of that slot does. -/
theorem step_starg_home_eq (index : Nat) (value : Value) (rest : List Value) (slot : Nat)
    (access : body.argumentAccess index = .home slot) :
    step body (.starg index) pc args frame (value :: rest) memory = do
      let some home := frame.locals[slot]? | .error .invalidState
      let (home, memory) ← storeLocal memory home value
      return FrameAction.next (pc + 1) rest { frame with locals := frame.locals.set slot home }
        memory := by
  simp only [step_starg_eq, storeArgument, access]
  cases frame.locals[slot]? with
  | none => rfl
  | some home =>
    dsimp only
    cases storeLocal memory home value <;> rfl

#print axioms step_starg_home_eq

/-- A store to an argument without a home faults as unsupported. -/
theorem step_starg_value_eq (index : Nat) (value : Value) (rest : List Value)
    (narrow : Option CIL.NarrowKind) (access : body.argumentAccess index = .value narrow) :
    step body (.starg index) pc args frame (value :: rest) memory =
      .error (.unsupported "Store to an argument without a home") := by
  simp only [step_starg_eq, storeArgument, access]
  rfl

#print axioms step_starg_value_eq

/-- Expose an argument address without expanding the instruction dispatcher; the address itself
    is `addressArgument`. Stepping uses this form only while the method's argument access is
    unknown, and the two equations below once it is known. -/
theorem step_ldarga_eq (index : Nat) (stack : List Value) :
    step body (.ldarga index) pc args frame stack memory = do
      return FrameAction.next (pc + 1) ((← addressArgument body index frame memory) :: stack)
        frame memory :=
  id rfl

attribute [cil_step] addressArgument

-- A home is read only where a call or span operation passes it; stepping evaluates each read.
attribute [cil_step] spanView callArgument viewOperandCount viewOperands

/-- A homed argument's address is its frame slot's, as `ldloca` of that slot takes it. -/
theorem step_ldarga_home_eq (index : Nat) (stack : List Value) (slot : Nat)
    (access : body.argumentAccess index = .home slot) :
    step body (.ldarga index) pc args frame stack memory = do
      let some home := frame.locals[slot]? | .error .invalidState
      return FrameAction.next (pc + 1) ((← localAddress memory slot home) :: stack) frame
        memory := by
  simp only [step_ldarga_eq, addressArgument, access]
  cases frame.locals[slot]? <;> rfl

#print axioms step_ldarga_home_eq

/-- The address of an argument without a home faults as unsupported. -/
theorem step_ldarga_value_eq (index : Nat) (stack : List Value) (narrow : Option CIL.NarrowKind)
    (access : body.argumentAccess index = .value narrow) :
    step body (.ldarga index) pc args frame stack memory =
      .error (.unsupported "Address of an argument without a home") := by
  simp only [step_ldarga_eq, addressArgument, access]
  rfl

#print axioms step_ldarga_value_eq

/-- Expose return validation without expanding the instruction dispatcher. -/
@[cil_step] theorem step_ret_eq (stack : List Value) :
    step body .ret pc args frame stack memory =
      if unspecifiedOperands 1 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else returnFrom body.returnNarrow body.returnsValue stack memory := by
  simp only [step, observerCount]
  rfl

#print axioms step_ret_eq

/-- A hole faults on every stack, before reading the frame or memory. -/
@[cil_step] theorem step_unadmitted (opcode : Nat) (stack : List Value) :
    step body (.unadmitted opcode) pc args frame stack memory =
      .error (.unsupported "Opcode not admitted") :=
  id rfl

#print axioms step_unadmitted

/-- A plain return validates the declared number of result values. -/
@[cil_step] theorem returnFrom_none_eq (returnsValue : Bool) (stack : List Value) :
    returnFrom none returnsValue stack memory =
      if stack.length = (if returnsValue then 1 else 0) then
        (do return FrameAction.returned (← stack.mapM (checkedValue memory)) memory)
      else .error .invalidState := rfl

#print axioms returnFrom_none_eq

end InstructionEquations

/-- What a call taking `count` arguments does under the link `link` of its pc: enter a `.direct`
    link's method, under `tail.` with the whole stack and retiring the frame; without a link run
    `unlinked`, the call's runtime model, unless under `tail.`; any other link faults. A regular
    definition, so the kernel checks a rewrite of its arguments by comparing them, where a `match`
    on the link would make it evaluate the table's read. -/
def callStep (link : Option CIL.Link) (count : Nat) (tail : Bool)
    (unlinked : Unit → ExecutionResult FrameAction) (frame : Frame) (stack : List Value)
    (memory : Memory) : ExecutionResult FrameAction :=
  match link with
  | some (.direct callee) =>
    if tail then
      if stack.length != count then .error .invalidState
      else do
        return FrameAction.tailCall callee
          (← stack.reverse.mapM (callArgument frame memory)) memory
    else if stack.length < count then .error .invalidState
    else do
      let arguments ← (stack.take count).reverse.mapM (callArgument frame memory)
      return FrameAction.call callee arguments (stack.drop count) memory
  | none => if tail then .error unlinkedCall else unlinked ()
  | some _ => .error unlinkedCall

section InstructionEquations

variable (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)

/-- A call enters the method its link names, after checking the arguments its method takes,
    deepest first, and a call without a link runs its method's runtime model, which checks the
    operands it observes, as `callStep` says. -/
@[cil_step] theorem step_call_eq (method : Extraction.MethodRef) (prefixes : CallPrefixes)
    (stack : List Value) :
    step body (.call method prefixes) pc args frame stack memory =
      if (body.linkAt pc).isSome && unspecifiedOperands method.argumentCount stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else callStep (body.linkAt pc) method.argumentCount prefixes.tail
        (fun _ => modelStep (Extraction.runtimeModel body.environment .call method) body pc frame
          stack memory) frame stack memory := by
  simp only [step, observerCount, guard_operands_zero, Bool.false_eq_true, ite_false, callStep]
  cases body.linkAt pc with
  | none => rfl
  | some link => cases link <;> rfl

#print axioms step_call_eq

/-- The step of a linked call is the one before a call left its operands to its model: the
    same argument check, at the same point before the arm's other faults. -/
theorem step_call_linked {method : Extraction.MethodRef} {prefixes : CallPrefixes}
    {link : CIL.Link} (linked : body.linkAt pc = some link) (stack : List Value) :
    step body (.call method prefixes) pc args frame stack memory =
      if unspecifiedOperands method.argumentCount stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else callStep (some link) method.argumentCount prefixes.tail
        (fun _ => .error unlinkedCall) frame stack memory := by
  rw [step_call_eq, linked]
  cases link <;> rfl

#print axioms step_call_linked

/-- A plain call checks its arguments, deepest first, and leaves the rest of the stack for the
    caller's continuation. -/
@[cil_step] theorem callStep_call (callee count : Nat)
    (unlinked : Unit → ExecutionResult FrameAction) (stack : List Value) :
    callStep (some (.direct callee)) count false unlinked frame stack memory =
      if stack.length < count then .error .invalidState
      else do
        let arguments ← (stack.take count).reverse.mapM (callArgument frame memory)
        return FrameAction.call callee arguments (stack.drop count) memory := rfl

#print axioms callStep_call

/-- A call under `tail.` takes the whole stack as its arguments and retires the frame. -/
@[cil_step] theorem callStep_tailCall (callee count : Nat)
    (unlinked : Unit → ExecutionResult FrameAction) (stack : List Value) :
    callStep (some (.direct callee)) count true unlinked frame stack memory =
      if stack.length != count then .error .invalidState
      else do
        return FrameAction.tailCall callee
          (← stack.reverse.mapM (callArgument frame memory)) memory :=
  rfl

#print axioms callStep_tailCall

/-- A call whose pc has a link other than a `.direct` one faults. -/
@[cil_step] theorem callStep_unlinked (link : CIL.Link) (count : Nat) (tail : Bool)
    (unlinked : Unit → ExecutionResult FrameAction) (stack : List Value)
    (undirected : ∀ callee, link ≠ .direct callee) :
    callStep (some link) count tail unlinked frame stack memory = .error unlinkedCall := by
  unfold callStep
  split
  · exact absurd (Option.some.inj ‹_›) (undirected _)
  · contradiction
  · rfl

#print axioms callStep_unlinked

/-- A call whose pc states no link runs its runtime model. -/
@[cil_step] theorem callStep_none (count : Nat)
    (unlinked : Unit → ExecutionResult FrameAction) (stack : List Value) :
    callStep none count false unlinked frame stack memory = unlinked () := rfl

#print axioms callStep_none

/-- A `tail.` call whose pc states no link faults, since a model retires no frame. -/
@[cil_step] theorem callStep_none_tail (count : Nat)
    (unlinked : Unit → ExecutionResult FrameAction) (stack : List Value) :
    callStep none count true unlinked frame stack memory = .error unlinkedCall := rfl

#print axioms callStep_none_tail

/-- A call whose pc states no link, outside `tail.`, runs the runtime model `found` gives its
    method, which checks the operands it observes. Stepping selects it once the link and model
    facts are known, so the kernel checks one application instead of rewriting `callStep`. -/
theorem step_call_model {method : Extraction.MethodRef} {prefixes : CallPrefixes}
    {model : CIL.RuntimeModel} (link : body.linkAt pc = none)
    (found : Extraction.runtimeModel body.environment .call method = some model)
    (direct : prefixes.tail = false) (stack : List Value) :
    step body (.call method prefixes) pc args frame stack memory =
      modelStep (some model) body pc frame stack memory := by
  rw [step_call_eq, link, direct, found]
  rfl

#print axioms step_call_model

/-- A call without a link whose method's model is an intrinsic steps as that intrinsic, which
    decides itself which operand bits it reads. -/
theorem step_call_intrinsic {method : Extraction.MethodRef} {prefixes : CallPrefixes}
    {operation : CIL.Intrinsic} {argc : Nat} (link : body.linkAt pc = none)
    (found : Extraction.runtimeModel body.environment .call method =
      some (.intrinsic operation argc))
    (direct : prefixes.tail = false) :
    step body (.call method prefixes) pc args frame stack memory =
      step body (.intrinsic operation argc) pc args frame stack memory := by
  rw [step_call_model (link := link) (found := found) (direct := direct)]
  rfl

#print axioms step_call_intrinsic

/-- A kept feature getter evaluates the same profile field as a feature instruction. -/
theorem step_call_feature {method : Extraction.MethodRef} {prefixes : CallPrefixes}
    {feature : CIL.Feature} (link : body.linkAt pc = none)
    (found : Extraction.runtimeModel body.environment .call method = some (.feature feature))
    (direct : prefixes.tail = false) :
    step body (.call method prefixes) pc args frame stack memory =
      step body (.feature feature) pc args frame stack memory := by
  rw [step_call_model (link := link) (found := found) (direct := direct)]
  rfl

#print axioms step_call_feature

/-- A memory operation's model runs as the `.memory` instruction of that operation: both guard
    its `argumentCount` operands and run `memoryInstruction`, so its step equations apply. -/
theorem modelStep_memory (operation : CIL.MemoryOp) (stack : List Value) :
    modelStep (some (.memory operation)) body pc frame stack memory =
      step body (.memory operation) pc args frame stack memory := by
  simp only [modelStep, observedCall, runModel, CIL.RuntimeModel.observerCount, step,
    observerCount, staticInstruction]
  rfl

#print axioms modelStep_memory

/-- A call without a link whose method's model is a memory operation steps as that operation. -/
theorem step_call_memory {method : Extraction.MethodRef} {prefixes : CallPrefixes}
    {operation : CIL.MemoryOp} (link : body.linkAt pc = none)
    (found : Extraction.runtimeModel body.environment .call method = some (.memory operation))
    (direct : prefixes.tail = false) (stack : List Value) :
    step body (.call method prefixes) pc args frame stack memory =
      step body (.memory operation) pc args frame stack memory := by
  rw [step_call_model (link := link) (found := found) (direct := direct),
    modelStep_memory (args := args)]

#print axioms step_call_memory

/-- An unlinked constructor dispatches its model after checking the explicit arguments. -/
theorem step_newobj_model {method : Extraction.MethodRef} {model : CIL.RuntimeModel}
    (link : body.linkAt pc = none)
    (found : Extraction.runtimeModel body.environment .newobj method = some model)
    (stack : List Value) :
    step body (.newobj method) pc args frame stack memory =
      if unspecifiedOperands method.parameters.length stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else modelStep (some model) body pc frame stack memory := by
  simp only [step, observerCount, newobjStep, link, found]

#print axioms step_newobj_model

/-- A memory constructor observes its explicit operands and pushes the operation's result. -/
theorem step_newobj_memory {method : Extraction.MethodRef} {operation : CIL.MemoryOp}
    (link : body.linkAt pc = none)
    (found : Extraction.runtimeModel body.environment .newobj method = some (.memory operation))
    (count : method.parameters.length = operation.argumentCount) (stack : List Value) :
    step body (.newobj method) pc args frame stack memory =
      step body (.memory operation) pc args frame stack memory := by
  rw [step_newobj_model (link := link) (found := found), modelStep_memory (args := args), count]
  by_cases observed : unspecifiedOperands operation.argumentCount stack = true <;>
    simp only [step, observerCount, observed, Bool.false_eq_true, ite_true, ite_false]

#print axioms step_newobj_memory

/-- A call without a link whose method's model is `SkipInit` checks that its reference operand
    forms, then pops it and preserves memory. -/
theorem step_call_skipInit_reference {method : Extraction.MethodRef} {prefixes : CallPrefixes}
    (link : body.linkAt pc = none)
    (found : Extraction.runtimeModel body.environment .call method = some .skipInit)
    (direct : prefixes.tail = false) (reference : ManagedReference) (rest : List Value) :
    step body (.call method prefixes) pc args frame (.reference reference :: rest) memory = do
      let _ ← formValue memory reference
      return .next (pc + 1) rest frame memory := by
  rw [step_call_model (link := link) (found := found) (direct := direct)]
  simp only [modelStep, observedCall, runModel, skipInitCall, CIL.RuntimeModel.observerCount]
  rfl

#print axioms step_call_skipInit_reference

/-- A checked SkipInit call on a formed address pops the reference without writing to it. -/
theorem step_call_skipInit_address {method : Extraction.MethodRef} {prefixes : CallPrefixes}
    (link : body.linkAt pc = none)
    (found : Extraction.runtimeModel body.environment .call method = some .skipInit)
    (direct : prefixes.tail = false) {address : Reference} {rest : List Value}
    (formed : form memory address = .ok address) :
    step body (.call method prefixes) pc args frame (.reference (.address address) :: rest) memory =
      .ok (.next (pc + 1) rest frame memory) := by
  rw [step_call_skipInit_reference (link := link) (found := found) (direct := direct)]
  simp [formValue, checkedAt, formed, Except.mapError, Bind.bind, Except.bind, pure, Except.pure]

#print axioms step_call_skipInit_address

/-- A resolved unaligned transfer executes its checked stack and memory action at the call PC. -/
theorem step_call_typedTransfer {method : Extraction.MethodRef} {prefixes : CallPrefixes}
    {kind : CIL.TransferKind} {store : Bool} (link : body.linkAt pc = none)
    (found : Extraction.runtimeModel body.environment .call method =
      some (.typedTransfer kind store)) (direct : prefixes.tail = false) (stack : List Value) :
    step body (.call method prefixes) pc args frame stack memory =
      typedTransferCall kind store pc frame stack memory := by
  rw [step_call_model (link := link) (found := found) (direct := direct)]
  by_cases observed : unspecifiedOperands (if store then 2 else 1) stack = true <;>
    simp [modelStep, observedCall, runModel, CIL.RuntimeModel.observerCount, observed,
      typedTransferCall, observedTransfer] <;> rfl

#print axioms step_call_typedTransfer

/-- A call whose pc links `callee` directly enters it, as `callStep` says; the model it would
    run without a link is never read. Stepping selects it once the link fact is known. -/
theorem step_call_direct {method : Extraction.MethodRef} {prefixes : CallPrefixes}
    {callee : Nat} (link : body.linkAt pc = some (.direct callee)) (stack : List Value) :
    step body (.call method prefixes) pc args frame stack memory =
      if unspecifiedOperands method.argumentCount stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else callStep (some (.direct callee)) method.argumentCount prefixes.tail
        (fun _ => .error unlinkedCall) frame stack memory := by
  rw [step_call_eq, link]
  rfl

#print axioms step_call_direct

/-- A call without a link whose method has no runtime model faults. -/
@[cil_step] theorem modelStep_none (stack : List Value) :
    modelStep none body pc frame stack memory = .error unlinkedCall := rfl

#print axioms modelStep_none

/-- The `System.Object` constructor consumes its receiver and changes nothing else, as `pop`
    does. -/
@[cil_step] theorem modelStep_objectConstructor (receiver : Value) (rest : List Value) :
    modelStep (some .objectConstructor) body pc frame (receiver :: rest) memory =
      .ok (.next (pc + 1) rest frame memory) := rfl

#print axioms modelStep_objectConstructor

/-- `localloc` allocates frame storage, zeroed as the body's declared localsinit flag says. -/
@[cil_step] theorem step_localloc_eq (stack : List Value) :
    step body .localloc pc args frame stack memory =
      if unspecifiedOperands 1 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else localAllocation body.declared.initLocals pc frame stack memory := by
  simp only [step, observerCount]
  rfl

#print axioms step_localloc_eq

/-- A typed `ldelem` loads by the shape the method's layouts give its element type. -/
@[cil_step] theorem step_ldelem_any_eq (element : CIL.Extraction.TypeExpr) (stack : List Value) :
    step body (.ldelem_any element) pc args frame stack memory =
      if unspecifiedOperands 2 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let (memory, values) ←
          typedElementInstruction (body.elementShape element) false stack memory
        return .next (pc + 1) values frame memory := by
  simp only [step, observerCount]
  rfl

#print axioms step_ldelem_any_eq

/-- A value element's typed access is a snapshot transfer for a struct or vector element and
    otherwise a numeric load or store of the element's width. -/
@[cil_step] theorem typedElementInstruction_value (element : CIL.ArrayElement) (store : Bool)
    (stack : List Value) :
    typedElementInstruction (.value element) store stack memory =
      if element.composite then arrayTransferInstruction element store stack memory
      else if store then arrayStore element.width stack memory
      else arrayLoad element.width element.signed stack memory := rfl

-- A stepped typed element access shows its element's width and sign as literals.
attribute [cil_step] CIL.ArrayElement.width CIL.ArrayElement.signed CIL.ArrayElement.composite
  CIL.EnumStorage.width CIL.EnumStorage.signed

/-- A typed `stelem` stores by the shape the method's layouts give its element type. -/
@[cil_step] theorem step_stelem_any_eq (element : CIL.Extraction.TypeExpr) (stack : List Value) :
    step body (.stelem_any element) pc args frame stack memory =
      if unspecifiedOperands 3 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let (memory, values) ←
          typedElementInstruction (body.elementShape element) true stack memory
        return .next (pc + 1) values frame memory := by
  simp only [step, observerCount]
  rfl

#print axioms step_stelem_any_eq

/-- `ldelema` addresses an element by the shape the method's layouts give its element type. -/
@[cil_step] theorem step_ldelema_eq (element : CIL.Extraction.TypeExpr) (readOnly : Bool)
    (stack : List Value) :
    step body (.ldelema element readOnly) pc args frame stack memory =
      if unspecifiedOperands 2 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let (memory, values) ←
          elementAddressInstruction (body.elementShape element) readOnly stack memory
        return .next (pc + 1) values frame memory := by
  simp only [step, observerCount]
  rfl

#print axioms step_ldelema_eq

/-- A value element's address is the reference `arrayAddress` gives, read-only after the
    prefix. -/
@[cil_step] theorem elementAddressInstruction_value (element : CIL.ArrayElement)
    (readOnly : Bool) (stack : List Value) :
    elementAddressInstruction (.value element) readOnly stack memory =
      arrayAddress element (!readOnly) stack memory := rfl

/-- `ldfld` reads the field as the body resolves it, behind the unspecified-bits guard.
    Stepping uses this form only while the field's shape is unknown, and the equations of
    `ObjectSteps` once it is known. -/
theorem step_ldfld_eq (field : CIL.Extraction.FieldRef) (stack : List Value) :
    step body (.ldfld field) pc args frame stack memory =
      if unspecifiedOperands 1 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let (memory, stack) ← fieldLoad body field stack memory
        return .next (pc + 1) stack frame memory := by
  simp only [step, observerCount]
  rfl

#print axioms step_ldfld_eq

/-- `stfld` writes the field as the body resolves it, behind the unspecified-bits guard.
    Stepping uses this form only while the field's shape is unknown. -/
theorem step_stfld_eq (field : CIL.Extraction.FieldRef) (stack : List Value) :
    step body (.stfld field) pc args frame stack memory =
      if unspecifiedOperands 2 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let (memory, stack) ← fieldStore body field stack memory
        return .next (pc + 1) stack frame memory := by
  simp only [step, observerCount]
  rfl

#print axioms step_stfld_eq

/-- `ldflda` forms the address the body resolves for the field, behind the guard. Stepping
    uses this form only while the field's shape is unknown. -/
theorem step_ldflda_eq (field : CIL.Extraction.FieldRef) (stack : List Value) :
    step body (.ldflda field) pc args frame stack memory =
      if unspecifiedOperands 1 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let (memory, stack) ← fieldReference body field stack memory
        return .next (pc + 1) stack frame memory := by
  simp only [step, observerCount]
  rfl

#print axioms step_ldflda_eq

attribute [cil_step] fieldLoad fieldStore fieldReference

attribute [cil_step] localAllocation

/-- An indirect call through a method pointer enters the body `indirectTarget` selects from the
    catalog its link gives; a fact for that selection, which the kernel checks, decides it without
    comparing identities here. -/
@[cil_step] theorem step_managed_call_eq (signature : CIL.ManagedSignature)
    (tail : Bool) (pointer : CIL.MethodPointer)
    (values : List Value) :
    step body (.managed (.call signature tail)) pc args frame
        (.methodPointer pointer :: values) memory =
      if unspecifiedOperands (signature.parameters.length + 1) (.methodPointer pointer :: values)
      then .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let some (.indirect catalog) := body.linkAt pc | .error unlinkedCall
        let some method := indirectTarget signature catalog pointer | .error .invalidState
        let count := signature.parameters.length
        if (if tail then values.length != count else values.length < count) then
          .error .invalidState else pure ()
        let arguments ← (values.take count).reverse.mapM (callArgument frame memory)
        if tail then return .tailCall method arguments memory
        else return .call method arguments (values.drop count) memory := by
  simp only [step, observerCount, managedStep]
  rfl

#print axioms step_managed_call_eq

/-- A narrowed return of one i32 extends it to the declared width. -/
@[cil_step] theorem returnFrom_narrow_eq (kind : CIL.NarrowKind) (returnsValue : Bool)
    (bits : CIL.W32) :
    returnFrom (some kind) returnsValue [.scalar (.i32 bits)] memory =
      if returnsValue then .ok (.returned [.scalar (.i32 (kind.extend bits))] memory)
      else .error .invalidState := rfl

#print axioms returnFrom_narrow_eq

-- Conditional branches on an i32 or i64 operand.
@[cil_step] theorem step_brfalse_i32_eq (target : Nat) (value : CIL.W32) (rest : List Value) :
    step body (.brfalse target) pc args frame (.scalar (.i32 value) :: rest) memory = do
      let some taken := CIL.truth (.i32 value) | .error .invalidState
      return FrameAction.next (if taken then pc + 1 else target) rest frame memory := id rfl

@[cil_step] theorem step_brfalse_i64_eq (target : Nat) (value : CIL.W64) (rest : List Value) :
    step body (.brfalse target) pc args frame (.scalar (.i64 value) :: rest) memory = do
      let some taken := CIL.truth (.i64 value) | .error .invalidState
      return FrameAction.next (if taken then pc + 1 else target) rest frame memory := id rfl

@[cil_step] theorem step_brtrue_i32_eq (target : Nat) (value : CIL.W32) (rest : List Value) :
    step body (.brtrue target) pc args frame (.scalar (.i32 value) :: rest) memory = do
      let some taken := CIL.truth (.i32 value) | .error .invalidState
      return FrameAction.next (if taken then target else pc + 1) rest frame memory := id rfl

@[cil_step] theorem step_brtrue_i64_eq (target : Nat) (value : CIL.W64) (rest : List Value) :
    step body (.brtrue target) pc args frame (.scalar (.i64 value) :: rest) memory = do
      let some taken := CIL.truth (.i64 value) | .error .invalidState
      return FrameAction.next (if taken then target else pc + 1) rest frame memory := id rfl

/-- The dispatcher arm for an op that only touches the stack and memory. -/
def instructionStep (op : CIL.Instruction) (pc : Nat) (frame : Frame) (stack : List Value)
    (memory : Memory) :
    ExecutionResult FrameAction := do
  let (memory, values) ← instruction op stack memory
  return .next (pc + 1) values frame memory

/-- The span shape resolves exactly the span loads that forward their operand. -/
private theorem valueShape_span_test (type : Extraction.TypeExpr) :
    Extraction.spanLocal type = (body.valueShape type matches .span) := by
  generalize resolved : body.valueShape type = shape
  unfold Method.valueShape LayoutEnvironment.valueShape valueShapeAt at resolved
  cases span : Extraction.spanLocal type <;> simp only [span, Bool.false_eq_true, ite_false,
    ite_true] at resolved
  all_goals repeat' split at resolved
  all_goals subst shape <;> rfl
#print axioms valueShape_span_test

/-- The decoded ldobj of primitive storage has the full result of its memory rule. -/
@[cil_step] theorem step_ldobj_primitive {type : Extraction.TypeExpr} {width : Nat} {signed : Bool}
    (shape : body.valueShape type = .primitive width signed) (stack : List Value) :
    step body (.ldobj type) pc args frame stack memory =
      typedTransferCall (.scalar width signed) false pc frame stack memory := by
  by_cases observed : unspecifiedOperands 1 stack = true <;>
    simp [step, observerCount, valueShape_span_test body type, shape, viewOperands, transferObject,
      typedTransferCall, observedTransfer, observed, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms step_ldobj_primitive

/-- The decoded ldobj of aggregate storage has the full result of its memory rule. -/
@[cil_step] theorem step_ldobj_aggregate {type : Extraction.TypeExpr} {size : Nat}
    (shape : body.valueShape type = .aggregate size) (stack : List Value) :
    step body (.ldobj type) pc args frame stack memory =
      typedTransferCall (.snapshot (.aggregate size)) false pc frame stack memory := by
  by_cases observed : unspecifiedOperands 1 stack = true <;>
    simp [step, observerCount, valueShape_span_test body type, shape, viewOperands, transferObject,
      typedTransferCall, observedTransfer, observed, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms step_ldobj_aggregate

/-- The decoded ldobj of vector storage has the full result of its memory rule. -/
@[cil_step] theorem step_ldobj_vector16 {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .vector 16) (stack : List Value) :
    step body (.ldobj type) pc args frame stack memory =
      step body (.memory .load128) pc args frame stack memory := by
  simp only [step, observerCount, valueShape_span_test body type, shape, transferObject,
    pureArity, staticInstruction]
  first | rfl | (cases unspecifiedOperands 1 stack <;> rfl)
#print axioms step_ldobj_vector16

/-- The decoded ldobj of vector storage has the full result of its memory rule. -/
@[cil_step] theorem step_ldobj_vector32 {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .vector 32) (stack : List Value) :
    step body (.ldobj type) pc args frame stack memory =
      step body (.memory .load256) pc args frame stack memory := by
  simp only [step, observerCount, valueShape_span_test body type, shape, transferObject,
    pureArity, staticInstruction]
  first | rfl | (cases unspecifiedOperands 1 stack <;> rfl)
#print axioms step_ldobj_vector32

/-- The decoded ldobj of vector storage has the full result of its memory rule. -/
@[cil_step] theorem step_ldobj_vector64 {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .vector 64) (stack : List Value) :
    step body (.ldobj type) pc args frame stack memory =
      step body (.memory .load512) pc args frame stack memory := by
  simp only [step, observerCount, valueShape_span_test body type, shape, transferObject,
    pureArity, staticInstruction]
  first | rfl | (cases unspecifiedOperands 1 stack <;> rfl)
#print axioms step_ldobj_vector64

/-- A decoded ldobj of span storage leaves a span view on the stack in place. -/
@[cil_step] theorem step_ldobj_span {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .span) (view : SpanView) (rest : List Value) :
    step body (.ldobj type) pc args frame (.bufferSpan view :: rest) memory =
      step body .nop pc args frame (.bufferSpan view :: rest) memory := by
  simp only [step, observerCount, valueShape_span_test body type, shape, transferObject,
    pureArity, staticInstruction]
  rfl
#print axioms step_ldobj_span

/-- A decoded ldobj of span storage leaves a span value formed from a reference in place. -/
@[cil_step] theorem step_ldobj_span_value {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .span) (reference : ManagedReference) (length : Nat)
    (rest : List Value) :
    step body (.ldobj type) pc args frame (.span reference length :: rest) memory =
      step body .nop pc args frame (.span reference length :: rest) memory := by
  simp only [step, observerCount, valueShape_span_test body type, shape, transferObject,
    pureArity, staticInstruction]
  rfl
#print axioms step_ldobj_span_value

/-- A decoded ldobj of span storage faults on a null reference, as a load through it does. -/
theorem step_ldobj_span_null {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .span) {operand : Value}
    (null : operand = .reference .null ∨ operand = .readOnlyReference .null) (rest : List Value) :
    step body (.ldobj type) pc args frame (operand :: rest) memory =
      .error (.memory .nullDereference .null 0) := by
  rcases null with rfl | rfl <;>
    simp only [step, observerCount, valueShape_span_test body type, shape, transferObject,
      pureArity, staticInstruction] <;> rfl
#print axioms step_ldobj_span_null

/-- A decoded ldobj of span storage faults on a plain address, which never names a span view. -/
theorem step_ldobj_span_address {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .span) {operand : Value} {reference : Reference}
    (address : operand = .reference (.address reference) ∨
      operand = .readOnlyReference (.address reference)) (rest : List Value) :
    step body (.ldobj type) pc args frame (operand :: rest) memory = .error .invalidState := by
  rcases address with rfl | rfl <;>
    simp only [step, observerCount, valueShape_span_test body type, shape, transferObject,
      pureArity, staticInstruction] <;> rfl
#print axioms step_ldobj_span_address

/-- A home a span operation reads stands for the view its slot holds. -/
theorem spanView_home_view {frame : Frame} {memory : Memory} {slot : Nat} {result : Value}
    (viewed : spanView frame memory (.spanHome slot) = .ok result) :
    ∃ view, result = .bufferSpan view := by
  simp only [spanView] at viewed
  split at viewed
  · simp only [loadLocal, Bind.bind, Except.bind, Pure.pure, Except.pure] at viewed
    repeat' (first | (cases viewed; exact ⟨_, rfl⟩) | contradiction | split at viewed)
  · cases viewed
#print axioms spanView_home_view

/-- A decoded ldobj of span storage reads a home as the view its slot holds when the load runs.
    A home whose slot holds no view faults. -/
@[cil_step high] theorem step_ldobj_span_home {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .span) (slot : Nat) (rest : List Value) :
    step body (.ldobj type) pc args frame (.spanHome slot :: rest) memory =
      match spanView frame memory (.spanHome slot) with
      | .ok (.bufferSpan view) => step body .nop pc args frame (.bufferSpan view :: rest) memory
      | .ok _ => .error .invalidState
      | .error fault => .error fault := by
  cases viewed : spanView frame memory (.spanHome slot) with
  | error fault =>
    simp only [step, observerCount, valueShape_span_test body type, shape, viewOperands, viewed,
      unspecifiedOperands, List.take, List.any, Bool.false_eq_true, ite_false, ite_true,
      Bind.bind, Except.bind]
  | ok result =>
    obtain ⟨view, rfl⟩ := spanView_home_view viewed
    simp only [step, observerCount, valueShape_span_test body type, shape, transferObject,
      viewOperands, viewed, unspecifiedOperands, List.take, List.any, Bool.false_eq_true,
      ite_false, ite_true, Bind.bind, Except.bind, pureArity]
    rfl
#print axioms step_ldobj_span_home

/-- A decoded ldobj of span storage forwards a span view or span value, reads a home as the view
    its slot holds, faults on a null reference as a null dereference, and raises an invalid state
    on any other stack. -/
theorem step_ldobj_span_result {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .span) (stack : List Value) :
    step body (.ldobj type) pc args frame stack memory = match stack with
      | .bufferSpan _ :: _ | .span .. :: _ => step body .nop pc args frame stack memory
      | .spanHome slot :: rest => match spanView frame memory (.spanHome slot) with
        | .ok (.bufferSpan view) => step body .nop pc args frame (.bufferSpan view :: rest) memory
        | .ok _ => .error .invalidState
        | .error fault => .error fault
      | .reference .null :: _ | .readOnlyReference .null :: _ =>
        .error (.memory .nullDereference .null 0)
      | _ => .error .invalidState := by
  cases stack with
  | nil =>
    simp only [step, observerCount, valueShape_span_test body type, shape, transferObject]
    rfl
  | cons head rest =>
    cases head
    case spanHome slot =>
      exact step_ldobj_span_home (body := body) (pc := pc) (args := args) (frame := frame)
        (memory := memory) shape slot rest
    all_goals
      simp only [step, observerCount, valueShape_span_test body type, shape, transferObject,
        pureArity]
      first | rfl | (rename_i reference; cases reference <;> rfl)
#print axioms step_ldobj_span_result

/-- The decoded stobj of primitive storage has the full result of its memory rule. -/
@[cil_step] theorem step_stobj_primitive {type : Extraction.TypeExpr} {width : Nat} {signed : Bool}
    (shape : body.valueShape type = .primitive width signed) (stack : List Value) :
    step body (.stobj type) pc args frame stack memory =
      typedTransferCall (.scalar width false) true pc frame stack memory := by
  by_cases observed : unspecifiedOperands 2 stack = true <;>
    simp [step, observerCount, shape, transferObject, typedTransferCall, observedTransfer,
      observed] <;> rfl
#print axioms step_stobj_primitive

/-- The decoded stobj of aggregate storage has the full result of its memory rule. -/
@[cil_step] theorem step_stobj_aggregate {type : Extraction.TypeExpr} {size : Nat}
    (shape : body.valueShape type = .aggregate size) (stack : List Value) :
    step body (.stobj type) pc args frame stack memory =
      typedTransferCall (.snapshot (.aggregate size)) true pc frame stack memory := by
  by_cases observed : unspecifiedOperands 2 stack = true <;>
    simp [step, observerCount, shape, transferObject, typedTransferCall, observedTransfer,
      observed] <;> rfl
#print axioms step_stobj_aggregate

/-- The decoded stobj of vector storage has the full result of its memory rule. -/
@[cil_step] theorem step_stobj_vector16 {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .vector 16) (stack : List Value) :
    step body (.stobj type) pc args frame stack memory =
      step body (.memory .store128) pc args frame stack memory := by
  simp only [step, observerCount, shape, transferObject,
    pureArity, staticInstruction]
  first | rfl | (cases unspecifiedOperands 2 stack <;> rfl)
#print axioms step_stobj_vector16

/-- The decoded stobj of vector storage has the full result of its memory rule. -/
@[cil_step] theorem step_stobj_vector32 {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .vector 32) (stack : List Value) :
    step body (.stobj type) pc args frame stack memory =
      step body (.memory .store256) pc args frame stack memory := by
  simp only [step, observerCount, shape, transferObject,
    pureArity, staticInstruction]
  first | rfl | (cases unspecifiedOperands 2 stack <;> rfl)
#print axioms step_stobj_vector32

/-- The decoded stobj of vector storage has the full result of its memory rule. -/
@[cil_step] theorem step_stobj_vector64 {type : Extraction.TypeExpr}
    (shape : body.valueShape type = .vector 64) (stack : List Value) :
    step body (.stobj type) pc args frame stack memory =
      step body (.memory .store512) pc args frame stack memory := by
  simp only [step, observerCount, shape, transferObject,
    pureArity, staticInstruction]
  first | rfl | (cases unspecifiedOperands 2 stack <;> rfl)
#print axioms step_stobj_vector64

/-- initobj checks its operands before accessing the resolved number of bytes. -/
@[cil_step] theorem step_initobj_eq {type : Extraction.TypeExpr} {size : Nat}
    (width : (body.valueShape type).size? = some size) (stack : List Value) :
    step body (.initobj type) pc args frame stack memory =
      if unspecifiedOperands 1 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let (updated, values) ← initializeBytes size stack memory
        return .next (pc + 1) values frame updated := by
  simp only [step, observerCount, width]
#print axioms step_initobj_eq

/-- cpobj checks its operands before accessing the resolved number of bytes. -/
@[cil_step] theorem step_cpobj_eq {type : Extraction.TypeExpr} {size : Nat}
    (width : (body.valueShape type).size? = some size) (stack : List Value) :
    step body (.cpobj type) pc args frame stack memory =
      if unspecifiedOperands 2 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let (updated, values) ← copyInitializedBytes size stack memory
        return .next (pc + 1) values frame updated := by
  simp only [step, observerCount, width]
#print axioms step_cpobj_eq

/-- The size of an admitted type pushes its resolved byte width as an i32. -/
@[cil_step] theorem step_sizeof_eq {type : Extraction.TypeExpr} {size : Nat}
    (width : (body.valueShape type).size? = some size) (stack : List Value) :
    step body (.sizeof type) pc args frame stack memory =
      step body (.ldc_i4 (BitVec.ofNat 32 size)) pc args frame stack memory := by
  change (body.environment.valueShape type).size? = some size at width
  simp only [step, observerCount, Extraction.CallLayouts.valueShape_eq, width, unspecifiedOperands,
    List.take_zero, List.any_nil, pureArity, instruction]
  rfl
#print axioms step_sizeof_eq

-- One equation per op, so simp selects it by constructor without a side condition.
@[cil_step] theorem step_fieldAt_eq {offset width signed} (stack : List Value) :
    step body (.fieldAt offset width signed) pc args frame stack memory =
      instructionStep (.fieldAt offset width signed) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_setFieldAt_eq {offset width} (stack : List Value) :
    step body (.setFieldAt offset width) pc args frame stack memory =
      instructionStep (.setFieldAt offset width) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 2 stack <;> rfl


/-! A struct field instruction steps as the lowered instruction of its checked shape, so the
equations of the lowered forms state what it does on every stack. -/

/-- A faulting guard faults the lowered instruction too, before it reads memory. -/
private theorem instruction_guarded {operation : CIL.Instruction} {stack : List Value}
    (unknown : unspecifiedOperands (observerCount operation) stack = true) :
    instruction operation stack memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := by
  unfold instruction
  rw [if_pos unknown]

/-- `ldfld` of a struct field of primitive or vector shape steps as `fieldAt` of its offset,
    width and sign on every stack, faults included. -/
theorem step_ldfld_value_eq (field : CIL.Extraction.FieldRef) (offset width : Nat)
    (signed : Bool) (shape : body.fieldShape field = .value offset width signed)
    (stack : List Value) :
    step body (.ldfld field) pc args frame stack memory =
      step body (.fieldAt offset width signed) pc args frame stack memory := by
  rw [step_ldfld_eq, step_fieldAt_eq]
  simp only [fieldLoad, shape, instructionStep]
  cases observed : unspecifiedOperands 1 stack
  · rfl
  · rw [instruction_guarded memory (operation := .fieldAt offset width signed) observed]
    rfl
#print axioms step_ldfld_value_eq

/-- A nested struct field is read from its checked offset with its initialization flags. -/
theorem step_ldfld_aggregate_eq (field : CIL.Extraction.FieldRef) (offset size : Nat)
    (shape : body.fieldShape field = .aggregate offset size) (stack : List Value) :
    step body (.ldfld field) pc args frame stack memory = (do
      let (memory, stack) ← loadAggregateField offset size stack memory
      return .next (pc + 1) stack frame memory) := by
  rw [step_ldfld_eq]
  simp only [fieldLoad, shape]
  unfold loadAggregateField
  split <;> rfl
#print axioms step_ldfld_aggregate_eq

/-- `stfld` of a struct field of primitive or vector shape steps as `setFieldAt` of its
    offset and width on every stack, faults included. -/
theorem step_stfld_value_eq (field : CIL.Extraction.FieldRef) (offset width : Nat)
    (signed : Bool) (shape : body.fieldShape field = .value offset width signed)
    (stack : List Value) :
    step body (.stfld field) pc args frame stack memory =
      step body (.setFieldAt offset width) pc args frame stack memory := by
  rw [step_stfld_eq, step_setFieldAt_eq]
  simp only [fieldStore, shape, instructionStep]
  cases observed : unspecifiedOperands 2 stack
  · rfl
  · rw [instruction_guarded memory (operation := .setFieldAt offset width) observed]
    rfl
#print axioms step_stfld_value_eq

/-- A nested struct store writes at the offset and width from the checked field shape. -/
theorem step_stfld_aggregate_eq (field : CIL.Extraction.FieldRef) (offset size : Nat)
    (shape : body.fieldShape field = .aggregate offset size) (stack : List Value) :
    step body (.stfld field) pc args frame stack memory = (do
      let (memory, stack) ← storeAggregateField offset size stack memory
      return .next (pc + 1) stack frame memory) := by
  rw [step_stfld_eq]
  simp only [fieldStore, shape]
  unfold storeAggregateField
  split <;> rfl
#print axioms step_stfld_aggregate_eq

/-- A struct ldflda computes its checked field offset and preserves the receiver's writability. -/
theorem step_ldflda_struct_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (addressed : (body.fieldShape field).structOffset? = some offset) (stack : List Value) :
    step body (.ldflda field) pc args frame stack memory = (do
      let (memory, stack) ← structFieldAddress offset stack memory
      return .next (pc + 1) stack frame memory) := by
  have reached : fieldReference body field stack memory = structFieldAddress offset stack memory := by
    unfold fieldReference
    split <;> simp_all [CIL.FieldShape.structOffset?]
  rw [step_ldflda_eq, reached]
  unfold structFieldAddress
  split <;> rfl
#print axioms step_ldflda_struct_eq

/-- A struct field address keeps a writable reference writable. -/
theorem step_ldflda_reference_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (addressed : (body.fieldShape field).structOffset? = some offset) (reference : Reference)
    (rest : List Value) :
    step body (.ldflda field) pc args frame (.reference (.address reference) :: rest)
        memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      return .next (pc + 1) (.reference (.address address) :: rest) frame memory := by
  rw [step_ldflda_struct_eq _ _ _ _ _ field offset addressed]
  simp only [structFieldAddress, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    Bool.false_or, Bool.false_eq_true, ite_false, bind_assoc, pure_bind]
#print axioms step_ldflda_reference_eq

/-- A struct field address through a readonly receiver stays readonly. -/
theorem step_ldflda_readOnlyReference_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (addressed : (body.fieldShape field).structOffset? = some offset) (reference : Reference)
    (rest : List Value) :
    step body (.ldflda field) pc args frame (.readOnlyReference (.address reference) :: rest)
        memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      return .next (pc + 1) (.readOnlyReference (.address address) :: rest) frame memory := by
  rw [step_ldflda_struct_eq _ _ _ _ _ field offset addressed]
  simp only [structFieldAddress, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    Bool.false_or, Bool.false_eq_true, ite_false, bind_assoc, pure_bind]
#print axioms step_ldflda_readOnlyReference_eq


@[cil_step] theorem step_ldc_i4_eq {value} (stack : List Value) :
    step body (.ldc_i4 value) pc args frame stack memory =
      instructionStep (.ldc_i4 value) pc frame stack memory := id rfl
@[cil_step] theorem step_ldc_i8_eq {value} (stack : List Value) :
    step body (.ldc_i8 value) pc args frame stack memory =
      instructionStep (.ldc_i8 value) pc frame stack memory := id rfl
@[cil_step] theorem step_ldind_eq {kind} (stack : List Value) :
    step body (.ldind kind) pc args frame stack memory =
      instructionStep (.ldind kind) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 1 stack <;> rfl
@[cil_step] theorem step_stind_eq {kind} (stack : List Value) :
    step body (.stind kind) pc args frame stack memory =
      instructionStep (.stind kind) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  cases observed : unspecifiedOperands 2 stack <;> rfl
@[cil_step] theorem step_ldlen_eq (stack : List Value) :
    step body .ldlen pc args frame stack memory =
      instructionStep .ldlen pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  by_cases observed : unspecifiedOperands 1 stack = true <;>
    simp only [observed, ↓reduceIte, Bool.false_eq_true] <;> rfl
@[cil_step] theorem step_ldelem_eq {kind} (stack : List Value) :
    step body (.ldelem kind) pc args frame stack memory =
      instructionStep (.ldelem kind) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  by_cases observed : unspecifiedOperands 2 stack = true <;>
    simp only [observed, ↓reduceIte, Bool.false_eq_true] <;> rfl
@[cil_step] theorem step_ldelem_ref_eq (stack : List Value) :
    step body .ldelem_ref pc args frame stack memory =
      instructionStep .ldelem_ref pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  by_cases observed : unspecifiedOperands 2 stack = true <;>
    simp only [observed, ↓reduceIte, Bool.false_eq_true] <;> rfl
@[cil_step] theorem step_stelem_eq {kind} (stack : List Value) :
    step body (.stelem kind) pc args frame stack memory =
      instructionStep (.stelem kind) pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  by_cases observed : unspecifiedOperands 3 stack = true <;>
    simp only [observed, ↓reduceIte, Bool.false_eq_true] <;> rfl
@[cil_step] theorem step_stelem_ref_eq (stack : List Value) :
    step body .stelem_ref pc args frame stack memory =
      instructionStep .stelem_ref pc frame stack memory := by
  simp only [step, instructionStep, instruction, observerCount, pureArity]
  by_cases observed : unspecifiedOperands 3 stack = true <;>
    simp only [observed, ↓reduceIte, Bool.false_eq_true] <;> rfl
-- A stepped `ldind` or `stind` of a known kind shows its width and sign as literals.
attribute [cil_step, cil_instruction_step] CIL.NumericKind.width CIL.NumericKind.signed
@[cil_step] theorem step_dup_eq (stack : List Value) :
    step body .dup pc args frame stack memory =
      instructionStep .dup pc frame stack memory := id rfl
@[cil_step] theorem step_pop_eq (stack : List Value) :
    step body .pop pc args frame stack memory =
      instructionStep .pop pc frame stack memory := id rfl
-- Locals go through the frame's slot for `index`.
@[cil_step] theorem step_ldloc_eq (index : Nat) (stack : List Value) :
    step body (.ldloc index) pc args frame stack memory = do
      let some slot := frame.locals[index]? | .error .invalidState
      return FrameAction.next (pc + 1) ((← loadLocal memory slot) :: stack) frame memory := id rfl

@[cil_step] theorem step_ldloca_eq (index : Nat) (stack : List Value) :
    step body (.ldloca index) pc args frame stack memory = do
      let some slot := frame.locals[index]? | .error .invalidState
      return FrameAction.next (pc + 1) ((← localAddress memory index slot) :: stack) frame
        memory :=
  id rfl

@[cil_step] theorem step_stloc_eq (index : Nat) (value : Value) (rest : List Value) :
    step body (.stloc index) pc args frame (value :: rest) memory = do
      let some slot := frame.locals[index]? | .error .invalidState
      let (slot, memory) ← storeLocal memory slot value
      return FrameAction.next (pc + 1) rest { frame with locals := frame.locals.set index slot }
        memory := id rfl

/-- A homed argument load steps as `ldloc` of its home slot. -/
theorem step_ldarg_home_ldloc (index : Nat) (stack : List Value) (slot : Nat)
    (access : body.argumentAccess index = .home slot) :
    step body (.ldarg index) pc args frame stack memory =
      step body (.ldloc slot) pc args frame stack memory := by
  rw [step_ldarg_home_eq body pc args frame memory index stack slot access, step_ldloc_eq]

#print axioms step_ldarg_home_ldloc

/-- A homed argument store steps as `stloc` of its home slot. -/
theorem step_starg_home_stloc (index : Nat) (value : Value) (rest : List Value) (slot : Nat)
    (access : body.argumentAccess index = .home slot) :
    step body (.starg index) pc args frame (value :: rest) memory =
      step body (.stloc slot) pc args frame (value :: rest) memory := by
  rw [step_starg_home_eq body pc args frame memory index value rest slot access, step_stloc_eq]

#print axioms step_starg_home_stloc

/-- A homed argument's address steps as `ldloca` of its home slot. -/
theorem step_ldarga_home_ldloca (index : Nat) (stack : List Value) (slot : Nat)
    (access : body.argumentAccess index = .home slot) :
    step body (.ldarga index) pc args frame stack memory =
      step body (.ldloca slot) pc args frame stack memory := by
  rw [step_ldarga_home_eq body pc args frame memory index stack slot access, step_ldloca_eq]

#print axioms step_ldarga_home_ldloca

/-- Memory operations fault on unspecified operand bits, then run `staticInstruction`. -/
@[cil_step] theorem step_memory_eq (operation : CIL.MemoryOp) (stack : List Value) :
    step body (.memory operation) pc args frame stack memory =
      if unspecifiedOperands operation.argumentCount stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let operands ← viewOperands frame memory (viewOperandCount operation) stack
        let (memory, values) ← staticInstruction body pc operation operands memory
        return FrameAction.next (pc + 1) values frame memory := by
  simp only [step, observerCount]
  rfl

/-- `ldsfld` pushes the value `staticLoad` reads through the descriptor bound to its pc. Stated
    as the match a rewrite of the read leaves, so checking a stepped load never evaluates it. -/
@[cil_step] theorem step_ldsfld_eq (field : CIL.Extraction.FieldRef) (stack : List Value) :
    step body (.ldsfld field) pc args frame stack memory =
      match staticLoad body pc memory with
      | .ok result => .ok (.next (pc + 1) (result.2 :: stack) frame result.1)
      | .error fault => .error fault := by
  have unfolded : step body (.ldsfld field) pc args frame stack memory = (do
      let (memory, value) ← staticLoad body pc memory
      return FrameAction.next (pc + 1) (value :: stack) frame memory) := id rfl
  rw [unfolded]
  cases staticLoad body pc memory <;> rfl

#print axioms step_ldsfld_eq

/-- `ldsflda` pushes the reference to the storage of the descriptor bound to its pc. Stated as
    the match a rewrite of the read leaves, so checking a stepped load never evaluates it. -/
@[cil_step] theorem step_ldsflda_eq (field : CIL.Extraction.FieldRef) (stack : List Value) :
    step body (.ldsflda field) pc args frame stack memory =
      match staticAddress body pc memory with
      | .ok result => .ok (.next (pc + 1) (result.2 :: stack) frame result.1)
      | .error fault => .error fault := by
  have unfolded : step body (.ldsflda field) pc args frame stack memory = (do
      let (memory, value) ← staticAddress body pc memory
      return FrameAction.next (pc + 1) (value :: stack) frame memory) := id rfl
  rw [unfolded]
  cases staticAddress body pc memory <;> rfl

#print axioms step_ldsflda_eq

/-- A field `ldtoken` pushes the same reference as `ldsflda` of that field. Stated as the match
    a rewrite of the read leaves, so checking a stepped load never evaluates it. -/
@[cil_step] theorem step_ldtoken_eq (field : CIL.Extraction.FieldRef) (stack : List Value) :
    step body (.ldtoken (.field field)) pc args frame stack memory =
      match staticAddress body pc memory with
      | .ok result => .ok (.next (pc + 1) (result.2 :: stack) frame result.1)
      | .error fault => .error fault := by
  have unfolded : step body (.ldtoken (.field field)) pc args frame stack memory = (do
      let (memory, value) ← staticAddress body pc memory
      return FrameAction.next (pc + 1) (value :: stack) frame memory) := id rfl
  rw [unfolded]
  cases staticAddress body pc memory <;> rfl

#print axioms step_ldtoken_eq

/-- `stsfld` faults: no static field is writable. -/
@[cil_step] theorem step_stsfld_eq (field : CIL.Extraction.FieldRef) (stack : List Value) :
    step body (.stsfld field) pc args frame stack memory =
      if unspecifiedOperands 1 stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else .error (.unsupported "Static field store") := by
  simp only [step, observerCount]
  rfl

#print axioms step_stsfld_eq

/-- An intrinsic must be available in the method's profile; its `argc` operands are taken
    deepest first. -/
@[cil_step] theorem step_intrinsic_eq (operation : CIL.Intrinsic) (argc : Nat)
    (stack : List Value) :
    step body (.intrinsic operation argc) pc args frame stack memory =
      if !operation.available body.profile then
        .error (.unsupported "Intrinsic unavailable in target profile")
      else if stack.length < argc then .error .invalidState else do
        let operands ← scalars (stack.take argc).reverse
        let value ← checkedIntrinsic operation operands
        return FrameAction.next (pc + 1)
          ((← checkedValue memory (.scalar value)) :: stack.drop argc) frame memory :=
  id rfl

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
  simp only [invoke_eq, found, checked, setup, Except.mapError, Bind.bind, Except.bind]
  exact executed

/-- A fetched step that continues at `target` costs one unit of fuel. -/
theorem run_next {program : CIL.Program} {fuel method pc target : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory}
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory =
      .ok (.next target values nextFrame updated)) :
    run program (fuel + 1) method pc args frame stack memory =
      run program fuel method target args nextFrame values updated := by
  simp only [run_succ, methodFound, instructionFound, stepped, Except.mapError, Bind.bind,
    Except.bind]
#print axioms run_next

/-- Return through frame expiration and the checked result validation. -/
theorem run_return {program : CIL.Program} {fuel method pc : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack values : List Value}
    {frame : Frame} {memory updated : Memory}
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.returned values updated))
    (checked : values.mapM (checkedValue (leaveFrame frame updated)) = .ok values) :
    run program (fuel + 1) method pc args frame stack memory =
      .ok (leaveFrame frame updated, values) := by
  simp only [run_succ, methodFound, instructionFound, stepped, checked,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms run_return

/-- A fetched step that faults ends the run with that fault, located at its method and pc. -/
theorem run_fault {program : CIL.Program} {fuel method pc : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack : List Value}
    {frame : Frame} {memory : Memory} {fault : ExecutionFault}
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (failed : step body op pc args frame stack memory = .error fault) :
    run program (fuel + 1) method pc args frame stack memory = .error ⟨method, pc, fault⟩ := by
  simp only [run_succ, methodFound, instructionFound, failed, Except.mapError, Bind.bind,
    Except.bind]

#print axioms run_fault

/-- An invocation whose checked entry succeeds faults exactly as its body's run does. -/
theorem invoke_of_run_fault {program : CIL.Program} {fuel method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered : Memory} {fault : LocatedFault}
    (found : program[method]? = some body)
    (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (executed : run program fuel method 0 args frame [] entered = .error fault) :
    invoke program fuel method args memory = .error fault := by
  simp only [invoke_eq, found, checked, setup, Except.mapError, Bind.bind, Except.bind]
  exact executed

#print axioms invoke_of_run_fault

/-- Compose one checked fetched step with a terminating continuation without
    fixing the continuation's fuel in the caller proof. -/
theorem run_next_exists {program : CIL.Program} {method pc target : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory}
    (post : Memory → List Value → Prop)
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory =
      .ok (.next target values nextFrame updated))
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
/-- Some fuel runs to a successful return satisfying `post` when the fetched instruction
    returns checked values that satisfy it. -/
theorem run_return_exists {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack values : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.returned values updated))
    (checked : values.mapM (checkedValue (leaveFrame frame updated)) = .ok values)
    (satisfied : post (leaveFrame frame updated) values) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧
        post result returned :=
  ⟨1, _, _, run_return (fuel := 0) methodFound instructionFound stepped checked, satisfied⟩

/-- Reduces an invocation goal to running the body from pc 0 in the frame `enterFrame`
    builds for checked arguments. -/
theorem invoke_exists_of_run {program : CIL.Program} {method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered : Memory}
    {post : Memory → List Value → Prop}
    (found : program[method]? = some body)
    (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (executed : ∃ fuel result returned,
      run program fuel method 0 args frame [] entered = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      invoke program fuel method args memory = .ok (result, returned) ∧ post result returned := by
  obtain ⟨fuel, result, returned, ran, satisfied⟩ := executed
  exact ⟨fuel, result, returned, invoke_of_run found checked setup ran, satisfied⟩

#print axioms run_return_exists
#print axioms invoke_exists_of_run

end CIL.Safety
