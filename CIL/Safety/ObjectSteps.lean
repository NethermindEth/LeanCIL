import CIL.Safety.StepComposition
import CIL.Safety.ObjectAllocationLemmas
import CIL.Safety.ValueSteps

/-!
# Object step equations

`cil_step` equations for the instructions that observe class instance references: identity
comparison (`ceq`, `beq`, `bne.un`), presence (`cgt.un` against null, `brtrue`, `brfalse`),
`isinst` and `castclass` (through `objectTest`, decided by a `runtimeTypeOf` fact), `ldnull`,
`ldstr` of a caller-bound literal (`literalObject_of_lookup`), `ldfld`/`stfld` of scalar class
fields, and `newobj`, whose link fact selects a class construction, which calls the constructor
with a fresh instance that `allocateObject_ok` or `allocateObject_insufficient` decides, or a
value-type construction, and `callvirt` of a non-virtual
method, which calls with a live receiver and throws `NullReferenceException` on a null one
(`receiverCall`), and `callvirt` of a virtual method, which enters the body its dispatch table
lists for the receiver's runtime class (`virtualCall`, decided by a `runtimeTypeOf` fact),
and the argument guards, which raise their named exception or pop their operands
(`zeroGuardOutcome`, `comparisonGuardOutcome`). Each states the dispatcher arm of
`CIL/Safety/Execution.lean` for object operands, so stepping never unfolds the dispatcher. The
observations themselves unfold through `cil_checked` down to `formObject`, which a caller's
facts or `formObject_null` decide; field accesses leave `objectFieldAddress` and the byte
access for a caller's facts, one equation per field width.
-/

namespace CIL.Safety

/-- The null object reference forms in every memory. -/
@[cil_checked] theorem formObject_null (memory : Memory) :
    formObject memory .null = .ok (.object .null) := rfl

#print axioms formObject_null

/-- A literal bound to `reference` loads what forming that reference gives. -/
theorem literalObject_of_lookup {memory : Memory} {text : String} {reference : Reference}
    (bound : memory.literals.lookup text = some reference) :
    literalObject memory text = formObject memory (.address reference) := by
  simp only [literalObject, bound]

#print axioms literalObject_of_lookup

attribute [cil_checked] objectNonNull objectEqual objectAboveNull objectTest

/-- A formed object reference is a checked value as it stands. -/
@[cil_checked] theorem checkedValue_object (memory : Memory) (reference : ManagedReference)
    (formed : formObject memory reference = .ok (.object reference)) :
    checkedValue memory (.object reference) = .ok (.object reference) := formed

#print axioms checkedValue_object

/-- An object home loads its formed reference. -/
@[cil_checked] theorem loadLocal_object (memory : Memory) (reference : ManagedReference)
    (formed : formObject memory reference = .ok (.object reference)) :
    loadLocal memory (.object (some reference)) = .ok (.object reference) := formed

#print axioms loadLocal_object

/-- Replacing an object home's reference preserves memory and requires the new one to form. -/
@[cil_checked] theorem storeLocal_object (memory : Memory) (previous : Option ManagedReference)
    (reference : ManagedReference)
    (formed : formObject memory reference = .ok (.object reference)) :
    storeLocal memory (.object previous) (.object reference) =
      .ok (.object (some reference), memory) := by
  simp [storeLocal, Value.hasUnspecified, formed, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms storeLocal_object

section ObjectEquations

variable (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)

/-- `newobj` checks its constructor's arguments for unspecified bits and then builds what the
    link at its pc states: a zeroed value-type temporary owned by the frame and passed by address,
    or an instance of the constructor's class with the link's bases, passed as the receiver and
    left under the rest of the stack. Any other link faults before anything is allocated. -/
@[cil_step] theorem step_newobj_eq (constructor : CIL.Extraction.MethodRef)
    (stack : List Value) :
    step body (.newobj constructor) pc args frame stack memory =
      if unspecifiedOperands constructor.parameters.length stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else match body.linkAt pc with
        | some (.aggregate callee size) =>
          if size = 0 || stack.length < constructor.parameters.length then .error .invalidState
          else do
            let arguments ←
              (stack.take constructor.parameters.length).reverse.mapM (checkedValue memory)
            let (temporary, allocated) ← allocateHome memory frame.activation size
            let (_, stored) ← storeLocal allocated (.bytes (.aggregate size) temporary)
              (.scalar (.aggregate (List.replicate size 0)))
            return FrameAction.construct callee (.reference (.address temporary) :: arguments)
              (stack.drop constructor.parameters.length)
              { frame with owned := temporary.allocation :: frame.owned } temporary
              (.aggregate size) stored
        | some (.object callee bases size) =>
          if stack.length < constructor.parameters.length then .error .invalidState
          else do
            let arguments ←
              (stack.take constructor.parameters.length).reverse.mapM (checkedValue memory)
            let (object, allocated) ← allocateObject memory ⟨constructor.owner, bases⟩ size
            return FrameAction.call callee (.object (.address object) :: arguments)
              (.object (.address object) :: stack.drop constructor.parameters.length) allocated
        | _ => .error unlinkedCall := by
  simp only [step, observerCount]
  rfl

#print axioms step_newobj_eq

/-- The call a receiver-checked `callvirt` makes with checked `arguments`, receiver first: a null
    receiver throws `NullReferenceException`, and a receiver that is no object reference is
    ill-typed. This is the `callInstance` arm of `step` after its argument checks. -/
def receiverCall (callee : Nat) (arguments rest : List Value) (memory : Memory) :
    ExecutionResult FrameAction :=
  match arguments with
  | .object (.address _) :: _ => .ok (.call callee arguments rest memory)
  | .object .null :: _ => .error (.thrown .nullReference)
  | _ => .error .invalidState

/-- `callvirt` of a non-virtual method checks its `argc` arguments and calls the method its link
    names with a live receiver; a null receiver throws `NullReferenceException` before the call. -/
@[cil_step] theorem step_callInstance_eq (target argc : Nat) (stack : List Value) :
    step body (.callInstance target argc) pc args frame stack memory =
      if unspecifiedOperands argc stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else match body.linkAt pc with
        | some (.direct callee) =>
          if stack.length < argc then .error .invalidState
          else (do
            let arguments ← (stack.take argc).reverse.mapM (checkedValue memory)
            receiverCall callee arguments (stack.drop argc) memory)
        | _ => .error unlinkedCall := by
  simp only [step, observerCount]
  rfl

#print axioms step_callInstance_eq

/-- A live receiver makes the call with the checked arguments as they stand. -/
@[cil_checked] theorem receiverCall_address (callee : Nat) (receiver : Reference)
    (arguments rest : List Value) :
    receiverCall callee (.object (.address receiver) :: arguments) rest memory =
      .ok (.call callee (.object (.address receiver) :: arguments) rest memory) := rfl

#print axioms receiverCall_address

/-- A null receiver throws before the call. -/
@[cil_checked] theorem receiverCall_null (callee : Nat) (arguments rest : List Value) :
    receiverCall callee (.object .null :: arguments) rest memory =
      .error (.thrown .nullReference) := rfl

#print axioms receiverCall_null

/-- The call a virtual `callvirt` makes with checked `arguments`, receiver first: into the body
    `targets` lists for a live receiver's runtime class, `NullReferenceException` for a null
    receiver. This is the `callVirtual` arm of `step` after its argument checks. -/
def virtualCall (targets : List (CIL.Extraction.TypeExpr × Nat)) (arguments rest : List Value)
    (memory : Memory) : ExecutionResult FrameAction :=
  match arguments with
  | .object (.address receiver) :: _ => do
    return .call (← virtualTarget memory targets receiver) arguments rest memory
  | .object .null :: _ => .error (.thrown .nullReference)
  | _ => .error .invalidState

/-- `callvirt` of a virtual method checks its `argc` arguments and enters the body its link's
    table selects for the receiver; a null receiver throws `NullReferenceException` before the
    call. -/
@[cil_step] theorem step_callVirtual_eq (stated : List (CIL.Extraction.TypeExpr × Nat))
    (argc : Nat) (stack : List Value) :
    step body (.callVirtual stated argc) pc args frame stack memory =
      if unspecifiedOperands argc stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else match body.linkAt pc with
        | some (.virtual targets) =>
          if stack.length < argc then .error .invalidState
          else (do
            let arguments ← (stack.take argc).reverse.mapM (checkedValue memory)
            virtualCall targets arguments (stack.drop argc) memory)
        | _ => .error unlinkedCall := by
  simp only [step, observerCount]
  rfl

#print axioms step_callVirtual_eq

/-- A live receiver enters the body the table lists for its runtime class; a step fact for
    `runtimeTypeOf` then decides the lookup. -/
@[cil_checked] theorem virtualCall_address (targets : List (CIL.Extraction.TypeExpr × Nat))
    (receiver : Reference) (arguments rest : List Value) :
    virtualCall targets (.object (.address receiver) :: arguments) rest memory = (do
      let type ← runtimeTypeOf memory receiver
      match targets.lookup type.identity with
      | some callee => .ok (.call callee (.object (.address receiver) :: arguments) rest memory)
      | none => .error outsideDispatchTable) := by
  simp only [virtualCall, virtualTarget, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases runtimeTypeOf memory receiver with
  | error => rfl
  | ok type =>
    dsimp only
    cases targets.lookup type.identity <;> rfl

#print axioms virtualCall_address

/-- A live receiver of a class the table lists enters that class's body. -/
theorem virtualCall_listed (targets : List (CIL.Extraction.TypeExpr × Nat))
    (receiver : Reference) (type : RuntimeType) (callee : Nat) (arguments rest : List Value)
    (typed : runtimeTypeOf memory receiver = .ok type)
    (listed : targets.lookup type.identity = some callee) :
    virtualCall targets (.object (.address receiver) :: arguments) rest memory =
      .ok (.call callee (.object (.address receiver) :: arguments) rest memory) := by
  simp [virtualCall_address, typed, listed, Bind.bind, Except.bind]

#print axioms virtualCall_listed

/-- A live receiver of a class the table omits is the model fault `outsideDispatchTable`, never
    a call or a named exception. -/
theorem virtualCall_outside (targets : List (CIL.Extraction.TypeExpr × Nat))
    (receiver : Reference) (type : RuntimeType) (arguments rest : List Value)
    (typed : runtimeTypeOf memory receiver = .ok type)
    (omitted : targets.lookup type.identity = none) :
    virtualCall targets (.object (.address receiver) :: arguments) rest memory =
      .error outsideDispatchTable := by
  simp [virtualCall_address, typed, omitted, Bind.bind, Except.bind]

#print axioms virtualCall_outside

/-- A null receiver throws before the call. -/
@[cil_checked] theorem virtualCall_null (targets : List (CIL.Extraction.TypeExpr × Nat))
    (arguments rest : List Value) :
    virtualCall targets (.object .null :: arguments) rest memory =
      .error (.thrown .nullReference) := rfl

#print axioms virtualCall_null

-- These equations are closed by `id rfl` because simp applies a lemma proved by `rfl` without a
-- proof term, and the kernel would then reduce `step` again at every use.
/-- `ceq` on two object references pushes their identity comparison. -/
@[cil_step high] theorem step_ceq_object_eq (left right : ManagedReference) (rest : List Value) :
    step body .ceq pc args frame (.object right :: .object left :: rest) memory = do
      let equal ← objectEqual memory left right
      return .next (pc + 1) (.scalar (.i32 (if equal then 1 else 0)) :: rest) frame memory :=
  id rfl

/-- `beq` on two object references branches when they are the same instance. -/
@[cil_step high] theorem step_beq_object_eq (target : Nat) (left right : ManagedReference)
    (rest : List Value) :
    step body (.beq target) pc args frame (.object right :: .object left :: rest) memory = do
      let equal ← objectEqual memory left right
      return .next (if equal then target else pc + 1) rest frame memory :=
  id rfl

/-- `bne.un` on two object references branches when they are different instances. -/
@[cil_step high] theorem step_bne_un_object_eq (target : Nat) (left right : ManagedReference)
    (rest : List Value) :
    step body (.bne_un target) pc args frame (.object right :: .object left :: rest) memory = do
      let equal ← objectEqual memory left right
      return .next (if equal then pc + 1 else target) rest frame memory :=
  id rfl

/-- `cgt.un` of an object reference against null pushes whether the reference is present. -/
@[cil_step high] theorem step_cgt_un_object_eq (left right : ManagedReference)
    (rest : List Value) :
    step body .cgt_un pc args frame (.object right :: .object left :: rest) memory = do
      let present ← objectAboveNull memory left right
      return .next (pc + 1) (.scalar (.i32 (if present then 1 else 0)) :: rest) frame memory :=
  id rfl

/-- `brfalse` on an object reference branches when it is null. -/
@[cil_step high] theorem step_brfalse_object_eq (target : Nat) (value : ManagedReference)
    (rest : List Value) :
    step body (.brfalse target) pc args frame (.object value :: rest) memory = do
      let present ← objectNonNull memory value
      return .next (if present then pc + 1 else target) rest frame memory :=
  id rfl

/-- `brtrue` on an object reference branches when it is present. -/
@[cil_step high] theorem step_brtrue_object_eq (target : Nat) (value : ManagedReference)
    (rest : List Value) :
    step body (.brtrue target) pc args frame (.object value :: rest) memory = do
      let present ← objectNonNull memory value
      return .next (if present then target else pc + 1) rest frame memory :=
  id rfl

/-- `castclass` keeps an object reference whose runtime lineage holds the class, and null;
    any other object throws `InvalidCastException`. -/
@[cil_step high] theorem step_castclass_eq (type : CIL.Extraction.TypeExpr)
    (value : ManagedReference) (rest : List Value) :
    step body (.castclass type) pc args frame (.object value :: rest) memory = do
      let result ← objectTest memory type true value
      return .next (pc + 1) (.object result :: rest) frame memory :=
  id rfl

/-- `isinst` keeps an object reference whose runtime lineage holds the class, and null; any
    other object becomes null. -/
@[cil_step high] theorem step_isinst_eq (type : CIL.Extraction.TypeExpr)
    (value : ManagedReference) (rest : List Value) :
    step body (.isinst type) pc args frame (.object value :: rest) memory = do
      let result ← objectTest memory type false value
      return .next (pc + 1) (.object result :: rest) frame memory :=
  id rfl

/-- `newarr` with an int32 length allocates an array of its element's shape and pushes it. -/
@[cil_step high] theorem step_newarr_i32_eq (element : CIL.Extraction.TypeExpr)
    (bits : BitVec 32) (rest : List Value) :
    step body (.newarr element) pc args frame (.scalar (.i32 bits) :: rest) memory = do
      let (array, allocated) ← allocateElements (body.elementShape element) (.i32 bits) memory
      return .next (pc + 1) (array :: rest) frame allocated := id rfl

/-- `newarr` with a native length allocates an array of its element's shape and pushes it. -/
@[cil_step high] theorem step_newarr_i64_eq (element : CIL.Extraction.TypeExpr)
    (bits : BitVec 64) (rest : List Value) :
    step body (.newarr element) pc args frame (.scalar (.i64 bits) :: rest) memory = do
      let (array, allocated) ← allocateElements (body.elementShape element) (.i64 bits) memory
      return .next (pc + 1) (array :: rest) frame allocated := id rfl

/-- An inline element shape allocates a value array. -/
@[cil_step] theorem allocateElements_value (element : CIL.ArrayElement) (length : CIL.Value) :
    allocateElements (.value element) length memory = do
      let (view, allocated) ← newArray memory element length
      return (.array view, allocated) := rfl

/-- A class element shape allocates an array of null references. -/
@[cil_step] theorem allocateElements_reference (element : CIL.Extraction.TypeExpr)
    (length : CIL.Value) :
    allocateElements (.reference element) length memory = do
      let (array, allocated) ← newReferenceArray memory element length
      return (.object (.address array), allocated) := rfl

/-- `ldnull` pushes the null object reference and leaves memory unchanged. -/
@[cil_step high] theorem step_ldnull_eq (stack : List Value) :
    step body .ldnull pc args frame stack memory =
      .ok (.next (pc + 1) (.object .null :: stack) frame memory) := id rfl

/-- `ldstr` pushes the object bound to its text and leaves memory unchanged. -/
@[cil_step high] theorem step_stringLiteral_eq (text : String) (stack : List Value) :
    step body (.memory (.stringLiteral text)) pc args frame stack memory = do
      let value ← literalObject memory text
      return .next (pc + 1) (value :: stack) frame memory := by
  simp only [step, observerCount, staticInstruction, memoryInstruction,
    stringLiteralInstruction, CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take,
    List.any, Bool.false_eq_true, ite_false, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases literalObject memory text <;> rfl

/-- `ThrowIfNull` throws `ArgumentNullException` for a null argument; otherwise it pops the
    argument and the parameter name and leaves memory unchanged. -/
@[cil_step high] theorem step_throwIfNull_eq (name argument : ManagedReference)
    (rest : List Value) :
    step body (.memory .throwIfNull) pc args frame (.object name :: .object argument :: rest)
        memory =
      match argument with
      | .null => .error (.thrown .argumentNull)
      | .address _ => .ok (.next (pc + 1) rest frame memory) := by
  cases argument <;> rfl

/-- The outcome of a zero guard on a `width`-bit value. -/
def zeroGuardOutcome (guard : ZeroGuard) (width : Nat) (signed : Bool) (value : CIL.Value) :
    ExecutionResult Unit :=
  match guardOperand width signed value with
  | some number =>
    match guard.throws number with
    | true => .error (.thrown .argumentOutOfRange)
    | false => .ok ()
  | none => .error .invalidState

/-- The outcome of a comparison guard on a `width`-bit value and its bound. -/
def comparisonGuardOutcome (guard : ComparisonGuard) (width : Nat) (signed : Bool)
    (value other : CIL.Value) : ExecutionResult Unit :=
  match guardOperand width signed value, guardOperand width signed other with
  | some number, some bound =>
    match guard.throws number bound with
    | true => .error (.thrown .argumentOutOfRange)
    | false => .ok ()
  | _, _ => .error .invalidState

/-- A zero guard on a 32-bit stack value throws, or pops it with the parameter name. -/
@[cil_step high] theorem step_zeroGuard_i32_eq (guard : ZeroGuard) (width : Nat) (signed : Bool)
    (name : ManagedReference) (bits : CIL.W32) (rest : List Value) :
    step body (.memory (.zeroGuard guard width signed)) pc args frame
        (.object name :: .scalar (.i32 bits) :: rest) memory = do
      zeroGuardOutcome guard width signed (.i32 bits)
      return .next (pc + 1) rest frame memory := by
  simp only [step, observerCount, Bool.or_false, staticInstruction, memoryInstruction,
    zeroGuardInstruction, zeroGuardOutcome, CIL.MemoryOp.argumentCount, unspecifiedOperands,
    List.take_succ_cons, List.take_zero, List.any_cons, List.any_nil, Value.hasUnspecified,
    CIL.Value.hasUnspecified, Bool.false_eq_true, ite_false]
  rcases guardOperand width signed (.i32 bits) with _ | number
  · rfl
  · dsimp only; cases guard.throws number <;> rfl

/-- A zero guard on a 64-bit stack value throws, or pops it with the parameter name. -/
@[cil_step high] theorem step_zeroGuard_i64_eq (guard : ZeroGuard) (width : Nat) (signed : Bool)
    (name : ManagedReference) (bits : CIL.W64) (rest : List Value) :
    step body (.memory (.zeroGuard guard width signed)) pc args frame
        (.object name :: .scalar (.i64 bits) :: rest) memory = do
      zeroGuardOutcome guard width signed (.i64 bits)
      return .next (pc + 1) rest frame memory := by
  simp only [step, observerCount, Bool.or_false, staticInstruction, memoryInstruction,
    zeroGuardInstruction, zeroGuardOutcome, CIL.MemoryOp.argumentCount, unspecifiedOperands,
    List.take_succ_cons, List.take_zero, List.any_cons, List.any_nil, Value.hasUnspecified,
    CIL.Value.hasUnspecified, Bool.false_eq_true, ite_false]
  rcases guardOperand width signed (.i64 bits) with _ | number
  · rfl
  · dsimp only; cases guard.throws number <;> rfl

/-- A comparison guard on 32-bit stack values throws, or pops both with the parameter name. -/
@[cil_step high] theorem step_comparisonGuard_i32_eq (guard : ComparisonGuard) (width : Nat)
    (signed : Bool) (name : ManagedReference) (other value : CIL.W32) (rest : List Value) :
    step body (.memory (.comparisonGuard guard width signed)) pc args frame
        (.object name :: .scalar (.i32 other) :: .scalar (.i32 value) :: rest) memory = do
      comparisonGuardOutcome guard width signed (.i32 value) (.i32 other)
      return .next (pc + 1) rest frame memory := by
  simp only [step, observerCount, Bool.or_false, staticInstruction, memoryInstruction,
    comparisonGuardInstruction, comparisonGuardOutcome, CIL.MemoryOp.argumentCount,
    unspecifiedOperands, List.take_succ_cons, List.take_zero, List.any_cons, List.any_nil,
    Value.hasUnspecified, CIL.Value.hasUnspecified, Bool.false_eq_true, ite_false]
  rcases guardOperand width signed (.i32 value) with _ | number <;>
    rcases guardOperand width signed (.i32 other) with _ | bound
  all_goals try rfl
  dsimp only; cases guard.throws number bound <;> rfl

/-- A comparison guard on 64-bit stack values throws, or pops both with the parameter name. -/
@[cil_step high] theorem step_comparisonGuard_i64_eq (guard : ComparisonGuard) (width : Nat)
    (signed : Bool) (name : ManagedReference) (other value : CIL.W64) (rest : List Value) :
    step body (.memory (.comparisonGuard guard width signed)) pc args frame
        (.object name :: .scalar (.i64 other) :: .scalar (.i64 value) :: rest) memory = do
      comparisonGuardOutcome guard width signed (.i64 value) (.i64 other)
      return .next (pc + 1) rest frame memory := by
  simp only [step, observerCount, Bool.or_false, staticInstruction, memoryInstruction,
    comparisonGuardInstruction, comparisonGuardOutcome, CIL.MemoryOp.argumentCount,
    unspecifiedOperands, List.take_succ_cons, List.take_zero, List.any_cons, List.any_nil,
    Value.hasUnspecified, CIL.Value.hasUnspecified, Bool.false_eq_true, ite_false]
  rcases guardOperand width signed (.i64 value) with _ | number <;>
    rcases guardOperand width signed (.i64 other) with _ | bound
  all_goals try rfl
  dsimp only; cases guard.throws number bound <;> rfl

#print axioms step_throwIfNull_eq
#print axioms step_zeroGuard_i32_eq
#print axioms step_zeroGuard_i64_eq
#print axioms step_comparisonGuard_i32_eq
#print axioms step_comparisonGuard_i64_eq

/-- `ldlen` of an array of class references pushes its length as a native integer. -/
@[cil_step high] theorem step_ldlen_object_eq (array : ManagedReference) (rest : List Value) :
    step body .ldlen pc args frame (.object array :: rest) memory = do
      let found ← referenceArrayOf memory array
      return .next (pc + 1) (.scalar (.i64 (BitVec.ofNat 64 found.2.2)) :: rest) frame memory := by
  rw [step_ldlen_eq]
  simp only [instructionStep, instruction, elementInstruction, Bind.bind, Except.bind, Pure.pure,
    Except.pure]
  cases referenceArrayOf memory array <;> rfl

/-- `ldlen` of a null object reference, as `ldnull` pushes it, throws `NullReferenceException`. -/
@[cil_step high] theorem step_ldlen_object_null_eq (rest : List Value) :
    step body .ldlen pc args frame (.object .null :: rest) memory =
      .error (.thrown .nullReference) := by
  rw [step_ldlen_object_eq]
  rfl

/-- `ldelem.ref` with an int32 index pushes the reference its element's slot holds. -/
@[cil_step high] theorem step_ldelem_ref_i32_eq (index : BitVec 32)
    (array : ManagedReference) (rest : List Value) :
    step body .ldelem_ref pc args frame (.scalar (.i32 index) :: .object array :: rest) memory = do
      let slot ← referenceArraySlot memory array index.toNat
      let value ← loadSlot memory slot.1
      return .next (pc + 1) (value :: rest) frame memory := by
  rw [step_ldelem_ref_eq]
  simp only [instructionStep, instruction, elementInstruction, arrayIndex, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  cases referenceArraySlot memory array index.toNat <;> try rfl
  rename_i slot
  dsimp only
  cases loadSlot memory slot.1 <;> rfl

/-- `stelem.ref` with an int32 index checks the stored object's class against the element
    class, then stores it into the element's slot. -/
@[cil_step high] theorem step_stelem_ref_i32_eq (index : BitVec 32)
    (value array : ManagedReference) (rest : List Value) :
    step body .stelem_ref pc args frame
        (.object value :: .scalar (.i32 index) :: .object array :: rest) memory = do
      let slot ← referenceArraySlot memory array index.toNat
      let _ ← storableIn memory slot.2 value
      let after ← storeSlot memory slot.1 value
      return .next (pc + 1) rest frame after := by
  rw [step_stelem_ref_eq]
  simp only [instructionStep, instruction, elementInstruction, arrayIndex, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  cases referenceArraySlot memory array index.toNat <;> try rfl
  rename_i slot
  dsimp only
  cases storableIn memory slot.2 value <;> try rfl
  dsimp only
  cases storeSlot memory slot.1 value <;> rfl

/-- A readable slot loads the reference it holds, which must still form. -/
theorem loadSlot_of_access {memory : Memory} {field : Reference}
    (readable : access memory field objectFieldSlot ordinaryAccessAlignment false = .ok ()) :
    loadSlot memory field = formObject memory (memory.slots field.allocation field.offset) := by
  simp only [loadSlot, readable, checkedAt, Except.mapError, Bind.bind, Except.bind]

/-- A writable slot stores a formed reference, changing nothing else. -/
theorem storeSlot_of_access {memory : Memory} {field : Reference} {value : ManagedReference}
    (writable : access memory field objectFieldSlot ordinaryAccessAlignment true = .ok ())
    (formed : formObject memory value = .ok (.object value)) :
    storeSlot memory field value = .ok (setSlot memory field value) := by
  simp only [storeSlot, writable, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- A readable value-array slot loads the array the reference it holds names. -/
theorem loadArraySlot_of_access {memory : Memory} {field : Reference}
    {element : CIL.ArrayElement}
    (readable : access memory field objectFieldSlot ordinaryAccessAlignment false = .ok ()) :
    loadArraySlot memory field element =
      arrayOfSlot memory (memory.slots field.allocation field.offset) element := by
  simp only [loadArraySlot, readable, checkedAt, Except.mapError, Bind.bind, Except.bind]

/-- A reference to offset 0 of a live heap allocation of `length` elements names that whole
    array, once its extent validates. -/
theorem arrayOfSlot_whole {memory : Memory} {array : Reference} {allocation : Allocation}
    {length : Nat} {element : CIL.ArrayElement}
    (found : liveAllocation memory array.allocation = .ok allocation)
    (heap : allocation.kind = .managedHeap) (origin : array.offset = 0)
    (positive : 0 < element.width) (whole : allocation.layout.size = length * element.width)
    (valid : ArrayView.validate ⟨.address array, length, element⟩ memory = .ok ()) :
    arrayOfSlot memory (.address array) element =
      .ok (.array ⟨.address array, length, element⟩) := by
  simp only [arrayOfSlot, found, heap, origin, positive, whole, Nat.mul_mod_left,
    Nat.mul_div_cancel _ positive, valid, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure, and_self, ↓reduceIte]

/-- A writable value-array slot stores the origin of a whole live heap array of its element. -/
theorem storeArraySlot_whole {memory : Memory} {field array : Reference}
    {allocation : Allocation} {length : Nat} {element : CIL.ArrayElement}
    (writable : access memory field objectFieldSlot ordinaryAccessAlignment true = .ok ())
    (found : liveAllocation memory array.allocation = .ok allocation)
    (heap : allocation.kind = .managedHeap) (origin : array.offset = 0)
    (whole : allocation.layout.size = length * element.width) :
    storeArraySlot memory field ⟨.address array, length, element⟩ element =
      .ok (setSlot memory field (.address array)) := by
  simp only [storeArraySlot, arraySlotValue, writable, found, heap, origin, whole, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, and_self, ↓reduceIte]

/-- `ldfld` of a class field whose slot holds a `width`-byte integer loads it from the field's
    located address. -/
theorem step_ldfld_word_eq (field : CIL.Extraction.FieldRef) (offset width : Nat) (signed : Bool)
    (fits : width ∈ [1, 2, 4, 8])
    (shape : body.fieldShape field = .classSlot offset (.word width signed))
    (reference : ManagedReference) (rest : List Value) :
    step body (.ldfld field) pc args frame (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let value ← loadValue memory (.address address) width signed
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  simp only [step_ldfld_eq, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    ite_false, fieldLoad, shape, classFieldLoad, fits, not_true_eq_false,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases objectFieldAddress memory reference field.owner offset <;> try rfl
  rename_i address
  dsimp only
  cases loadValue memory (.address address) width signed <;> rfl

/-- `stfld` of a class field whose slot holds an 8-byte integer writes the value's bytes at the
    located address. -/
theorem step_stfld_word_i64_eq (field : CIL.Extraction.FieldRef) (offset : Nat) (signed : Bool)
    (shape : body.fieldShape field = .classSlot offset (.word 8 signed))
    (bits : BitVec 64) (reference : ManagedReference) (rest : List Value) :
    step body (.stfld field) pc args frame
        (.scalar (.i64 bits) :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let after ← checkedAt (.address address) 8
        (write memory address (numberBytes bits.toNat 8) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame after := by
  simp only [step_stfld_eq, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    CIL.Value.hasUnspecified, fieldStore, shape, classFieldStore,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases objectFieldAddress memory reference field.owner offset <;> try rfl
  rename_i address
  dsimp only
  cases checkedAt (.address address) 8
    (write memory address (numberBytes bits.toNat 8) ordinaryAccessAlignment) <;> rfl

/-- `stfld` of a class field whose slot holds a 1-, 2- or 4-byte integer writes the low bytes of
    the int32 value. -/
theorem step_stfld_word_i32_eq (field : CIL.Extraction.FieldRef) (offset width : Nat)
    (signed : Bool) (narrow : width ∈ [1, 2, 4])
    (shape : body.fieldShape field = .classSlot offset (.word width signed))
    (bits : BitVec 32) (reference : ManagedReference) (rest : List Value) :
    step body (.stfld field) pc args frame
        (.scalar (.i32 bits) :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let after ← checkedAt (.address address) width
        (write memory address (numberBytes bits.toNat width) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame after := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at narrow
  rcases narrow with rfl | rfl | rfl
  all_goals
    simp only [step_stfld_eq, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
      CIL.Value.hasUnspecified, fieldStore, shape,
      classFieldStore, Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases objectFieldAddress memory reference field.owner offset <;> try rfl
    rename_i address
    dsimp only
    cases checkedAt (.address address) _
      (write memory address (numberBytes bits.toNat _) ordinaryAccessAlignment) <;> rfl

/-- `ldfld` of a class field holding an object reference pushes the reference its located slot
    holds. -/
theorem step_ldfld_reference_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (shape : body.fieldShape field = .classSlot offset .reference)
    (reference : ManagedReference) (rest : List Value) :
    step body (.ldfld field) pc args frame (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let value ← loadSlot memory address
      return .next (pc + 1) (value :: rest) frame memory := by
  simp only [step_ldfld_eq, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    fieldLoad, shape, classFieldLoad, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  cases objectFieldAddress memory reference field.owner offset <;> try rfl
  rename_i address
  dsimp only
  cases loadSlot memory address <;> rfl

/-- `stfld` of a class field holding an object reference stores the reference into its located
    slot. -/
theorem step_stfld_reference_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (shape : body.fieldShape field = .classSlot offset .reference)
    (value reference : ManagedReference) (rest : List Value) :
    step body (.stfld field) pc args frame (.object value :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let after ← storeSlot memory address value
      return .next (pc + 1) rest frame after := by
  simp only [step_stfld_eq, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    fieldStore, shape, classFieldStore, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  cases objectFieldAddress memory reference field.owner offset <;> try rfl
  rename_i address
  dsimp only
  cases storeSlot memory address value <;> rfl

/-- `ldfld` of a class field holding a value array pushes the whole array its located slot
    names. -/
theorem step_ldfld_array_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (element : CIL.ArrayElement)
    (shape : body.fieldShape field = .classSlot offset (.array element))
    (reference : ManagedReference) (rest : List Value) :
    step body (.ldfld field) pc args frame (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let value ← loadArraySlot memory address element
      return .next (pc + 1) (value :: rest) frame memory := by
  simp only [step_ldfld_eq, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    fieldLoad, shape, classFieldLoad, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  cases objectFieldAddress memory reference field.owner offset <;> try rfl
  rename_i address
  dsimp only
  cases loadArraySlot memory address element <;> rfl

/-- `stfld` of a class field holding a value array keeps the stored array's origin in its
    located slot. -/
theorem step_stfld_array_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (element : CIL.ArrayElement)
    (shape : body.fieldShape field = .classSlot offset (.array element))
    (view : ArrayView) (reference : ManagedReference) (rest : List Value) :
    step body (.stfld field) pc args frame (.array view :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let after ← storeArraySlot memory address view element
      return .next (pc + 1) rest frame after := by
  simp only [step_stfld_eq, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    fieldStore, shape, classFieldStore, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  cases objectFieldAddress memory reference field.owner offset <;> try rfl
  rename_i address
  dsimp only
  cases storeArraySlot memory address view element <;> rfl

/-- `ldflda` of a class field faults: the model gives no address into an object. -/
theorem step_ldflda_class_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (slot : CIL.ClassSlot) (shape : body.fieldShape field = .classSlot offset slot)
    (reference : ManagedReference) (rest : List Value) :
    step body (.ldflda field) pc args frame (.object reference :: rest) memory =
      .error (.unsupported "Class field address") := by
  simp only [step_ldflda_eq, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    fieldReference, shape]
  rfl

/-- `ldfld` of a class field whose slot holds a 1-byte integer, as `step_ldfld_word_eq` states
    it. -/
theorem step_ldfld_word_1_eq (field : CIL.Extraction.FieldRef) (offset : Nat) (signed : Bool)
    (shape : body.fieldShape field = .classSlot offset (.word 1 signed))
    (reference : ManagedReference) (rest : List Value) :
    step body (.ldfld field) pc args frame (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let value ← loadValue memory (.address address) 1 signed
      return .next (pc + 1) (.scalar value :: rest) frame memory :=
  step_ldfld_word_eq body pc args frame memory field offset 1 signed (by decide) shape reference
    rest

/-- `ldfld` of a class field whose slot holds a 2-byte integer, as `step_ldfld_word_eq` states
    it. -/
theorem step_ldfld_word_2_eq (field : CIL.Extraction.FieldRef) (offset : Nat) (signed : Bool)
    (shape : body.fieldShape field = .classSlot offset (.word 2 signed))
    (reference : ManagedReference) (rest : List Value) :
    step body (.ldfld field) pc args frame (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let value ← loadValue memory (.address address) 2 signed
      return .next (pc + 1) (.scalar value :: rest) frame memory :=
  step_ldfld_word_eq body pc args frame memory field offset 2 signed (by decide) shape reference
    rest

/-- `ldfld` of a class field whose slot holds a 4-byte integer, as `step_ldfld_word_eq` states
    it. -/
theorem step_ldfld_word_4_eq (field : CIL.Extraction.FieldRef) (offset : Nat) (signed : Bool)
    (shape : body.fieldShape field = .classSlot offset (.word 4 signed))
    (reference : ManagedReference) (rest : List Value) :
    step body (.ldfld field) pc args frame (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let value ← loadValue memory (.address address) 4 signed
      return .next (pc + 1) (.scalar value :: rest) frame memory :=
  step_ldfld_word_eq body pc args frame memory field offset 4 signed (by decide) shape reference
    rest

/-- `ldfld` of a class field whose slot holds a 8-byte integer, as `step_ldfld_word_eq` states
    it. -/
theorem step_ldfld_word_8_eq (field : CIL.Extraction.FieldRef) (offset : Nat) (signed : Bool)
    (shape : body.fieldShape field = .classSlot offset (.word 8 signed))
    (reference : ManagedReference) (rest : List Value) :
    step body (.ldfld field) pc args frame (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let value ← loadValue memory (.address address) 8 signed
      return .next (pc + 1) (.scalar value :: rest) frame memory :=
  step_ldfld_word_eq body pc args frame memory field offset 8 signed (by decide) shape reference
    rest

/-- `stfld` of a class field whose slot holds a 1-byte integer, as `step_stfld_word_i32_eq`
    states it. -/
theorem step_stfld_word_i32_1_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (signed : Bool) (shape : body.fieldShape field = .classSlot offset (.word 1 signed))
    (bits : BitVec 32) (reference : ManagedReference) (rest : List Value) :
    step body (.stfld field) pc args frame
        (.scalar (.i32 bits) :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let after ← checkedAt (.address address) 1
        (write memory address (numberBytes bits.toNat 1) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame after :=
  step_stfld_word_i32_eq body pc args frame memory field offset 1 signed (by decide) shape bits
    reference rest

/-- `stfld` of a class field whose slot holds a 2-byte integer, as `step_stfld_word_i32_eq`
    states it. -/
theorem step_stfld_word_i32_2_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (signed : Bool) (shape : body.fieldShape field = .classSlot offset (.word 2 signed))
    (bits : BitVec 32) (reference : ManagedReference) (rest : List Value) :
    step body (.stfld field) pc args frame
        (.scalar (.i32 bits) :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let after ← checkedAt (.address address) 2
        (write memory address (numberBytes bits.toNat 2) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame after :=
  step_stfld_word_i32_eq body pc args frame memory field offset 2 signed (by decide) shape bits
    reference rest

/-- `stfld` of a class field whose slot holds a 4-byte integer, as `step_stfld_word_i32_eq`
    states it. -/
theorem step_stfld_word_i32_4_eq (field : CIL.Extraction.FieldRef) (offset : Nat)
    (signed : Bool) (shape : body.fieldShape field = .classSlot offset (.word 4 signed))
    (bits : BitVec 32) (reference : ManagedReference) (rest : List Value) :
    step body (.stfld field) pc args frame
        (.scalar (.i32 bits) :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference field.owner offset
      let after ← checkedAt (.address address) 4
        (write memory address (numberBytes bits.toNat 4) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame after :=
  step_stfld_word_i32_eq body pc args frame memory field offset 4 signed (by decide) shape bits
    reference rest

end ObjectEquations

/-- When set, a closed body's field instruction steps only by the operand's shape fact, and
    evaluating the shape instead is an error, so a test can require that a step reads the fact. -/
register_option cil.requireFieldShapeFacts : Bool := {
  defValue := false
  descr := "step a closed body's field instruction only by the operand's shape fact"
}

open Lean Meta in
/-- How `body` resolves `field` as a `FieldShape` literal, with its proof: from the operand's
    shared shape fact, or by compiled evaluation for a closed body and operand, which the kernel
    checks again. An evaluated shape is the literal a shape fact states, so both give one term. -/
def fieldShapeKnown? (body field : Expr) : MetaM (Option (Expr × Expr)) := do
  let resolver := mkApp2 (mkConst ``CIL.Method.fieldShape) body field
  if let some (.done shared) ← ResolutionFacts.sharedShape? ``CIL.Method.fieldShape resolver then
    if let some proof := shared.proof? then return some (shared.expr, proof)
  if resolver.hasFVar || resolver.hasMVar then return none
  if cil.requireFieldShapeFacts.get (← getOptions) then
    throwError "field {field} of a closed body has no shape fact"
  -- A body the compiler cannot run, such as one over an axiom, is left to simp.
  let evaluated? ← try
      pure (some (toExpr (← unsafe evalExpr CIL.FieldShape (mkConst ``CIL.FieldShape) resolver)))
    catch _ => pure none
  evaluated?.mapM fun evaluated => do
    return (evaluated, ← mkExpectedTypeHint (← mkEqRefl evaluated) (← mkEq resolver evaluated))

open Lean Meta in
/-- How `body` resolves `field`, as `fieldShapeKnown?` finds it, or else as simp rewrites the
    shape with the facts in scope. -/
def fieldShapeIn (body field : Expr) : SimpM (Expr × Expr) := do
  if let some known ← fieldShapeKnown? body field then return known
  let resolver := mkApp2 (mkConst ``CIL.Method.fieldShape) body field
  let shape ← Simp.simp resolver
  return (← whnfR (← instantiateMVars shape.expr), ← shape.getProof)

open Lean Meta in
/-- The lowered instruction a struct field access `op` of `body` steps as, with a proof of
    `∀ pc args frame memory stack` that both step alike; `none` for any other instruction and for
    a field whose shape no fact or evaluation shows to be a struct field. -/
def structFieldLowering? (body op : Expr) : MetaM (Option (Expr × Expr)) := do
  let (name, #[field]) := (← whnfR op).getAppFnArgs | return none
  let accesses := [``CIL.Instruction.ldfld, ``CIL.Instruction.stfld, ``CIL.Instruction.ldflda]
  unless accesses.contains name do
    return none
  let some (shape, proof) ← (try fieldShapeKnown? body field catch _ => pure none) | return none
  let lowering (equation : Name) (lowered : Expr) (premises : Array Expr) := do
    let type ← inferType (mkApp (mkConst equation) body)
    forallBoundedTelescope type (some 4) fun variables _ => do
      let proof := mkAppN (mkConst equation) (#[body] ++ variables ++ #[field] ++ premises)
      return some (lowered, ← mkLambdaFVars variables proof)
  match name, shape.getAppFnArgs with
  | ``CIL.Instruction.ldfld, (``CIL.FieldShape.value, #[offset, width, signed]) =>
    lowering ``step_ldfld_value_eq (mkApp3 (mkConst ``CIL.Instruction.fieldAt) offset width signed)
      #[offset, width, signed, proof]
  | ``CIL.Instruction.ldfld, (``CIL.FieldShape.aggregate, #[offset, size]) =>
    lowering ``step_ldfld_aggregate_eq
      (mkApp2 (mkConst ``CIL.Instruction.aggregateFieldAt) offset size) #[offset, size, proof]
  | ``CIL.Instruction.stfld, (``CIL.FieldShape.value, #[offset, width, signed]) =>
    lowering ``step_stfld_value_eq (mkApp2 (mkConst ``CIL.Instruction.setFieldAt) offset width)
      #[offset, width, signed, proof]
  | ``CIL.Instruction.stfld, (``CIL.FieldShape.aggregate, #[offset, size]) =>
    lowering ``step_stfld_aggregate_eq
      (mkApp2 (mkConst ``CIL.Instruction.setAggregateFieldAt) offset size) #[offset, size, proof]
  | ``CIL.Instruction.ldflda, (``CIL.FieldShape.value, #[offset, _, _])
  | ``CIL.Instruction.ldflda, (``CIL.FieldShape.aggregate, #[offset, _]) =>
    let addressed ← mkCongrArg (mkConst ``CIL.FieldShape.structOffset?) proof
    let resolved := mkApp (mkConst ``CIL.FieldShape.structOffset?)
      (mkApp2 (mkConst ``CIL.Method.fieldShape) body field)
    let placed ← mkAppM ``Option.some #[offset]
    let addressed ← mkExpectedTypeHint addressed (← mkEq resolved placed)
    lowering ``step_ldflda_struct_eq (mkApp (mkConst ``CIL.Instruction.fieldAddress) offset)
      #[offset, addressed]
  | _, _ => return none

open Lean Meta in
/-- The step a class field instruction takes by `equation`, showing the field's owner as the
    operand writes it, so facts stated over that owner still match the stepped goal. -/
def fieldStep (field equation : Expr) : MetaM Simp.Step := do
  let some (_, lhs, stepped) := (← inferType equation).eq? | return .continue
  let_expr CIL.Extraction.FieldRef.mk owner _ _ _ := (← withDefault <| whnf field).consumeMData
    | return .visit { expr := stepped, proof? := some equation }
  let projected := mkApp (mkConst ``CIL.Extraction.FieldRef.owner) field
  let shown := stepped.replace fun term => if term == projected then some owner else none
  let proof ← mkExpectedTypeHint equation (← mkEq lhs shown)
  return .visit { expr := shown, proof? := some proof }

open Lean Meta in
/-- A field load steps by the equation for the field's shape, as `fieldShapeIn` finds it: a
    struct field as the lowered load of its shape, and a class field by the equation for its
    slot and the receiver on the stack. A load whose shape stays unknown steps to `fieldLoad`,
    whose match a later fact can decide. -/
simproc [cil_step] reduceFieldLoad (step _ (.ldfld _) _ _ _ _ _) := fun expression => do
  let_expr CIL.Safety.step body operation pc args frame stack memory := expression
    | return .continue
  let_expr CIL.Instruction.ldfld field := operation | return .continue
  let leading := #[body, pc, args, frame, memory, field]
  let generic := mkAppN (mkConst ``step_ldfld_eq) (leading.push stack)
  let (shape, proof) ← fieldShapeIn body field
  match shape.getAppFnArgs with
  | (``CIL.FieldShape.value, #[offset, width, signed]) =>
    return ← equationStep (mkAppN (mkConst ``step_ldfld_value_eq)
      (leading ++ #[offset, width, signed, proof, stack]))
  | (``CIL.FieldShape.aggregate, #[offset, size]) =>
    return ← equationStep (mkAppN (mkConst ``step_ldfld_aggregate_eq)
      (leading ++ #[offset, size, proof, stack]))
  | _ => pure ()
  let_expr CIL.FieldShape.classSlot offset slot := shape | equationStep generic
  let_expr List.cons _ receiver rest := stack | equationStep generic
  let_expr Value.object reference := receiver | equationStep generic
  let known? ← match (← whnfR slot).getAppFnArgs with
    | (``CIL.ClassSlot.word, #[width, signed]) =>
      let equation? := match ← getNatValue? width with
        | some 1 => some ``step_ldfld_word_1_eq
        | some 2 => some ``step_ldfld_word_2_eq
        | some 4 => some ``step_ldfld_word_4_eq
        | some 8 => some ``step_ldfld_word_8_eq
        | _ => none
      pure (equation?.map fun name =>
        mkAppN (mkConst name) (leading ++ #[offset, signed, proof, reference, rest]))
    | (``CIL.ClassSlot.reference, _) =>
      pure (some (mkAppN (mkConst ``step_ldfld_reference_eq)
        (leading ++ #[offset, proof, reference, rest])))
    | (``CIL.ClassSlot.array, #[element]) =>
      pure (some (mkAppN (mkConst ``step_ldfld_array_eq)
        (leading ++ #[offset, element, proof, reference, rest])))
    | _ => pure none
  match known? with
  | some equation => fieldStep field equation
  | none => equationStep generic

open Lean Meta in
/-- A field store steps by the equation for the field's shape, as `fieldShapeIn` finds it: a
    struct field as the lowered store of its shape, and a class field by the equation for its
    slot and the stored value and receiver on the stack. A store whose shape stays unknown steps
    to `fieldStore`. -/
simproc [cil_step] reduceFieldStore (step _ (.stfld _) _ _ _ _ _) := fun expression => do
  let_expr CIL.Safety.step body operation pc args frame stack memory := expression
    | return .continue
  let_expr CIL.Instruction.stfld field := operation | return .continue
  let leading := #[body, pc, args, frame, memory, field]
  let generic := mkAppN (mkConst ``step_stfld_eq) (leading.push stack)
  let (shape, proof) ← fieldShapeIn body field
  match shape.getAppFnArgs with
  | (``CIL.FieldShape.value, #[offset, width, signed]) =>
    return ← equationStep (mkAppN (mkConst ``step_stfld_value_eq)
      (leading ++ #[offset, width, signed, proof, stack]))
  | (``CIL.FieldShape.aggregate, #[offset, size]) =>
    return ← equationStep (mkAppN (mkConst ``step_stfld_aggregate_eq)
      (leading ++ #[offset, size, proof, stack]))
  | _ => pure ()
  let_expr CIL.FieldShape.classSlot offset slot := shape | equationStep generic
  let_expr List.cons _ stored below := stack | equationStep generic
  let_expr List.cons _ receiver rest := below | equationStep generic
  let_expr Value.object reference := receiver | equationStep generic
  let known? ← match (← whnfR slot).getAppFnArgs, stored.getAppFnArgs with
    | (``CIL.ClassSlot.word, #[width, signed]), (``Value.scalar, #[number]) =>
      let equation? := match ← getNatValue? width, number.getAppFnArgs with
        | some 1, (``CIL.Value.i32, #[bits]) => some (``step_stfld_word_i32_1_eq, bits)
        | some 2, (``CIL.Value.i32, #[bits]) => some (``step_stfld_word_i32_2_eq, bits)
        | some 4, (``CIL.Value.i32, #[bits]) => some (``step_stfld_word_i32_4_eq, bits)
        | some 8, (``CIL.Value.i64, #[bits]) => some (``step_stfld_word_i64_eq, bits)
        | _, _ => none
      pure (equation?.map fun (name, bits) =>
        mkAppN (mkConst name) (leading ++ #[offset, signed, proof, bits, reference, rest]))
    | (``CIL.ClassSlot.reference, _), (``Value.object, #[value]) =>
      pure (some (mkAppN (mkConst ``step_stfld_reference_eq)
        (leading ++ #[offset, proof, value, reference, rest])))
    | (``CIL.ClassSlot.array, #[element]), (``Value.array, #[view]) =>
      pure (some (mkAppN (mkConst ``step_stfld_array_eq)
        (leading ++ #[offset, element, proof, view, reference, rest])))
    | _, _ => pure none
  match known? with
  | some equation => fieldStep field equation
  | none => equationStep generic

open Lean Meta in
/-- A struct field address steps as the lowered address of its offset, and a class field
    address to its fault, as `fieldShapeIn` finds the shape. An address whose shape stays
    unknown steps to `fieldReference`. -/
simproc [cil_step] reduceFieldAddress (step _ (.ldflda _) _ _ _ _ _) := fun expression => do
  let_expr CIL.Safety.step body operation pc args frame stack memory := expression
    | return .continue
  let_expr CIL.Instruction.ldflda field := operation | return .continue
  let leading := #[body, pc, args, frame, memory, field]
  let generic := mkAppN (mkConst ``step_ldflda_eq) (leading.push stack)
  let (shape, proof) ← fieldShapeIn body field
  match shape.getAppFnArgs with
  | (``CIL.FieldShape.value, #[offset, _, _]) | (``CIL.FieldShape.aggregate, #[offset, _]) =>
    -- The offset fact reduces to `some offset` once the shape fact rewrites the resolution.
    let addressed ← mkCongrArg (mkConst ``CIL.FieldShape.structOffset?) proof
    let resolved := mkApp (mkConst ``CIL.FieldShape.structOffset?)
      (mkApp2 (mkConst ``CIL.Method.fieldShape) body field)
    let expected ← mkEq resolved (← mkAppM ``Option.some #[offset])
    let addressed ← mkExpectedTypeHint addressed expected
    return ← equationStep (mkAppN (mkConst ``step_ldflda_struct_eq)
      (leading ++ #[offset, addressed, stack]))
  | _ => pure ()
  let_expr CIL.FieldShape.classSlot offset slot := shape | equationStep generic
  let_expr List.cons _ receiver rest := stack | equationStep generic
  let_expr Value.object reference := receiver | equationStep generic
  equationStep (mkAppN (mkConst ``step_ldflda_class_eq)
    (leading ++ #[offset, slot, proof, reference, rest]))

#print axioms step_ceq_object_eq
#print axioms step_beq_object_eq
#print axioms step_bne_un_object_eq
#print axioms step_cgt_un_object_eq
#print axioms step_brfalse_object_eq
#print axioms step_brtrue_object_eq
#print axioms step_castclass_eq
#print axioms step_isinst_eq
#print axioms step_ldnull_eq
#print axioms step_newarr_i32_eq
#print axioms step_newarr_i64_eq
#print axioms allocateElements_value
#print axioms allocateElements_reference
#print axioms step_stringLiteral_eq
#print axioms step_ldlen_object_eq
#print axioms step_ldlen_object_null_eq
#print axioms step_ldelem_ref_i32_eq
#print axioms step_stelem_ref_i32_eq
#print axioms loadArraySlot_of_access
#print axioms arrayOfSlot_whole
#print axioms storeArraySlot_whole
#print axioms loadSlot_of_access
#print axioms storeSlot_of_access
#print axioms step_ldfld_word_eq
#print axioms step_stfld_word_i64_eq
#print axioms step_stfld_word_i32_eq
#print axioms step_ldfld_reference_eq
#print axioms step_stfld_reference_eq
#print axioms step_ldfld_array_eq
#print axioms step_stfld_array_eq
#print axioms step_ldflda_class_eq
#print axioms step_ldfld_word_1_eq
#print axioms step_ldfld_word_2_eq
#print axioms step_ldfld_word_4_eq
#print axioms step_ldfld_word_8_eq
#print axioms step_stfld_word_i32_1_eq
#print axioms step_stfld_word_i32_2_eq
#print axioms step_stfld_word_i32_4_eq

end CIL.Safety
