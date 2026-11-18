import CIL.Safety.Frames
import CIL.Safety.StackAllocation
import CIL.Safety.ArrayAllocation
import CIL.Safety.StaticMemory
import CIL.Safety.ReferenceObservations
import CIL.Safety.HeapObjects
import CIL.Safety.NativeMethodTables
import CIL.Resolution
import CIL.RuntimeModel
import CIL.Extraction.RuntimeModels

/-!
# Checked interpreter

The interpreter that safety proofs reason about. It runs over allocation-aware memory and
checked values, and it reports why it stopped: every fault is an `ExecutionFault` located at a
method and pc instead of `none`. Value-only instructions are delegated to `CIL.step` through
`pureArity`, so the two interpreters cannot disagree on arithmetic. Locals have only the meaning
given here, through the kinds of their slots. `runModel` runs a runtime model through the same
named functions as the instructions emitted for its call.
-/

namespace CIL.Safety

/-- Whether a value has a well-formed numeric representation; a snapshot must hold
    exactly as many bytes as its shape. -/
def numericValue : CIL.Value → Bool
  | .snapshot shape bytes => bytes.length == shape.width
  | .aggregate _ | .i8 _ | .i32 _ | .i64 _ | .v128 _ | .v128Low64 _ | .v256 _ | .v512 _ => true
  | _ => false

theorem numericValue_snapshotValue (shape : CIL.SnapshotShape) (bytes : List (BitVec 8 × Bool))
    (length : bytes.length = shape.width) : numericValue (snapshotValue shape bytes) = true := by
  unfold snapshotValue
  split
  · cases shape <;> rfl
  · simp [numericValue, length]

theorem loadSnapshot_numeric {m : Memory} {r : ManagedReference} {shape : CIL.SnapshotShape}
    {value : CIL.Value} (h : loadSnapshot m r shape = .ok value) : numericValue value = true := by
  unfold loadSnapshot at h
  cases hr : referenceAt r <;> simp only [hr, Bind.bind, Except.bind] at h
  · cases h
  · rename_i address
    cases hb : checkedAt r shape.width (readSnapshot m address shape.width 1) <;>
      simp only [hb, Pure.pure, Except.pure] at h
    · cases h
    · cases h
      exact numericValue_snapshotValue _ _ (readSnapshot_length (checkedAt_ok hb))

theorem bitcastValue_numeric {source target : CIL.SnapshotShape} {input value : CIL.Value}
    (h : bitcastValue source target input = .ok value) : numericValue value = true := by
  unfold bitcastValue at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i sizes
      split at h
      · rename_i bytes found
        cases h
        apply numericValue_snapshotValue
        have length := valueSnapshot_length found
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at sizes
        exact length.trans sizes
      · cases h

/-- Checks that a value may be pushed: a reference or span base must form in memory and a
    scalar must be numeric. -/
def checkedValue (m : Memory) : Value → ExecutionResult Value
  | .methodPointer pointer => .ok (.methodPointer pointer)
  | .methodTable table => .ok (.methodTable table)
  | .object r => formObject m r
  | .reference r => formValue m r
  | .readOnlyReference r => do
    let _ ← formValue m r
    return .readOnlyReference r
  | .array view => do
    let _ ← checkedAt view.reference 0 (view.validate m)
    return .array view
  | .bufferSpan view => do
    let _ ← checkedAt view.reference 0 (view.validate m)
    return .bufferSpan view
  | .span r length => do
    let _ ← formValue m r
    return .span r length
  | .scalar value => if numericValue value then .ok (.scalar value) else .error .invalidState

/-- Only the value-only instruction whitelist may use the original pure
    arithmetic semantics. No memory/reference operation can enter this path. -/
def pureArity : CIL.Instruction → Option Nat
  | .conv_i1 | .conv_i2 | .conv_u2 => some 1
  | .nop => some 0
  | .neg => some 1
  | .cgt | .bgt _ | .ble _ | .ble_un _ => some 2
  | .conv_i8 | .conv_i4 | .conv_u1 | .conv_u4 | .conv_u8 | .conv_u | .conv_i | .not => some 1
  | .add | .sub | .mul | .and | .or | .xor | .shl | .shr | .shr_un
    | .clt | .clt_un | .cgt_un | .ceq => some 2
  | .brfalse _ | .brtrue _ | .switch _ => some 1
  | .blt_un _ | .bge_un _ | .bgt_un _ | .bge _ | .blt _ | .beq _ | .bne_un _ => some 2
  | .br _ | .feature _ => some 0
  | .intrinsic _ argc => some argc
  -- Faulting arithmetic has its own arms in `step`; `CIL.step` would drop the fault.
  | .div | .div_un | .rem | .rem_un | .add_ovf | .add_ovf_un | .sub_ovf | .sub_ovf_un
    | .mul_ovf | .mul_ovf_un | .conv_ovf _ | .conv_ovf_un _ => none
  | _ => none

/-- The operands of a value-only instruction, all of which must be numeric scalars. -/
def scalars : List Value → ExecutionResult (List CIL.Value)
  | [] => .ok []
  | .scalar value :: rest => do
    if numericValue value then return value :: (← scalars rest) else .error .invalidState
  | _ => .error .invalidState

/-- What a checked step asks the driver to do next. A constructor carries the caller-owned
    temporary it builds into and that temporary's layout. -/
inductive FrameAction where
  | next (pc : Nat) (stack : List Value) (frame : Frame) (memory : Memory)
  | call (callee : Nat) (args rest : List Value) (memory : Memory)
  | tailCall (callee : Nat) (args : List Value) (memory : Memory)
  | construct (callee : Nat) (args rest : List Value) (frame : Frame)
      (temporary : Reference) (kind : CIL.LocalKind) (memory : Memory)
  | returned (result : List Value) (memory : Memory)

/-- How a call-family instruction faults when its method's link table gives its pc no target, or
    a target of another kind than the instruction enters. -/
def unlinkedCall : ExecutionFault := .unsupported "Call site has no program target"

/-- The catalog body an indirect call through `pointer` enters: the entry for the pointer's
    target, when the pointer has the call site's signature; `none` for any other pointer. A
    step proof rewrites this with a fact the kernel checks, so the elaborator never compares the
    identities, whose strings it compares with recursion as deep as they are long. -/
def indirectTarget (signature : CIL.ManagedSignature) (catalog : List CIL.ManagedTarget)
    (pointer : CIL.MethodPointer) : Option Nat :=
  if pointer.signature != signature then none
  else pointer.target.bind fun identity =>
    (catalog.find? (·.identity == identity)).map (·.method)

/-- A selected body is one the catalog lists. -/
theorem indirectTarget_mem {signature : CIL.ManagedSignature} {catalog : List CIL.ManagedTarget}
    {pointer : CIL.MethodPointer} {method : Nat}
    (selected : indirectTarget signature catalog pointer = some method) :
    method ∈ catalog.map CIL.ManagedTarget.method := by
  unfold indirectTarget at selected
  split at selected
  · cases selected
  · cases target : pointer.target with
    | none => simp [target] at selected
    | some identity =>
      simp only [target, Option.bind] at selected
      obtain ⟨entry, found, rfl⟩ := Option.map_eq_some_iff.mp selected
      exact List.mem_map.mpr ⟨entry, List.mem_of_find?_eq_some found, rfl⟩
#print axioms indirectTarget_mem

/-- Managed dispatch checks stable pointer identity and signature before selecting a body from
    the catalog `link`, the call site's entry in its method's link table. Tail calls use the same
    retirement action as direct tail calls. -/
def managedStep (operation : CIL.ManagedOp) (link : Option CIL.Link) (pc : Nat) (frame : Frame)
    (stack : List Value) (memory : Memory) : ExecutionResult FrameAction := do
  match operation, stack with
  | .address target signature, _ =>
    return .next (pc + 1) (.methodPointer ⟨signature, some target.identity⟩ :: stack) frame memory
  | .call signature _ tail, .methodPointer pointer :: values =>
    let some (.indirect catalog) := link | .error unlinkedCall
    let some method := indirectTarget signature catalog pointer | .error .invalidState
    let count := signature.parameters.length
    if (if tail then values.length != count else values.length < count) then
      .error .invalidState else pure ()
    let arguments ← (values.take count).reverse.mapM (checkedValue memory)
    if tail then return .tailCall method arguments memory
    else return .call method arguments (values.drop count) memory
  | _, _ => .error .invalidState

/-- Evaluates an intrinsic. Operands with unspecified bits are allowed only where the
    result does not observe them; arithmetic faults are reported, not swallowed. -/
def checkedIntrinsic (operation : CIL.Intrinsic) (operands : List CIL.Value) : ExecutionResult CIL.Value :=
  if operands.any CIL.Value.hasUnspecified then
    match CIL.evalUnspecifiedIntrinsic operation operands with
    | some value => .ok value
    | none => .error (.unsupported "Intrinsic observes unspecified vector bits")
  else match operation with
  | .scalar (.math kind width signed) =>
    (CIL.evalIntegerMath kind width signed operands).mapError ExecutionFault.arithmetic
  | .scalar (.divRem width signed) =>
    (CIL.evalDivRem width signed operands).mapError ExecutionFault.arithmetic
  | .x86Base .divRem64 => (CIL.X86.divRemValue operands).mapError ExecutionFault.arithmetic
  | _ => match CIL.evalIntrinsic operation operands with
    | some value => .ok value
    | none => .error .invalidState

/-- A narrowed return extends one i32 from a value-returning method; a plain return checks
    the declared arity and validates each returned value. Malformed stacks fault. -/
def returnFrom (narrow : Option CIL.NarrowKind) (returnsValue : Bool) (stack : List Value)
    (memory : Memory) : ExecutionResult FrameAction :=
  match narrow, stack with
  | some kind, [.scalar (.i32 bits)] =>
    if returnsValue then .ok (.returned [.scalar (.i32 (kind.extend bits))] memory)
    else .error .invalidState
  | some _, _ => .error .invalidState
  | none, _ =>
    if stack.length = (if returnsValue then 1 else 0) then do
      return .returned (← stack.mapM (checkedValue memory)) memory
    else .error .invalidState

/-- The value `ldarg index` pushes: a homed argument's frame slot, or the incoming argument
    narrowed as its declared type requires. An incoming value with unspecified vector bits is
    never narrowed. -/
def loadArgument (body : CIL.Method) (index : Nat) (args : List Value) (frame : Frame)
    (memory : Memory) : ExecutionResult Value :=
  match body.argumentAccess index with
  | .home slot => do
    let some home := frame.locals[slot]? | .error .invalidState
    loadLocal memory home
  | .value none => do
    let some value := args[index]? | .error .invalidState
    checkedValue memory value
  | .value (some kind) => do
    let some value := args[index]? | .error .invalidState
    if value.hasUnspecified then
      .error (.unsupported "Instruction observes unspecified vector bits") else
    let .scalar (.i32 bits) := value | .error .invalidState
    checkedValue memory (.scalar (.i32 (kind.extend bits)))

/-- The frame and memory after `starg index` stores `value`: a homed argument's frame slot is
    written as `stloc` of that slot writes it. An argument without a home has no slot to write. -/
def storeArgument (body : CIL.Method) (index : Nat) (value : Value) (frame : Frame)
    (memory : Memory) : ExecutionResult (Frame × Memory) :=
  match body.argumentAccess index with
  | .home slot => do
    let some home := frame.locals[slot]? | .error .invalidState
    let (home, memory) ← storeLocal memory home value
    return ({ frame with locals := frame.locals.set slot home }, memory)
  | .value _ => .error (.unsupported "Store to an argument without a home")

/-- The address `ldarga index` pushes: a homed argument's frame slot, as `ldloca` of that slot
    takes it. An argument without a home has no address. -/
def addressArgument (body : CIL.Method) (index : Nat) (frame : Frame) (memory : Memory) :
    ExecutionResult Value :=
  match body.argumentAccess index with
  | .home slot => do
    let some home := frame.locals[slot]? | .error .invalidState
    localAddress memory home
  | .value _ => .error (.unsupported "Address of an argument without a home")

/-- Runs `next` unless one of the top `count` operands has unspecified bits, which `step` rejects
    with the same fault before every instruction. -/
def observedCall (count : Nat) (stack : List Value) (next : Unit → ExecutionResult FrameAction) :
    ExecutionResult FrameAction :=
  if unspecifiedOperands count stack then
    .error (.unsupported "Instruction observes unspecified vector bits") else next ()

/-- An intrinsic must be available in `profile`; its `argc` operands are taken deepest first. -/
def intrinsicCall (profile : CIL.FeatureProfile) (operation : CIL.Intrinsic) (argc pc : Nat)
    (frame : Frame) (stack : List Value) (memory : Memory) : ExecutionResult FrameAction :=
  if !operation.available profile then
    .error (.unsupported "Intrinsic unavailable in target profile")
  else if stack.length < argc then .error .invalidState else do
    let operands ← scalars (stack.take argc).reverse
    let value ← checkedIntrinsic operation operands
    return .next (pc + 1) ((← checkedValue memory (.scalar value)) :: stack.drop argc) frame memory

/-- A feature test pushes 1 when `profile` has `feature`, and 0 otherwise. -/
def featureCall (profile : CIL.FeatureProfile) (feature : CIL.Feature) (pc : Nat) (frame : Frame)
    (stack : List Value) (memory : Memory) : ExecutionResult FrameAction :=
  .ok (.next (pc + 1) (.scalar (.i32 (if profile.evaluate feature then 1 else 0)) :: stack) frame
    memory)

/-- A reference comparison pushes 1 when the two references, deepest first, stand in
    `relation`, and 0 otherwise; a readonly reference compares as its address. -/
def referenceCompareCall (relation : CIL.ReferenceRelation) (pc : Nat) (frame : Frame)
    (stack : List Value) (memory : Memory) : ExecutionResult FrameAction := do
  match stack with
  | .reference right :: .reference left :: rest
  | .reference right :: .readOnlyReference left :: rest
  | .readOnlyReference right :: .reference left :: rest
  | .readOnlyReference right :: .readOnlyReference left :: rest =>
    let holds ← match relation with
      | .same => referenceEqual memory left right
      | .less => referenceLess memory left right
      | .greater => referenceLess memory right left
    return .next (pc + 1) (.scalar (.i32 (if holds then 1 else 0)) :: rest) frame memory
  | _ => .error .invalidState

/-- A reference below a byte offset moves back by that offset and keeps its readonly
    restriction. -/
def referenceSubtractCall (pc : Nat) (frame : Frame) (stack : List Value) (memory : Memory) :
    ExecutionResult FrameAction := do
  match stack with
  | .scalar offset :: .reference value :: rest =>
    let result ← referenceSubtract memory value offset
    return .next (pc + 1) (.reference result :: rest) frame memory
  | .scalar offset :: .readOnlyReference value :: rest =>
    let result ← referenceSubtract memory value offset
    return .next (pc + 1) (.readOnlyReference result :: rest) frame memory
  | _ => .error .invalidState

/-- The typed load or store an unaligned transfer of `kind` performs. -/
def typedTransferInstruction : CIL.TransferKind → Bool → CIL.Instruction
  | .scalar width signed, false => .loadScalar width signed
  | .scalar width _, true => .storeScalar width
  | .snapshot (.aggregate size), false => .loadAggregate size
  | .snapshot (.aggregate size), true => .storeAggregate size
  | .snapshot .vector128, false => .memory .load128
  | .snapshot .vector128, true => .memory .store128
  | .snapshot .vector256, false => .memory .load256
  | .snapshot .vector256, true => .memory .store256
  | .snapshot .vector512, false => .memory .load512
  | .snapshot .vector512, true => .memory .store512

/-- An unaligned transfer of `kind` runs as its typed load or store. -/
def typedTransferCall (kind : CIL.TransferKind) (store : Bool) (pc : Nat) (frame : Frame)
    (stack : List Value) (memory : Memory) : ExecutionResult FrameAction := do
  let (memory, values) ← instruction (typedTransferInstruction kind store) stack memory
  return .next (pc + 1) values frame memory

/-- `Unsafe.SkipInit` pops its out reference once it forms; nothing is written. Any other operand
    faults as the `skipInit` instruction does. -/
def skipInitCall (pc : Nat) (frame : Frame) (stack : List Value) (memory : Memory) :
    ExecutionResult FrameAction := do
  match stack with
  | .reference reference :: rest =>
    let _ ← formValue memory reference
    return .next (pc + 1) rest frame memory
  | _ => .error (.unsupported "Not a memory instruction")

/-- Executes `model` as the call at `pc` of `body`. The caller applies `observedCall` with
    `model.observerCount` first. On the stacks a model admits this equals `step` on the
    instruction emitted for the call, and it refuses every other stack. -/
def runModel (body : CIL.Method) (model : CIL.RuntimeModel) (pc : Nat) (frame : Frame)
    (stack : List Value) (memory : Memory) : ExecutionResult FrameAction :=
  match model with
  | .intrinsic operation argc => intrinsicCall body.profile operation argc pc frame stack memory
  | .memory operation => do
    let (memory, values) ← memoryInstruction operation stack memory
    return .next (pc + 1) values frame memory
  | .feature feature => featureCall body.profile feature pc frame stack memory
  | .constant value => .ok (.next (pc + 1) (.scalar (.i32 value) :: stack) frame memory)
  | .referenceCompare relation => referenceCompareCall relation pc frame stack memory
  | .referenceSubtract => referenceSubtractCall pc frame stack memory
  | .typedTransfer kind store => typedTransferCall kind store pc frame stack memory
  | .skipInit => skipInitCall pc frame stack memory
  | .objectConstructor => match stack with
    | _ :: rest => .ok (.next (pc + 1) rest frame memory)
    | [] => .error (.unsupported "Not a memory instruction")

/-- A call whose pc states no link runs `model`, the runtime model its method stands for, after
    checking the operands the model observes; without one it faults with `unlinkedCall`. -/
def modelStep (model : Option CIL.RuntimeModel) (body : CIL.Method) (pc : Nat) (frame : Frame)
    (stack : List Value) (memory : Memory) : ExecutionResult FrameAction :=
  match model with
  | some model =>
    observedCall model.observerCount stack fun _ => runModel body model pc frame stack memory
  | none => .error unlinkedCall

/-- A call's runtime model only ever continues at the next pc in the same frame. -/
theorem modelStep_next {model : Option CIL.RuntimeModel} {body : CIL.Method} {pc : Nat}
    {frame : Frame} {stack : List Value} {memory : Memory} {action : FrameAction}
    (executed : modelStep model body pc frame stack memory = .ok action) :
    ∃ values final, action = .next (pc + 1) values frame final := by
  unfold modelStep observedCall runModel intrinsicCall featureCall referenceCompareCall
    referenceSubtractCall typedTransferCall skipInitCall at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first
    | exact ⟨_, _, (Except.ok.inj executed).symm⟩
    | cases executed
    | split at executed

/-- A call's runtime model reads its body only through the profile. -/
theorem modelStep_profile_congr {moved body : CIL.Method} (profile : moved.profile = body.profile)
    (model : Option CIL.RuntimeModel) (pc : Nat) (frame : Frame) (stack : List Value)
    (memory : Memory) :
    modelStep model moved pc frame stack memory = modelStep model body pc frame stack memory := by
  simp only [modelStep, runModel, profile]

#print axioms modelStep_profile_congr

/-- `ldfld` of `field` as `body` resolves it: a class slot through the receiver, or a struct
    field at its checked offset and width through a reference or out of a struct value. A field
    outside the checked layouts and class slots faults with its reason. -/
def fieldLoad (body : CIL.Method) (field : CIL.Extraction.FieldRef) (stack : List Value)
    (memory : Memory) : ExecutionResult (Memory × List Value) :=
  match body.fieldShape field with
  | .classSlot offset slot => classFieldLoad field.owner offset slot stack memory
  | .value offset width signed => instruction (.fieldAt offset width signed) stack memory
  | .aggregate offset size => instruction (.aggregateFieldAt offset size) stack memory
  | .unsupported reason => .error (.unsupported reason)

/-- `stfld` of `field` as `body` resolves it: a class slot through the receiver, or a struct
    field at its checked offset and width through a writable reference; faults as `fieldLoad`. -/
def fieldStore (body : CIL.Method) (field : CIL.Extraction.FieldRef) (stack : List Value)
    (memory : Memory) : ExecutionResult (Memory × List Value) :=
  match body.fieldShape field with
  | .classSlot offset slot => classFieldStore field.owner offset slot stack memory
  | .value offset width _ => instruction (.setFieldAt offset width) stack memory
  | .aggregate offset size => instruction (.setAggregateFieldAt offset size) stack memory
  | .unsupported reason => .error (.unsupported reason)

/-- `ldflda` of `field` as `body` resolves it: the address of a struct field at its checked
    offset, read-only through a read-only reference. A class field's address is never formed; the
    extractor refuses one at admission, so only a hand-written body steps one. -/
def fieldReference (body : CIL.Method) (field : CIL.Extraction.FieldRef) (stack : List Value)
    (memory : Memory) : ExecutionResult (Memory × List Value) :=
  match body.fieldShape field with
  | .value offset .. | .aggregate offset _ => instruction (.fieldAddress offset) stack memory
  | .classSlot .. => .error (.unsupported "Class field address")
  | .unsupported reason => .error (.unsupported reason)

/-- `localloc` of the byte count alone on the stack: fresh storage owned by `frame`, zeroed when
    `initLocals` is set. Any other stack is an invalid state. -/
def localAllocation (initLocals : Bool) (pc : Nat) (frame : Frame) (stack : List Value)
    (memory : Memory) : ExecutionResult FrameAction := do
  let [.scalar size] := stack | .error .invalidState
  let bytes ← match size with
    | .i32 bits => pure bits.toNat
    | .i64 bits => pure bits.toNat
    | _ => .error .invalidState
  let (reference, owner, memory) ← allocateStack memory frame bytes initLocals
  return .next (pc + 1) [.reference reference] owner memory

/-- `newarr` of `length` elements of `shape`: an inline value array or an array of null class
    references; a method-table or unsupported shape allocates nothing. -/
def allocateElements (shape : ElementShape) (length : CIL.Value) (memory : Memory) :
    ExecutionResult (Value × Memory) := do
  match shape with
  | .value element =>
    let (view, memory) ← newArray memory element length
    return (.array view, memory)
  | .reference element =>
    let (array, memory) ← newReferenceArray memory element length
    return (.object (.address array), memory)
  | .method _ => .error (.unsupported ElementShape.methodAllocation)
  | .unsupported reason => .error (.unsupported reason)

/-- `newobj` of a value type: a zeroed temporary of `size` bytes owned by `frame`, passed by
    address to `callee` ahead of the `argc` arguments on the stack; the driver pushes the
    temporary's value once the constructor returns. -/
def constructAggregate (callee argc : Nat) (size : Fin (2^64)) (frame : Frame)
    (stack : List Value) (m : Memory) : ExecutionResult FrameAction := do
  if size = 0 || stack.length < argc then .error .invalidState else
    let arguments ← (stack.take argc).reverse.mapM (checkedValue m)
    let (temporary, memory) ← allocateHome m frame.activation size
    let (_, memory) ← storeLocal memory (.bytes (.aggregate size) temporary)
      (.scalar (.aggregate (List.replicate size 0)))
    let frame := { frame with owned := temporary.allocation :: frame.owned }
    return .construct callee (.reference (.address temporary) :: arguments)
      (stack.drop argc) frame temporary (.aggregate size) memory

/-- `newobj` of a class: a fresh zeroed instance of `type` with `size` bytes of fields, passed
    to `constructor` as its receiver ahead of the `argc` arguments on the stack, and left on the
    caller's stack for when the constructor returns. -/
def constructObject (constructor argc : Nat) (type : RuntimeType) (size : Nat)
    (stack : List Value) (m : Memory) : ExecutionResult FrameAction := do
  if stack.length < argc then .error .invalidState else
    let arguments ← (stack.take argc).reverse.mapM (checkedValue m)
    let (object, memory) ← allocateObject m type size
    let created := Value.object (.address object)
    return .call constructor (created :: arguments) (created :: stack.drop argc) memory

/-- `newobj` of a constructor of `owner` taking `argc` arguments, as its `link` states: a
    value-type temporary for `.aggregate`, a class instance with the link's bases for
    `.object`. Any other link, or none, faults with `unlinkedCall`. -/
def newobjStep (link : Option CIL.Link) (owner : CIL.Extraction.TypeExpr) (argc : Nat)
    (frame : Frame) (stack : List Value) (m : Memory) : ExecutionResult FrameAction :=
  match link with
  | some (.aggregate callee size) => constructAggregate callee argc size frame stack m
  | some (.object constructor bases size) =>
    constructObject constructor argc ⟨owner, bases⟩ size stack m
  | _ => .error unlinkedCall

/-- Executes one instruction of `body`. Instructions that would observe unspecified vector
    bits are rejected before dispatch, and a call in the arm of its link. -/
def step (body : CIL.Method) (op : CIL.Instruction) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) : ExecutionResult FrameAction := do
  if unspecifiedOperands (observerCount op) stack then
    .error (.unsupported "Instruction observes unspecified vector bits") else
  -- Native table offsets, faulting arithmetic, object identity, type tests, instance fields,
  -- argument homes, `localloc`, `newarr` and `newobj` are matched apart, so neither match exceeds
  -- the 79 alternatives `split` handles.
  match op, stack with
  -- A native table offset is a byte count; the cursor keeps the table's identities.
  | .add, .scalar offset :: .methodTable table :: rest
  | .add, .methodTable table :: .scalar offset :: rest =>
    let offset ← match offset with
      | .i32 bits => .ok (bits.signExtend 64)
      | .i64 bits => .ok bits
      | _ => .error .invalidState
    let selected ← checkedAt .null nativeMethodWidth (addNativeTable table m offset)
    return .next (pc + 1) (.methodTable selected :: rest) frame m
  -- One arm per overflow-checked arithmetic constructor, flags as `checkedKind?` gives them.
  | .add_ovf, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.checkedValues .add true x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .add_ovf_un, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.checkedValues .add false x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .sub_ovf, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.checkedValues .sub true x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .sub_ovf_un, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.checkedValues .sub false x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .mul_ovf, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.checkedValues .mul true x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .mul_ovf_un, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.checkedValues .mul false x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  -- One arm per division constructor, flags as `divideKind?` gives them.
  | .div, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.divideValues true false x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .div_un, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.divideValues false false x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .rem, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.divideValues true true x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .rem_un, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.divideValues false true x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  -- Overflow-checked conversions, reading the operand as signed or as unsigned.
  | .conv_ovf target, .scalar x :: rest =>
    let value ← (CIL.convertInteger target.width target.signed false x).mapError
      ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .conv_ovf_un target, .scalar x :: rest =>
    let value ← (CIL.convertInteger target.width target.signed true x).mapError
      ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  -- Object identity and null tests; `x != null` compiles to `cgt.un` against null.
  | .ceq, .object right :: .object left :: rest =>
    let equal ← objectEqual m left right
    return .next (pc + 1) (.scalar (.i32 (if equal then 1 else 0)) :: rest) frame m
  | .beq target, .object right :: .object left :: rest =>
    let equal ← objectEqual m left right
    return .next (if equal then target else pc + 1) rest frame m
  | .bne_un target, .object right :: .object left :: rest =>
    let equal ← objectEqual m left right
    return .next (if equal then pc + 1 else target) rest frame m
  | .cgt_un, .object right :: .object left :: rest =>
    let present ← objectAboveNull m left right
    return .next (pc + 1) (.scalar (.i32 (if present then 1 else 0)) :: rest) frame m
  | .brfalse target, .object value :: rest =>
    let present ← objectNonNull m value
    return .next (if present then pc + 1 else target) rest frame m
  | .brtrue target, .object value :: rest =>
    let present ← objectNonNull m value
    return .next (if present then target else pc + 1) rest frame m
  -- Class type tests: null and an instance of `type` pass; another object fails the test.
  | .castclass type, .object value :: rest =>
    let result ← objectTest m type true value
    return .next (pc + 1) (.object result :: rest) frame m
  | .isinst type, .object value :: rest =>
    let result ← objectTest m type false value
    return .next (pc + 1) (.object result :: rest) frame m
  -- Instance fields, as the body's layout environment resolves them.
  | .ldfld field, _ =>
    let (memory, stack) ← fieldLoad body field stack m
    return .next (pc + 1) stack frame memory
  | .ldflda field, _ =>
    let (memory, stack) ← fieldReference body field stack m
    return .next (pc + 1) stack frame memory
  | .stfld field, _ =>
    let (memory, stack) ← fieldStore body field stack m
    return .next (pc + 1) stack frame memory
  -- An argument's home is written and addressed as the local slot it is.
  | .starg index, value :: rest =>
    let (frame, memory) ← storeArgument body index value frame m
    return .next (pc + 1) rest frame memory
  | .ldarga index, _ =>
    return .next (pc + 1) ((← addressArgument body index frame m) :: stack) frame m

  -- Dynamic frame storage, zeroed as the body's declared localsinit flag says.
  | .localloc, _ => localAllocation body.declared.initLocals pc frame stack m
  -- Static fields resolve the descriptor extraction bound to their pc.
  | .ldsfld _, _ =>
    let (memory, value) ← staticLoad body pc m
    return .next (pc + 1) (value :: stack) frame memory
  | .ldsflda _, _ | .ldtoken (.field _), _ =>
    let (memory, value) ← staticAddress body pc m
    return .next (pc + 1) (value :: stack) frame memory
  | .stsfld _, _ => .error (.unsupported "Static field store")
  -- A fresh array of the storage the layouts give its declared element type.
  | .newarr element, .scalar length :: rest =>
    let (array, memory) ← allocateElements (body.elementShape element) length m
    return .next (pc + 1) (array :: rest) frame memory
  -- Typed element accesses take the storage the layouts give their declared element type.
  | .ldelem_any element, _ =>
    let (memory, values) ← typedElementInstruction (body.elementShape element) false stack m
    return .next (pc + 1) values frame memory
  | .stelem_any element, _ =>
    let (memory, values) ← typedElementInstruction (body.elementShape element) true stack m
    return .next (pc + 1) values frame memory
  | .ldelema element readOnly, _ =>
    let (memory, values) ← elementAddressInstruction (body.elementShape element) readOnly stack m
    return .next (pc + 1) values frame memory
  -- A call enters the body its pc links to once its method's arguments are specified; a pc with
  -- no link runs the runtime model its operand names, which checks the operands it observes and
  -- leaves no frame for a `tail.` call to retire.
  | .call method prefixes, _ =>
    match body.linkAt pc with
    | none =>
      if prefixes.tail then .error unlinkedCall else
        modelStep (CIL.Extraction.runtimeModel body.environment .call method) body pc frame stack m
    | some link => observedCall method.argumentCount stack fun _ => do
      match link with
      | .direct callee =>
        if prefixes.tail then
          if stack.length != method.argumentCount then .error .invalidState else
            return .tailCall callee (← stack.reverse.mapM (checkedValue m)) m
        else if stack.length < method.argumentCount then .error .invalidState else
          let arguments ← (stack.take method.argumentCount).reverse.mapM (checkedValue m)
          return .call callee arguments (stack.drop method.argumentCount) m
      | _ => .error unlinkedCall
  -- A construction allocates what the link at its pc states and enters the constructor it names.
  | .newobj constructor, _ =>
    newobjStep (body.linkAt pc) constructor.owner constructor.parameters.length frame stack m
  -- A hole faults on every stack.
  | .unadmitted _, _ => .error (.unsupported "Opcode not admitted")
  | _, _ =>
  match op, stack with
  | .managed operation, _ => managedStep operation (body.linkAt pc) pc frame stack m
  | .add, .scalar _ :: .reference _ :: _
  | .add, .reference _ :: .scalar _ :: _
  | .add, .scalar _ :: .readOnlyReference _ :: _
  | .add, .readOnlyReference _ :: .scalar _ :: _ =>
    let (memory, values) ← referenceAddInstruction 1 true stack m
    return .next (pc + 1) values frame memory
  | .sub, .scalar _ :: .reference _ :: _
  | .sub, .scalar _ :: .readOnlyReference _ :: _ => referenceSubtractCall pc frame stack m
  | .sub, .reference right :: .reference left :: rest
  | .sub, .reference right :: .readOnlyReference left :: rest
  | .sub, .readOnlyReference right :: .reference left :: rest
  | .sub, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let result ← referenceDifference m left right
    return .next (pc + 1) (.scalar (.i64 result) :: rest) frame m
  | .clt_un, .reference _ :: .reference _ :: _
  | .clt_un, .reference _ :: .readOnlyReference _ :: _
  | .clt_un, .readOnlyReference _ :: .reference _ :: _
  | .clt_un, .readOnlyReference _ :: .readOnlyReference _ :: _ =>
    referenceCompareCall .less pc frame stack m
  | .cgt_un, .reference _ :: .reference _ :: _
  | .cgt_un, .reference _ :: .readOnlyReference _ :: _
  | .cgt_un, .readOnlyReference _ :: .reference _ :: _
  | .cgt_un, .readOnlyReference _ :: .readOnlyReference _ :: _ =>
    referenceCompareCall .greater pc frame stack m
  | .blt_un target, .reference right :: .reference left :: rest
  | .blt_un target, .reference right :: .readOnlyReference left :: rest
  | .blt_un target, .readOnlyReference right :: .reference left :: rest
  | .blt_un target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let less ← referenceLess m left right
    return .next (if less then target else pc + 1) rest frame m
  | .bge_un target, .reference right :: .reference left :: rest
  | .bge_un target, .reference right :: .readOnlyReference left :: rest
  | .bge_un target, .readOnlyReference right :: .reference left :: rest
  | .bge_un target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let less ← referenceLess m left right
    return .next (if less then pc + 1 else target) rest frame m
  | .bgt_un target, .reference right :: .reference left :: rest
  | .bgt_un target, .reference right :: .readOnlyReference left :: rest
  | .bgt_un target, .readOnlyReference right :: .reference left :: rest
  | .bgt_un target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let less ← referenceLess m right left
    return .next (if less then target else pc + 1) rest frame m
  | .ble_un target, .reference right :: .reference left :: rest
  | .ble_un target, .reference right :: .readOnlyReference left :: rest
  | .ble_un target, .readOnlyReference right :: .reference left :: rest
  | .ble_un target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let less ← referenceLess m right left
    return .next (if less then pc + 1 else target) rest frame m
  -- Reference observations preserve memory and do not grant byte access authority.
  | .brfalse target, .reference value :: rest
  | .brfalse target, .readOnlyReference value :: rest =>
    let present ← referenceNonNull m value
    return .next (if present then pc + 1 else target) rest frame m
  | .brtrue target, .reference value :: rest
  | .brtrue target, .readOnlyReference value :: rest =>
    let present ← referenceNonNull m value
    return .next (if present then target else pc + 1) rest frame m
  | .ceq, .reference _ :: .reference _ :: _
  | .ceq, .reference _ :: .readOnlyReference _ :: _
  | .ceq, .readOnlyReference _ :: .reference _ :: _
  | .ceq, .readOnlyReference _ :: .readOnlyReference _ :: _ =>
    referenceCompareCall .same pc frame stack m
  | .beq target, .reference right :: .reference left :: rest
  | .beq target, .reference right :: .readOnlyReference left :: rest
  | .beq target, .readOnlyReference right :: .reference left :: rest
  | .beq target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let equal ← referenceEqual m left right
    return .next (if equal then target else pc + 1) rest frame m
  | .bne_un target, .reference right :: .reference left :: rest
  | .bne_un target, .reference right :: .readOnlyReference left :: rest
  | .bne_un target, .readOnlyReference right :: .reference left :: rest
  | .bne_un target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let equal ← referenceEqual m left right
    return .next (if equal then pc + 1 else target) rest frame m
  | .intrinsic operation argc, _ => intrinsicCall body.profile operation argc pc frame stack m
  | .ldarg index, _ =>
    return .next (pc + 1) ((← loadArgument body index args frame m) :: stack) frame m
  | .ldloc i, _ =>
    let some slot := frame.locals[i]? | .error .invalidState
    return .next (pc + 1) ((← loadLocal m slot) :: stack) frame m
  | .ldloca i, _ =>
    let some slot := frame.locals[i]? | .error .invalidState
    return .next (pc + 1) ((← localAddress m slot) :: stack) frame m
  | .stloc i, value :: rest =>
    let some slot := frame.locals[i]? | .error .invalidState
    let (slot, memory) ← storeLocal m slot value
    return .next (pc + 1) rest { frame with locals := frame.locals.set i slot } memory
  | .initializeSpanLocal index constructor, _ =>
    let some slot := frame.locals[index]? | .error .invalidState
    let (memory, values) ← memoryInstruction constructor.operation stack m
    let value :: rest := values | .error .invalidState
    let (slot, memory) ← storeLocal memory slot value
    return .next (pc + 1) rest { frame with locals := frame.locals.set index slot } memory
  -- Each receiver call and construction reads the method it enters from the link of its pc.
  | .callInstance _ argc, _ =>
    let some (.direct callee) := body.linkAt pc | .error unlinkedCall
    if stack.length < argc then .error .invalidState else
      let arguments ← (stack.take argc).reverse.mapM (checkedValue m)
      -- The receiver is the deepest argument; anything but an object reference is ill-typed.
      match arguments with
      | .object (.address _) :: _ => return .call callee arguments (stack.drop argc) m
      | .object .null :: _ => .error (.thrown .nullReference)
      | _ => .error .invalidState
  | .callVirtual _ argc, _ =>
    let some (.virtual targets) := body.linkAt pc | .error unlinkedCall
    if stack.length < argc then .error .invalidState else
      let arguments ← (stack.take argc).reverse.mapM (checkedValue m)
      match arguments with
      | .object (.address receiver) :: _ =>
        return .call (← virtualTarget m targets receiver) arguments (stack.drop argc) m
      | .object .null :: _ => .error (.thrown .nullReference)
      | _ => .error .invalidState
  | .memory operation, _ =>
    let (memory, values) ← staticInstruction body pc operation stack m
    return .next (pc + 1) values frame memory
  | .throw exception, _ => .error (.thrown exception)
  | .ret, _ => returnFrom body.returnNarrow body.returnsValue stack m
  | _, _ =>
    match pureArity op with
    | some argc =>
      if stack.length < argc then .error .invalidState else
        let values ← scalars (stack.take argc)
        let some (.next target result _) :=
          CIL.step op false none pc values (fun _ => none) body.profile
            | .error .invalidState
        let result ← (result.map Value.scalar).mapM (checkedValue m)
        return .next target (result ++ stack.drop argc) frame m
    | none =>
      let (memory, values) ← instruction op stack m
      return .next (pc + 1) values frame memory

/-- Every executed instruction goes through the checked dispatcher. Fuel has
    the same recursive call structure as the original interpreter. Constructor
    storage belongs to its caller, so expiration of the constructor's private
    frame does not destroy the value being constructed. Static instructions use
    extraction-bound field identities and readonly allocation storage. -/
def run (program : CIL.Program) : Nat → Nat → Nat → List Value → Frame →
    List Value → Memory → Except LocatedFault (Memory × List Value)
  | 0, method, pc, _, _, _, _ => .error ⟨method, pc, .fuelExhausted⟩
  | fuel + 1, method, pc, args, frame, stack, memory => do
    let some body := program[method]? | .error ⟨method, pc, .invalidState⟩
    let some op := body.code[pc]? | .error ⟨method, pc, .invalidState⟩
    let action ← (step body op pc args frame stack memory).mapError fun fault => ⟨method, pc, fault⟩
    match action with
    | .next target stack frame memory => run program fuel method target args frame stack memory
    | .call callee arguments rest memory =>
      let some child := program[callee]? | .error ⟨method, pc, .invalidState⟩
      let (childFrame, memory) ← (enterFrame child arguments memory).mapError fun fault => ⟨method, pc, fault⟩
      let (memory, result) ← run program fuel callee 0 arguments childFrame [] memory
      run program fuel method (pc + 1) args frame (result ++ rest) memory
    | .tailCall callee arguments memory =>
      let some child := program[callee]? | .error ⟨method, pc, .invalidState⟩
      if child.returnsValue != body.returnsValue then .error ⟨method, pc, .invalidState⟩ else
        let memory := leaveFrame frame memory
        let arguments ← (arguments.mapM (checkedValue memory)).mapError
          fun fault => ⟨method, pc, fault⟩
        let (childFrame, memory) ← (enterFrame child arguments memory).mapError
          fun fault => ⟨method, pc, fault⟩
        run program fuel callee 0 arguments childFrame [] memory
    | .construct callee arguments rest frame temporary kind memory =>
      let some child := program[callee]? | .error ⟨method, pc, .invalidState⟩
      let (childFrame, memory) ← (enterFrame child arguments memory).mapError fun fault => ⟨method, pc, fault⟩
      let (memory, result) ← run program fuel callee 0 arguments childFrame [] memory
      if !result.isEmpty then .error ⟨method, pc, .invalidState⟩ else
        let value ← (loadLocal memory (.bytes kind temporary)).mapError
          fun fault => ⟨method, pc, fault⟩
        run program fuel method (pc + 1) args frame (value :: rest) memory
    | .returned result memory =>
      let memory := leaveFrame frame memory
      let result ← (result.mapM (checkedValue memory)).mapError fun fault => ⟨method, pc, fault⟩
      return (memory, result)

/-- Calls `method` with checked `args` in a fresh frame. -/
def invoke (program : CIL.Program) (fuel method : Nat) (args : List Value) (m : Memory) :
    Except LocatedFault (Memory × List Value) := do
  let some body := program[method]? | .error ⟨method, 0, .invalidState⟩
  let args ← (args.mapM (checkedValue m)).mapError fun fault => ⟨method, 0, fault⟩
  let (frame, memory) ← (enterFrame body args m).mapError fun fault => ⟨method, 0, fault⟩
  run program fuel method 0 args frame [] memory

/-- Consumer macros name the dispatchers' `eq_def`, which a quotation cannot generate itself. -/
private theorem dispatch_eq_def_generated : True := by
  have := @CIL.step.eq_def
  have := @step.eq_def
  trivial

end CIL.Safety
