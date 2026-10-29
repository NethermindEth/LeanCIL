import CIL.Safety.Frames
import CIL.Safety.StackAllocation
import CIL.Safety.StaticMemory
import CIL.Safety.ReferenceObservations
import CIL.NativeEvaluation

/-!
# Checked interpreter

The interpreter that safety proofs reason about. It runs the same instructions as
`CIL.step`, but over allocation-aware memory and checked values, and it reports why it
stopped: every fault is an `ExecutionFault` located at a method and pc instead of `none`.
Value-only instructions are delegated to `CIL.step` through `pureArity`, so the two
interpreters cannot disagree on arithmetic.
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
def pureArity : CIL.Op → Option Nat
  | .convI1 | .convI2 | .convU2 => some 1
  | .nop => some 0
  | .neg => some 1
  | .gt | .bgt _ | .ble _ | .bleu _ => some 2
  | .convI8 | .convI4 | .convU1 | .convU4 | .convU8 | .convU | .bnot => some 1
  | .add | .sub | .mul | .band | .bor | .bxor | .shl | .shr | .shrUn
    | .lt | .ltu | .gtu | .eq => some 2
  | .brzero _ | .brnonzero _ | .switch _ => some 1
  | .bltu _ | .bgeu _ | .bgtu _ | .bge _ | .blt _ | .beq _ | .bne _ => some 2
  | .branch _ | .feature _ => some 0
  | .intrinsic _ argc => some argc
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
  | construct (callee : Nat) (args rest : List Value) (frame : Frame)
      (temporary : Reference) (kind : CIL.LocalKind) (memory : Memory)
  | returned (result : List Value) (memory : Memory)

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
  | .x86Base .divRem64 => (CIL.X86.divRemValue operands).mapError ExecutionFault.arithmetic
  | _ => match CIL.evalIntrinsic operation operands with
    | some value => .ok value
    | none => .error .invalidState

/-- Executes one instruction of `body`. Instructions that would observe unspecified vector
    bits are rejected before dispatch. -/
def step (body : CIL.Method) (op : CIL.Op) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) : ExecutionResult FrameAction := do
  let unknownArgument := match op with
    | .arg index (some _) => (args[index]?.map Value.hasUnspecified).getD false
    | _ => false
  if unspecifiedOperands (observerCount op) stack || unknownArgument then
    .error (.unsupported "Instruction observes unspecified vector bits") else
  match op, stack with
  | .sub, .scalar offset :: .reference value :: rest =>
    let result ← referenceSubtract m value offset
    return .next (pc + 1) (.reference result :: rest) frame m
  | .sub, .scalar offset :: .readOnlyReference value :: rest =>
    let result ← referenceSubtract m value offset
    return .next (pc + 1) (.readOnlyReference result :: rest) frame m
  | .sub, .reference right :: .reference left :: rest
  | .sub, .reference right :: .readOnlyReference left :: rest
  | .sub, .readOnlyReference right :: .reference left :: rest
  | .sub, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let result ← referenceDifference m left right
    return .next (pc + 1) (.scalar (.i64 result) :: rest) frame m
  | .ltu, .reference right :: .reference left :: rest
  | .ltu, .reference right :: .readOnlyReference left :: rest
  | .ltu, .readOnlyReference right :: .reference left :: rest
  | .ltu, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let less ← referenceLess m left right
    return .next (pc + 1) (.scalar (.i32 (if less then 1 else 0)) :: rest) frame m
  | .gtu, .reference right :: .reference left :: rest
  | .gtu, .reference right :: .readOnlyReference left :: rest
  | .gtu, .readOnlyReference right :: .reference left :: rest
  | .gtu, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let less ← referenceLess m right left
    return .next (pc + 1) (.scalar (.i32 (if less then 1 else 0)) :: rest) frame m
  | .bltu target, .reference right :: .reference left :: rest
  | .bltu target, .reference right :: .readOnlyReference left :: rest
  | .bltu target, .readOnlyReference right :: .reference left :: rest
  | .bltu target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let less ← referenceLess m left right
    return .next (if less then target else pc + 1) rest frame m
  | .bgeu target, .reference right :: .reference left :: rest
  | .bgeu target, .reference right :: .readOnlyReference left :: rest
  | .bgeu target, .readOnlyReference right :: .reference left :: rest
  | .bgeu target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let less ← referenceLess m left right
    return .next (if less then pc + 1 else target) rest frame m
  | .bgtu target, .reference right :: .reference left :: rest
  | .bgtu target, .reference right :: .readOnlyReference left :: rest
  | .bgtu target, .readOnlyReference right :: .reference left :: rest
  | .bgtu target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let less ← referenceLess m right left
    return .next (if less then target else pc + 1) rest frame m
  | .bleu target, .reference right :: .reference left :: rest
  | .bleu target, .reference right :: .readOnlyReference left :: rest
  | .bleu target, .readOnlyReference right :: .reference left :: rest
  | .bleu target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let less ← referenceLess m right left
    return .next (if less then pc + 1 else target) rest frame m
  -- Reference observations preserve memory and do not grant byte access authority.
  | .brzero target, .reference value :: rest
  | .brzero target, .readOnlyReference value :: rest =>
    let present ← referenceNonNull m value
    return .next (if present then pc + 1 else target) rest frame m
  | .brnonzero target, .reference value :: rest
  | .brnonzero target, .readOnlyReference value :: rest =>
    let present ← referenceNonNull m value
    return .next (if present then target else pc + 1) rest frame m
  | .eq, .reference right :: .reference left :: rest
  | .eq, .reference right :: .readOnlyReference left :: rest
  | .eq, .readOnlyReference right :: .reference left :: rest
  | .eq, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let equal ← referenceEqual m left right
    return .next (pc + 1) (.scalar (.i32 (if equal then 1 else 0)) :: rest) frame m
  | .beq target, .reference right :: .reference left :: rest
  | .beq target, .reference right :: .readOnlyReference left :: rest
  | .beq target, .readOnlyReference right :: .reference left :: rest
  | .beq target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let equal ← referenceEqual m left right
    return .next (if equal then target else pc + 1) rest frame m
  | .bne target, .reference right :: .reference left :: rest
  | .bne target, .reference right :: .readOnlyReference left :: rest
  | .bne target, .readOnlyReference right :: .reference left :: rest
  | .bne target, .readOnlyReference right :: .readOnlyReference left :: rest =>
    let equal ← referenceEqual m left right
    return .next (if equal then pc + 1 else target) rest frame m
  | .stackAlloc initLocals, [.scalar size] =>
    let bytes ← match size with
      | .i32 bits => pure bits.toNat
      | .i64 bits => pure bits.toNat
      | _ => .error .invalidState
    let (reference, owner, memory) ← allocateStack m frame bytes initLocals
    return .next (pc + 1) [.reference reference] owner memory
  | .intrinsic operation argc, _ =>
    if !operation.available body.profile then .error (.unsupported "Intrinsic unavailable in target profile") else
    if stack.length < argc then .error .invalidState else
      let operands ← scalars (stack.take argc).reverse
      let value ← checkedIntrinsic operation operands
      return .next (pc + 1) ((← checkedValue m (.scalar value)) :: stack.drop argc) frame m
  | .nativeBinary operation, .scalar y :: .scalar x :: rest =>
    let (target, values) ← (CIL.nativeBinaryValues operation pc x y).mapError ExecutionFault.arithmetic
    let values ← (values.map Value.scalar).mapM (checkedValue m)
    return .next target (values ++ rest) frame m
  | .checkedConvert width signed unsignedInput, .scalar x :: rest =>
    let value ← (CIL.convertInteger width signed unsignedInput x).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .checkedArithmetic kind signed, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.checkedValues kind signed x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .divide signed remainder, .scalar y :: .scalar x :: rest =>
    let value ← (CIL.divideValues signed remainder x y).mapError ExecutionFault.arithmetic
    return .next (pc + 1) ((← checkedValue m (.scalar value)) :: rest) frame m
  | .arg i none, _ =>
    let some value := args[i]? | .error .invalidState
    return .next (pc + 1) ((← checkedValue m value) :: stack) frame m
  | .arg i (some kind), _ =>
    let some (.scalar (.i32 bits)) := args[i]? | .error .invalidState
    return .next (pc + 1) ((← checkedValue m (.scalar (.i32 (kind.extend bits)))) :: stack) frame m
  | .vectorArg i, _ =>
    let home ← argumentHome frame i
    return .next (pc + 1) ((← loadLocal m home) :: stack) frame m
  | .vectorArgAddr i, _ =>
    let home ← argumentHome frame i
    return .next (pc + 1) ((← localAddress m home) :: stack) frame m
  | .local i _, _ | .vectorLocal i, _ =>
    let some slot := frame.locals[i]? | .error .invalidState
    return .next (pc + 1) ((← loadLocal m slot) :: stack) frame m
  | .localAddr i, _ | .vectorLocalAddr i, _ =>
    let some slot := frame.locals[i]? | .error .invalidState
    return .next (pc + 1) ((← localAddress m slot) :: stack) frame m
  | .setLocal i _, value :: rest | .setVectorLocal i, value :: rest =>
    let some slot := frame.locals[i]? | .error .invalidState
    let (slot, memory) ← storeLocal m slot value
    return .next (pc + 1) rest { frame with locals := frame.locals.set i slot } memory
  | .initializeSpanLocal index constructor, _ =>
    let some slot := frame.locals[index]? | .error .invalidState
    let (memory, values) ← memoryInstruction constructor.operation stack m
    let value :: rest := values | .error .invalidState
    let (slot, memory) ← storeLocal memory slot value
    return .next (pc + 1) rest { frame with locals := frame.locals.set index slot } memory
  | .call callee argc, _ =>
    if stack.length < argc then .error .invalidState else
      let arguments ← (stack.take argc).reverse.mapM (checkedValue m)
      return .call callee arguments (stack.drop argc) m
  | .newVector256 callee argc, _ =>
    if stack.length < argc then .error .invalidState else
      let arguments ← (stack.take argc).reverse.mapM (checkedValue m)
      let (temporary, memory) ← allocateHome m frame.activation (localWidth .vector256)
      let memory ← storeValue memory (.address temporary) (.v256 0)
      let frame := { frame with owned := temporary.allocation :: frame.owned }
      return .construct callee (.reference (.address temporary) :: arguments)
        (stack.drop argc) frame temporary .vector256 memory
  | .newAggregate callee argc size, _ =>
    if size = 0 || stack.length < argc then .error .invalidState else
      let arguments ← (stack.take argc).reverse.mapM (checkedValue m)
      let (temporary, memory) ← allocateHome m frame.activation size
      let (_, memory) ← storeLocal memory (.bytes (.aggregate size) temporary)
        (.scalar (.aggregate (List.replicate size 0)))
      let frame := { frame with owned := temporary.allocation :: frame.owned }
      return .construct callee (.reference (.address temporary) :: arguments)
        (stack.drop argc) frame temporary (.aggregate size) memory
  | .memory operation, _ =>
    let (memory, values) ← staticInstruction body pc operation stack m
    return .next (pc + 1) values frame memory
  | .throw exception, _ => .error (.thrown exception)
  | .ret (some kind), [.scalar (.i32 bits)] =>
    if body.returnsValue then
      return .returned (← [.scalar (.i32 (kind.extend bits))].mapM (checkedValue m)) m
    else .error .invalidState
  | .ret none, _ =>
    if stack.length = (if body.returnsValue then 1 else 0) then
      return .returned (← stack.mapM (checkedValue m)) m
    else .error .invalidState
  | _, _ =>
    match pureArity op with
    | some argc =>
      if stack.length < argc then .error .invalidState else
        let values ← scalars (stack.take argc)
        let some (.next target result _) :=
          CIL.step op false pc [] 0 values (fun _ => none) body.profile | .error .invalidState
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
