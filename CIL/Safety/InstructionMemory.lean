import CIL.Safety.SnapshotMemory
import CIL.Safety.SpanViews
import CIL.Safety.ArrayViews
import CIL.Semantics

/-!
# Checked memory instructions

The values, faults and memory instructions of the checked interpreter
(`CIL/Safety/Execution.lean`). A `Value` keeps managed references and spans apart from
integers, and every failure is an `ExecutionFault`. `instruction` and `memoryInstruction`
give loads, stores, typed copies, fields, lanes, blocks and spans their meaning over the
allocation-aware `Memory`, so every byte moved passes its form and access checks.
Multi-byte numbers are little-endian.
-/

namespace CIL.Safety

/-- A value on the checked evaluation stack: a scalar, a managed reference, or a span (a
    reference and its element count). References are not integers, so code cannot turn a
    number into an address. -/
inductive Value where
  | scalar (value : CIL.Value)
  | reference (value : ManagedReference)
  | span (reference : ManagedReference) (length : Nat)
  /-- A typed primitive buffer view, including whether writes through it are permitted. -/
  | bufferSpan (view : SpanView)
  /-- A supplied primitive array; its length is immutable and does not grant byte authority. -/
  | array (view : ArrayView)
  /-- A reference obtained through a readonly view; scalar loads preserve this restriction. -/
  | readOnlyReference (reference : ManagedReference)
  deriving DecidableEq, Repr

/-- Why the checked interpreter stopped. -/
inductive ExecutionFault where
  /-- Checked arithmetic failed, for example by dividing by zero or overflowing. -/
  | arithmetic (fault : CIL.ArithmeticFault)
  /-- An access of `width` bytes through `reference` broke the memory rule `rule`. -/
  | memory (rule : Fault) (reference : ManagedReference) (width : Nat)
  /-- An ill-typed stack, a missing argument, local or method, or another malformed state. -/
  | invalidState
  /-- An operation the model rejects rather than gives a meaning, such as observing
      unspecified vector bits or an overlapping block copy. -/
  | unsupported (description : String)
  /-- The method raised the CLR exception named `exception`. -/
  | thrown (exception : String)
  /-- `run` ran out of fuel before the method returned. -/
  | fuelExhausted
  /-- Dynamic stack demand exceeded the caller-supplied per-activation quota.
      This model resource failure is not an automatically established CLR exception. -/
  | stackAllocationFailure (requested available : Nat)
  deriving DecidableEq, Repr

/-- A checked result: a value, or the fault that stopped execution. -/
abbrev ExecutionResult := Except ExecutionFault

/-- Whether a stack value has bits that must not be observed; only a scalar can. -/
def Value.hasUnspecified : Value → Bool
  | .scalar value => value.hasUnspecified
  | _ => false

/-- Whether any of the top `count` stack entries has unspecified bits. -/
def unspecifiedOperands (count : Nat) (stack : List Value) : Bool :=
  (stack.take count).any Value.hasUnspecified

/-- Operands an op observes or exposes across a method boundary; `step` rejects the op when
    any of them has unspecified bits. -/
def observerCount : CIL.Op → Nat
  -- Arithmetic and comparisons
  | .nativeBinary _ | .divide .. | .checkedArithmetic .. => 2
  | .checkedConvert .. | .neg | .bnot | .convI1 | .convI2 | .convU2
  | .convI8 | .convI4 | .convU1 | .convU4 | .convU8 | .convU | .stackAlloc _ => 1
  | .add | .sub | .mul | .band | .bor | .bxor | .shl | .shr | .shrUn
  | .lt | .ltu | .gt | .gtu | .eq | .bgt _ | .ble _ | .bleu _
  | .bltu _ | .bgeu _ | .bgtu _ | .bge _ | .blt _ | .beq _ | .bne _ => 2
  | .brzero _ | .brnonzero _ | .switch _ => 1
  -- Memory, fields and lanes
  | .loadAggregate _ | .loadScalar .. | .fieldAt .. | .fieldAddress _ | .aggregateFieldAt ..
  | .lane _ | .laneAddress _ | .load64 | .skipInit | .asRef | .initAggregate _ => 1
  | .storeAggregate _ | .storeScalar _ | .setFieldAt .. | .setAggregateFieldAt ..
  | .setLane _ | .store64 | .copyObject _ => 2
  -- Method boundaries
  | .ret _ => 1
  | .call _ argc | .newVector256 _ argc | .newAggregate _ argc _ => argc
  | .memory operation => operation.argumentCount
  -- Internal forwarders preserve unspecified bits; stores and intrinsic consumers guard them.
  | .nop | .arg .. | .vectorArg _ | .vectorArgAddr _ | .local .. | .vectorLocal _
  | .vectorLocalAddr _ | .setVectorLocal _ | .localAddr _ | .setLocal .. | .const32 _
  | .const64 _ | .dup | .pop
  | .branch _ | .feature _ | .intrinsic ..
  | .throw _ | .unsupported _ => 0

/-- A memory check as an execution result; a fault is attributed to `reference` and `width`. -/
def checkedAt (reference : ManagedReference) (width : Nat) (result : Checked α) :
    ExecutionResult α :=
  result.mapError fun rule => .memory rule reference width

theorem checkedAt_ok {reference : ManagedReference} {width : Nat} {result : Checked α} {value : α}
    (h : checkedAt reference width result = .ok value) : result = .ok value := by
  cases result <;> simp_all [checkedAt, Except.mapError]

/-- The address behind a managed reference; `null` faults as a null dereference. -/
def referenceAt : ManagedReference → ExecutionResult Reference
  | .null => .error (.memory .nullDereference .null 0)
  | .address reference => .ok reference

-- Constructor equations, so stepping keeps a symbolic `referenceAt` for the caller's fact.
theorem referenceAt_null : referenceAt .null = .error (.memory .nullDereference .null 0) := rfl
theorem referenceAt_address (reference : Reference) :
    referenceAt (.address reference) = .ok reference := rfl

#print axioms referenceAt_null
#print axioms referenceAt_address

/-- The number `bytes` encode, least significant byte first. -/
def byteNumber (bytes : List (BitVec 8)) : Nat :=
  bytes.foldr (fun byte high => byte.toNat + 256 * high) 0

/-- The low `width` bytes of `value`, least significant first, as `byteNumber` reads them. -/
def numberBytes (value width : Nat) : List (BitVec 8) :=
  (List.range width).map fun i => BitVec.ofNat 8 (value / 256^i)

/-- The value a byte snapshot of `shape` denotes: a plain aggregate or vector when every byte
    is initialized, otherwise the snapshot itself. -/
def snapshotValue (shape : CIL.SnapshotShape) (bytes : List (BitVec 8 × Bool)) : CIL.Value :=
  if bytes.all Prod.snd then
    let data := bytes.map Prod.fst
    match shape with
    | .aggregate _ => .aggregate data
    | .vector128 => .v128 (BitVec.ofNat 128 (byteNumber data))
    | .vector256 => .v256 (BitVec.ofNat 256 (byteNumber data))
    | .vector512 => .v512 (BitVec.ofNat 512 (byteNumber data))
  else .snapshot shape bytes

/-- The bytes of `value` as a snapshot of `shape`, all initialized unless `value` is itself a
    snapshot; `none` when the value does not have that shape and width. -/
def valueSnapshot (shape : CIL.SnapshotShape) : CIL.Value → Option (List (BitVec 8 × Bool))
  | .snapshot actual bytes =>
    if actual = shape ∧ bytes.length = shape.width then some bytes else none
  | .aggregate bytes => match shape with
    | .aggregate width => if bytes.length = width then some (bytes.map fun b => (b, true)) else none
    | _ => none
  | .v128 bits =>
    if shape = .vector128 then some ((numberBytes bits.toNat 16).map fun b => (b, true)) else none
  | .v256 bits =>
    if shape = .vector256 then some ((numberBytes bits.toNat 32).map fun b => (b, true)) else none
  | .v512 bits =>
    if shape = .vector512 then some ((numberBytes bits.toNat 64).map fun b => (b, true)) else none
  | _ => none

/-- Reinterprets `value`, which must have shape `source`, as a value of shape `target` with
    the same bytes. Unspecified bits and unequal widths are rejected. -/
def bitcastValue (source target : CIL.SnapshotShape) (value : CIL.Value) :
    ExecutionResult CIL.Value := do
  if value.hasUnspecified then .error (.unsupported "Bitcast observes unspecified vector bits") else
  if source.width != target.width then .error .invalidState else
    let some bytes := valueSnapshot source value | .error .invalidState
    return snapshotValue target bytes

theorem valueSnapshot_length {shape : CIL.SnapshotShape} {value : CIL.Value}
    {bytes : List (BitVec 8 × Bool)} (h : valueSnapshot shape value = some bytes) :
    bytes.length = shape.width := by
  cases value with
  | snapshot actual data =>
    simp only [valueSnapshot] at h
    split at h
    · rename_i condition
      have same := Option.some.inj h
      rw [← same]
      exact condition.2
    · cases h
  | _ =>
    cases shape <;> simp_all [valueSnapshot, numberBytes, CIL.SnapshotShape.width]
    all_goals first
      | (rcases h with ⟨length, rfl⟩; simp [length])
      | (rw [← h]; simp)

/-- Reads `shape.width` bytes through `reference` with their initialization flags, as the value they
    denote; uninitialized bytes stay in a snapshot instead of faulting. -/
def loadSnapshot (memory : Memory) (reference : ManagedReference) (shape : CIL.SnapshotShape) :
    ExecutionResult CIL.Value := do
  let address ← referenceAt reference
  let bytes ← checkedAt reference shape.width (readSnapshot memory address shape.width 1)
  return snapshotValue shape bytes

/-- The alignment of ordinary reference-free accesses: byte offsets are allowed, as in the
    modelled CoreCLR x64/ARM64 normal-memory convention. This is not the portable CLI
    natural-alignment rule; aligned APIs, volatile or atomic operations and device memory are
    outside it, as `docs/SOUNDNESS.md` records. -/
abbrev ordinaryAccessAlignment : Nat := 1

/-- Loads a `width`-byte scalar or vector through `reference`, extending a 1- or 2-byte load
    to i32 with sign when `signed`. A 16-, 32- or 64-byte load of uninitialized bytes yields a
    vector snapshot instead of faulting. -/
def loadValue (memory : Memory) (reference : ManagedReference) (width : Nat)
    (signed : Bool := false) : ExecutionResult CIL.Value := do
  if width = 16 || width = 32 || width = 64 then
    if let .error .uninitialized := dereference memory reference width ordinaryAccessAlignment then
      return ← loadSnapshot memory reference
        (if width = 16 then .vector128 else if width = 32 then .vector256 else .vector512)
  let bytes ← checkedAt reference width
    (dereference memory reference width ordinaryAccessAlignment)
  let number := byteNumber bytes
  match width with
  | 1 =>
    return .i32 (if signed then (BitVec.ofNat 8 number).signExtend 32 else BitVec.ofNat 32 number)
  | 2 =>
    return .i32 (if signed then (BitVec.ofNat 16 number).signExtend 32 else BitVec.ofNat 32 number)
  | 4 => return .i32 (BitVec.ofNat 32 number)
  | 8 => return .i64 (BitVec.ofNat 64 number)
  | 16 => return .v128 (BitVec.ofNat 128 number)
  | 32 => return .v256 (BitVec.ofNat 256 number)
  | 64 => return .v512 (BitVec.ofNat 512 number)
  | _ => .error (.unsupported "Memory value width")

/-- Stores an i64 or vector value through `reference`; a vector snapshot of its full width
    keeps its initialization flags. Unspecified bits are unsupported; any other value is
    `invalidState`. -/
def storeValue (memory : Memory) (reference : ManagedReference) (value : CIL.Value) :
    ExecutionResult Memory := do
  if value.hasUnspecified then .error (.unsupported "Store observes unspecified vector bytes") else
  if let .snapshot shape bytes := value then
    if (shape = .vector128 || shape = .vector256 || shape = .vector512) &&
        bytes.length == shape.width then
      let address ← referenceAt reference
      return ← checkedAt reference shape.width
        (writeSnapshot memory address bytes ordinaryAccessAlignment)
    else .error .invalidState
  let (width, number) ← match value with
    | .i64 bits => .ok (8, bits.toNat)
    | .v128 bits => .ok (16, bits.toNat)
    | .v256 bits => .ok (32, bits.toNat)
    | .v512 bits => .ok (64, bits.toNat)
    | _ => .error .invalidState
  let address ← referenceAt reference
  checkedAt reference width
    (write memory address (numberBytes number width) ordinaryAccessAlignment)

/-- `reference` as a stack value, once it forms (a live allocation, a valid offset); `null`
    always forms. -/
def formValue (memory : Memory) (reference : ManagedReference) : ExecutionResult Value := do
  match reference with
  | .null => return .reference .null
  | .address r =>
    let result ← checkedAt reference 0 (form memory r)
    return .reference (.address result)

/-- Two non-null, live references to one allocation, checked without byte access authority. -/
def referencePositions (memory : Memory) (left right : ManagedReference) :
    ExecutionResult (Nat × Nat) := do
  let first ← referenceAt left
  let second ← referenceAt right
  let _ ← checkedAt left 0 (form memory first)
  let _ ← checkedAt right 0 (form memory second)
  if first.allocation != second.allocation then
    .error (.unsupported "Cross-allocation pointer arithmetic")
  else return (first.offset, second.offset)

/-- Pointer differences return the native-width signed byte displacement, with modular bits. -/
def referenceDifference (memory : Memory) (left right : ManagedReference) :
    ExecutionResult CIL.W64 := do
  let (first, second) ← referencePositions memory left right
  return BitVec.ofNat 64 first - BitVec.ofNat 64 second

/-- Array indices use unsigned bounds checks, so negative int32/native values are out of range. -/
def arrayIndex : CIL.Value → Option Nat
  | .i32 bits => some bits.toNat
  | .i64 bits => some bits.toNat
  | _ => none

/-- Array access distinguishes actual CLR null/bounds exceptions from malformed model states. -/
def arrayElement (memory : Memory) (view : ArrayView) (index width : Nat) :
    ExecutionResult Reference := do
  if width != view.elementType.width then .error .invalidState else pure ()
  let _ ← checkedAt view.reference 0 (view.validate memory)
  if view.reference == .null then .error (.thrown "System.NullReferenceException") else pure ()
  if index < view.length then pure () else .error (.thrown "System.IndexOutOfRangeException")
  checkedAt view.reference width (view.element memory index)
/-- Runs a `.memory` operation on the stack (top first), giving the new memory and stack.
    Operands with unspecified bits are rejected first. The static-field and span-construction
    operations need extracted metadata, so `staticInstruction` runs them and they are
    unsupported here; any other operand shape is `invalidState`. -/
def memoryInstruction (operation : CIL.MemoryOp) (stack : List Value) (memory : Memory) :
    ExecutionResult (Memory × List Value) := do
  if unspecifiedOperands operation.argumentCount stack then
    .error (.unsupported "Memory operation observes unspecified vector bits") else
  match operation, stack with
  -- Wide multiply, block copy and block initialization
  | .bigMul64, .reference low :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest =>
    return (← storeValue memory low (.i64 (left * right)),
      .scalar (.i64 (CIL.WideMultiply.high64 left right)) :: rest)
  | .copyBlock alignment,
      .scalar (.i32 count) :: .reference source :: .reference destination :: rest =>
    let width := count.toNat
    if width = 0 then return (memory, rest) else
      let src ← referenceAt source
      let dst ← referenceAt destination
      if src.allocation = dst.allocation && src.offset < dst.offset + width &&
          dst.offset < src.offset + width then
        .error (.unsupported "Overlapping block copy")
      else
        let bytes ← checkedAt source width (read memory src width alignment)
        return (← checkedAt destination width (write memory dst bytes alignment), rest)
  | .initBlock alignment,
      .scalar (.i32 count) :: .scalar (.i32 value) :: .reference destination :: rest =>
    let width := count.toNat
    if width = 0 then return (memory, rest) else
      let dst ← referenceAt destination
      let _ ← checkedAt destination width (access memory dst width alignment true)
      return (← checkedAt destination width
        (write memory dst (List.replicate width (value.setWidth 8)) alignment), rest)
  -- Vector loads and stores
  | .load128, .reference r :: rest => return (memory, .scalar (← loadValue memory r 16) :: rest)
  | .load256, .reference r :: rest => return (memory, .scalar (← loadValue memory r 32) :: rest)
  | .load512, .reference r :: rest => return (memory, .scalar (← loadValue memory r 64) :: rest)
  | .store512, .scalar (.v512 bits) :: .reference r :: rest =>
    return (← storeValue memory r (.v512 bits), rest)
  | .store512, .scalar (.snapshot .vector512 bytes) :: .reference r :: rest =>
    return (← storeValue memory r (.snapshot .vector512 bytes), rest)
  | .store128, .scalar (.v128 bits) :: .reference r :: rest =>
    return (← storeValue memory r (.v128 bits), rest)
  | .store256, .scalar (.v256 bits) :: .reference r :: rest =>
    return (← storeValue memory r (.v256 bits), rest)
  | .store128, .scalar (.snapshot .vector128 bytes) :: .reference r :: rest =>
    return (← storeValue memory r (.snapshot .vector128 bytes), rest)
  | .store256, .scalar (.snapshot .vector256 bytes) :: .reference r :: rest =>
    return (← storeValue memory r (.snapshot .vector256 bytes), rest)
  | .init256, .reference r :: rest => return (← storeValue memory r (.v256 0), rest)
  -- References, pointer arithmetic and bit casts
  | .byteOffset, .reference target :: .reference origin :: rest
  | .byteOffset, .readOnlyReference target :: .reference origin :: rest
  | .byteOffset, .reference target :: .readOnlyReference origin :: rest
  | .byteOffset, .readOnlyReference target :: .readOnlyReference origin :: rest => do
    let offset ← referenceDifference memory target origin
    return (memory, .scalar (.i64 offset) :: rest)
  | .asRef, .reference r :: rest => return (memory, (← formValue memory r) :: rest)
  | .add size signed, .scalar offset :: .reference r :: rest =>
    let some offset := CIL.offsetValue signed offset | .error .invalidState
    let address ← referenceAt r
    let result ← checkedAt r 0 (add memory address size (BitVec.ofInt 64 offset))
    return (memory, .reference (.address result) :: rest)
  | .bitcast256, .scalar (.v256 bits) :: rest => return (memory, .scalar (.v256 bits) :: rest)
  | .bitcastValue source target, .scalar value :: rest =>
    return (memory, .scalar (← bitcastValue source target value) :: rest)
  | .bitcastByteBool, .scalar (.i32 bits) :: rest =>
    if bits.toNat ≤ 1 then return (memory, .scalar (.i32 bits) :: rest)
    else .error (.unsupported "Noncanonical Boolean representation")
  | .bitcastByteBool, .scalar (.i8 bits) :: rest =>
    if bits.toNat ≤ 1 then return (memory, .scalar (.i32 (bits.zeroExtend 32)) :: rest)
    else .error (.unsupported "Noncanonical Boolean representation")
  | .skipInit, .reference r :: rest =>
    let _ ← formValue memory r
    return (memory, rest)
  -- Arrays retain the supplied length; reads and writes use checked element storage.
  | .arraySpan element writable .whole, .array array :: rest =>
    if array.elementType != element then .error .invalidState else pure ()
    let view : SpanView := ⟨array.reference, array.length, element.width, writable⟩
    let _ ← checkedAt view.reference 0 (view.validate memory)
    return (memory, .bufferSpan view :: rest)
  | .arraySpan element writable .fromStart,
      .scalar (.i32 start) :: .array array :: rest =>
    if array.elementType != element then .error .invalidState else pure ()
    let view : SpanView := ⟨array.reference, array.length, element.width, writable⟩
    let _ ← checkedAt view.reference 0 (view.validate memory)
    if start.toNat ≤ view.length then pure ()
      else .error (.thrown "System.ArgumentOutOfRangeException")
    let sliced ← checkedAt view.reference 0 (view.slice memory start.toNat
      (view.length - start.toNat))
    return (memory, .bufferSpan sliced :: rest)
  | .arraySpan element writable .counted,
      .scalar (.i32 length) :: .scalar (.i32 start) :: .array array :: rest =>
    if array.elementType != element then .error .invalidState else pure ()
    let view : SpanView := ⟨array.reference, array.length, element.width, writable⟩
    let _ ← checkedAt view.reference 0 (view.validate memory)
    if start.toNat ≤ view.length && length.toNat ≤ view.length - start.toNat then pure ()
      else .error (.thrown "System.ArgumentOutOfRangeException")
    let sliced ← checkedAt view.reference 0 (view.slice memory start.toNat length.toNat)
    return (memory, .bufferSpan sliced :: rest)
  | .arraySpan element writable .whole, .reference .null :: rest =>
    let view : SpanView := ⟨.null, 0, element.width, writable⟩
    let _ ← checkedAt view.reference 0 (view.validate memory)
    return (memory, .bufferSpan view :: rest)
  | .arraySpan element writable .fromStart, .scalar (.i32 start) :: .reference .null :: rest =>
    if start == 0 then pure () else .error (.thrown "System.ArgumentOutOfRangeException")
    let view : SpanView := ⟨.null, 0, element.width, writable⟩
    let _ ← checkedAt view.reference 0 (view.validate memory)
    return (memory, .bufferSpan view :: rest)
  | .arraySpan element writable .counted,
      .scalar (.i32 length) :: .scalar (.i32 start) :: .reference .null :: rest =>
    if start == 0 && length == 0 then pure ()
      else .error (.thrown "System.ArgumentOutOfRangeException")
    let view : SpanView := ⟨.null, 0, element.width, writable⟩
    let _ ← checkedAt view.reference 0 (view.validate memory)
    return (memory, .bufferSpan view :: rest)
  | .arrayAddress element writable, .scalar index :: .array view :: rest =>
    if view.elementType != element then .error .invalidState else pure ()
    let some index := arrayIndex index | .error .invalidState
    let reference ← arrayElement memory view index element.width
    return (memory, (if writable then .reference (.address reference)
      else .readOnlyReference (.address reference)) :: rest)
  | .arrayLength, .array view :: rest =>
    let _ ← checkedAt view.reference 0 (view.validate memory)
    if view.reference == .null then .error (.thrown "System.NullReferenceException") else
      return (memory, .scalar (.i64 (BitVec.ofNat 64 view.length)) :: rest)
  | .arrayLoad width signed, .scalar index :: .array view :: rest =>
    let some index := arrayIndex index | .error .invalidState
    let reference ← arrayElement memory view index width
    let value ← loadValue memory (.address reference) width signed
    return (memory, .scalar value :: rest)
  | .arrayStore width, .scalar value :: .scalar index :: .array view :: rest =>
    let some index := arrayIndex index | .error .invalidState
    let reference ← arrayElement memory view index width
    let number ← match width, value with
      | 1, .i32 bits | 2, .i32 bits | 4, .i32 bits => .ok bits.toNat
      | 8, .i64 bits => .ok bits.toNat
      | _, _ => .error .invalidState
    let updated ← checkedAt (.address reference) width
      (write memory reference (numberBytes number width) 1)
    return (updated, rest)
  | .arrayLength, .reference .null :: _ => .error (.thrown "System.NullReferenceException")
  | .arrayLoad .., .scalar index :: .reference .null :: _
  | .arrayAddress .., .scalar index :: .reference .null :: _ =>
    let some _ := arrayIndex index | .error .invalidState
    .error (.thrown "System.NullReferenceException")
  | .arrayStore _, .scalar _ :: .scalar index :: .reference .null :: _ =>
    let some _ := arrayIndex index | .error .invalidState
    .error (.thrown "System.NullReferenceException")
  -- Spans
  | .spanFromReference width writable, .scalar (.i32 length) :: .reference reference :: rest =>
    if length.toInt < 0 then .error (.thrown "System.ArgumentOutOfRangeException") else pure ()
    let view : SpanView := ⟨reference, length.toNat, width, writable⟩
    let _ ← checkedAt reference (length.toNat * width) (view.validate memory)
    return (memory, .bufferSpan view :: rest)
  | .spanFromReference width false,
      .scalar (.i32 length) :: .readOnlyReference reference :: rest =>
    if length.toInt < 0 then .error (.thrown "System.ArgumentOutOfRangeException") else pure ()
    let view : SpanView := ⟨reference, length.toNat, width, false⟩
    let _ ← checkedAt reference (length.toNat * width) (view.validate memory)
    return (memory, .bufferSpan view :: rest)
  | .spanReadOnly, .bufferSpan view :: rest =>
    let _ ← checkedAt view.reference 0 (view.validate memory)
    return (memory, .bufferSpan view.asReadOnly :: rest)
  | .spanSlice true, .scalar (.i32 length) :: .scalar (.i32 start) :: .bufferSpan view :: rest =>
    if start.toNat ≤ view.length && length.toNat ≤ view.length - start.toNat then pure ()
      else .error (.thrown "System.ArgumentOutOfRangeException")
    let sliced ← checkedAt view.reference 0 (view.slice memory start.toNat length.toNat)
    return (memory, .bufferSpan sliced :: rest)
  | .spanSlice false, .scalar (.i32 start) :: .bufferSpan view :: rest =>
    if start.toNat ≤ view.length then pure ()
      else .error (.thrown "System.ArgumentOutOfRangeException")
    let sliced ← checkedAt view.reference 0 (view.slice memory start.toNat (view.length - start.toNat))
    return (memory, .bufferSpan sliced :: rest)
  | .spanItem width, .scalar (.i32 index) :: .bufferSpan view :: rest =>
    if width == view.width then pure () else .error .invalidState
    if index.toNat < view.length then pure ()
      else .error (.thrown "System.IndexOutOfRangeException")
    let reference ← checkedAt view.reference width (view.element memory index.toNat)
    return (memory, (if view.writable then .reference (.address reference)
      else .readOnlyReference (.address reference)) :: rest)
  | .spanLength, .bufferSpan view :: rest =>
    let _ ← checkedAt view.reference 0 (view.validate memory)
    return (memory, .scalar (.i32 (BitVec.ofNat 32 view.length)) :: rest)
  | .spanReference, .span r _ :: rest =>
    return (memory, (← formValue memory r) :: rest)
  -- Unsigned comparison: a negative index is out of range, as in `ReadOnlySpan<T>.this[int]`.
  | .spanItem width, .scalar (.i32 index) :: .span r length :: rest =>
    if index.toNat < length then
      let address ← referenceAt r
      let result ← checkedAt r 0 (add memory address width (BitVec.ofNat 64 index.toNat))
      return (memory, .reference (.address result) :: rest)
    else .error (.thrown "System.IndexOutOfRangeException")
  | .spanLength, .span _ length :: rest =>
    return (memory, .scalar (.i32 (BitVec.ofNat 32 length)) :: rest)
  -- Null references
  | .nullRef, _ => return (memory, .reference .null :: stack)
  -- A pure comparison: no access, so a live, expired or end reference all answer false.
  | .isNullRef, .reference r :: rest =>
    return (memory, .scalar (.i32 (match r with | .null => 1 | .address _ => 0)) :: rest)
  | .staticAddress _, _ | .staticValue _, _ | .createSpan _, _ | .spanCreate, _ =>
    .error (.unsupported "Extraction-bound static/span allocation metadata")
  | _, _ => .error .invalidState

/-- Runs an op on the stack (top first) and memory: loads, stores, typed copies, aggregate
    fields, vector lanes, constants and stack shuffles. `step` falls back to it for ops with
    neither their own arm nor a value-only meaning; a `.memory` op goes to `memoryInstruction`
    without static-field metadata, and any other op is unsupported here. -/
def instruction (op : CIL.Op) (stack : List Value) (m : Memory) :
    ExecutionResult (Memory × List Value) := do
  if unspecifiedOperands (observerCount op) stack then
    .error (.unsupported "Instruction observes unspecified vector bits") else
  match op, stack with
  -- Typed copies and scalar and aggregate memory
  | .copyObject size, .reference source :: .reference destination :: rest =>
    let src ← referenceAt source
    let dst ← referenceAt destination
    if src.allocation = dst.allocation && src.offset != dst.offset &&
        src.offset < dst.offset + size && dst.offset < src.offset + size then
      .error (.unsupported "Partially overlapping typed copy")
    else
      let bytes ← checkedAt source size (read m src size ordinaryAccessAlignment)
      return (← checkedAt destination size (write m dst bytes ordinaryAccessAlignment), rest)
  | .loadScalar width signed, .reference r :: rest
  | .loadScalar width signed, .readOnlyReference r :: rest =>
    if width = 1 || width = 2 || width = 4 || width = 8 then
      return (m, .scalar (← loadValue m r width signed) :: rest)
    else .error (.unsupported "Scalar memory width")
  | .storeScalar width, .scalar value :: .reference r :: rest =>
    let number ← match width, value with
      | 1, .i32 bits | 2, .i32 bits | 4, .i32 bits => .ok bits.toNat
      | 8, .i64 bits => .ok bits.toNat
      | _, _ => .error .invalidState
    let address ← referenceAt r
    return (← checkedAt r width
      (write m address (numberBytes number width) ordinaryAccessAlignment), rest)
  | .storeScalar width, _ :: .readOnlyReference r :: _ =>
    .error (.memory .unwritable r width)
  | .loadAggregate size, .reference r :: rest =>
    if let .error .uninitialized := dereference m r size ordinaryAccessAlignment then
      return (m, .scalar (← loadSnapshot m r (.aggregate size)) :: rest)
    let bytes ← checkedAt r size (dereference m r size ordinaryAccessAlignment)
    return (m, .scalar (.aggregate bytes) :: rest)
  | .storeAggregate size, .scalar (.aggregate bytes) :: .reference r :: rest =>
    if bytes.length != size then .error .invalidState else
      let address ← referenceAt r
      return (← checkedAt r size (write m address bytes ordinaryAccessAlignment), rest)
  | .storeAggregate size, .scalar (.snapshot (.aggregate width) bytes) :: .reference r :: rest =>
    if bytes.length != size || width != size then .error .invalidState else
      let address ← referenceAt r
      return (← checkedAt r size (writeSnapshot m address bytes ordinaryAccessAlignment), rest)
  | .initAggregate size, .reference r :: rest =>
    let address ← referenceAt r
    return (← checkedAt r size
      (write m address (List.replicate size 0) ordinaryAccessAlignment), rest)
  -- Fields
  | .fieldAddress offset, .reference (.address r) :: rest =>
    let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
    return (m, .reference (.address address) :: rest)
  | .fieldAt offset width signed, .scalar (.aggregate bytes) :: rest =>
    if offset + width > bytes.length then .error .invalidState else
      let number := byteNumber ((bytes.drop offset).take width)
      let value ← match width with
        | 1 => .ok (.i32 (if signed then (BitVec.ofNat 8 number).signExtend 32
            else BitVec.ofNat 32 number))
        | 2 => .ok (.i32 (if signed then (BitVec.ofNat 16 number).signExtend 32
            else BitVec.ofNat 32 number))
        | 4 => .ok (.i32 (BitVec.ofNat 32 number))
        | 8 => .ok (.i64 (BitVec.ofNat 64 number))
        | 16 => .ok (.v128 (BitVec.ofNat 128 number))
        | 32 => .ok (.v256 (BitVec.ofNat 256 number))
        | _ => .error (.unsupported "Aggregate field width")
      return (m, .scalar value :: rest)
  | .fieldAt offset width _, .scalar (.snapshot (.aggregate size) bytes) :: rest =>
    if bytes.length != size || offset + width > size then .error .invalidState else
      if width = 16 || width = 32 then
        let value ← bitcastValue (.aggregate width) (if width = 16 then .vector128 else .vector256)
          (.snapshot (.aggregate width) ((bytes.drop offset).take width))
        return (m, .scalar value :: rest)
      else .error (.unsupported "Snapshot field width")
  | .aggregateFieldAt offset size, .scalar (.aggregate bytes) :: rest =>
    if offset + size > bytes.length then .error .invalidState else
      return (m, .scalar (.aggregate ((bytes.drop offset).take size)) :: rest)
  | .aggregateFieldAt offset size, .reference reference :: rest =>
    let r ← referenceAt reference
    let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
    let bytes ← checkedAt (.address address) size (read m address size ordinaryAccessAlignment)
    return (m, .scalar (.aggregate bytes) :: rest)
  | .setAggregateFieldAt offset size, .scalar (.aggregate bytes) :: .reference reference :: rest =>
    if bytes.length != size then .error .invalidState else
      let r ← referenceAt reference
      let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
      return (← checkedAt (.address address) size
        (write m address bytes ordinaryAccessAlignment), rest)
  | .fieldAt offset width signed, .reference (.address r) :: rest =>
    let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
    return (m, .scalar (← loadValue m (.address address) width signed) :: rest)
  | .setFieldAt offset 16, .scalar value :: .reference (.address r) :: rest =>
    let some bytes := valueSnapshot .vector128 value | .error .invalidState
    let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
    return (← checkedAt (.address address) 16
      (writeSnapshot m address bytes ordinaryAccessAlignment), rest)
  | .setFieldAt offset 32, .scalar value :: .reference (.address r) :: rest =>
    let some bytes := valueSnapshot .vector256 value | .error .invalidState
    let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
    return (← checkedAt (.address address) 32
      (writeSnapshot m address bytes ordinaryAccessAlignment), rest)
  | .setFieldAt offset width, .scalar value :: .reference (.address r) :: rest =>
    let number ← match width, value with
      | 1, .i32 bits => .ok bits.toNat
      | 2, .i32 bits => .ok bits.toNat
      | 4, .i32 bits => .ok bits.toNat
      | 8, .i64 bits => .ok bits.toNat
      | _, _ => .error .invalidState
    let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
    return (← checkedAt (.address address) width
      (write m address (numberBytes number width) ordinaryAccessAlignment), rest)
  -- Field and lane accesses through null fault like `referenceAt`, before any offset is formed.
  | .fieldAt .., .reference .null :: _ | .fieldAddress _, .reference .null :: _
  | .lane _, .reference .null :: _ | .laneAddress _, .reference .null :: _
  | .setFieldAt .., .scalar _ :: .reference .null :: _
  | .setLane _, .scalar _ :: .reference .null :: _ =>
    .error (.memory .nullDereference .null 0)
  -- Memory operations, constants and 64-bit words
  | .memory operation, _ => memoryInstruction operation stack m
  | .const32 bits, _ => return (m, .scalar (.i32 bits) :: stack)
  | .const64 bits, _ => return (m, .scalar (.i64 bits) :: stack)
  | .load64, .reference r :: rest | .load64, .readOnlyReference r :: rest =>
    return (m, .scalar (← loadValue m r 8) :: rest)
  | .store64, .scalar (.i64 bits) :: .reference r :: rest =>
    return (← storeValue m r (.i64 bits), rest)
  | .store64, _ :: .readOnlyReference r :: _ => .error (.memory .unwritable r 8)
  -- Vector lanes
  | .lane index, .reference (.address r) :: rest =>
    let address ← checkedAt (.address r) 0 (add m r 8 (BitVec.ofNat 64 index.val))
    return (m, .scalar (← loadValue m (.address address) 8) :: rest)
  | .lane index, .scalar (.v256 bits) :: rest =>
    return (m, .scalar (.i64 (CIL.Vector.lane64 bits index.val)) :: rest)
  | .laneAddress index, .reference (.address r) :: rest =>
    let address ← checkedAt (.address r) 0 (add m r 8 (BitVec.ofNat 64 index.val))
    return (m, .reference (.address address) :: rest)
  | .setLane index, .scalar (.i64 bits) :: .reference (.address r) :: rest =>
    let address ← checkedAt (.address r) 0 (add m r 8 (BitVec.ofNat 64 index.val))
    return (← storeValue m (.address address) (.i64 bits), rest)
  -- References and stack shuffles
  | .skipInit, .reference r :: rest =>
    let _ ← formValue m r
    return (m, rest)
  | .asRef, .reference r :: rest => return (m, (← formValue m r) :: rest)
  | .dup, value :: rest => return (m, value :: value :: rest)
  | .pop, _ :: rest => return (m, rest)
  | _, _ => .error (.unsupported "Not a memory instruction")

/-- Runs `ops` in order with `instruction`, stopping at the first fault. For straight-line
    examples only: it has no branches, calls or frames, which `run` handles. -/
def instructions (ops : List CIL.Op) (stack : List Value) (m : Memory) :
    ExecutionResult (Memory × List Value) := do
  match ops with
  | [] => return (m, stack)
  | op :: rest =>
    let (memory, values) ← instruction op stack m
    instructions rest values memory

/-- An execution fault with the method index and pc where it happened. -/
structure LocatedFault where
  method : Nat
  instruction : Nat
  fault : ExecutionFault
  deriving DecidableEq, Repr

/-- `instruction`, with a fault located at `method` and `pc`. -/
def instructionAt (method pc : Nat) (op : CIL.Op) (stack : List Value) (memory : Memory) :
    Except LocatedFault (Memory × List Value) :=
  (instruction op stack memory).mapError fun fault => ⟨method, pc, fault⟩

/-- Runs a straight-line body. A plain `arg` pushes the checked argument, and `ret` returns
    the stack when it holds exactly the declared number of results; running off the end is
    `invalidState`. Every other op goes through `instruction`, so branches and calls are
    unsupported here (`run` handles them). -/
def block (returns : Bool) (args : List Value) (ops : List CIL.Op)
    (stack : List Value) (m : Memory) : ExecutionResult (Memory × List Value) := do
  match ops with
  | [] => .error .invalidState
  | .arg index none :: rest =>
    let some value := args[index]? | .error .invalidState
    let value ← match value with
      | .reference reference => formValue m reference
      | .scalar value => if value.initialized then .ok (.scalar value) else .error .invalidState
      | .span reference length => .ok (.span reference length)
      | .array view => do
        let _ ← checkedAt view.reference 0 (view.validate m)
        pure (.array view)
      | .bufferSpan view => do
        let _ ← checkedAt view.reference 0 (view.validate m)
        pure (.bufferSpan view)
      | .readOnlyReference reference => do
        let _ ← formValue m reference
        pure (.readOnlyReference reference)
    block returns args rest (value :: stack) m
  | .ret none :: _ =>
    if stack.length = (if returns then 1 else 0) then return (m, stack)
    else .error .invalidState
  | op :: rest =>
    let (memory, values) ← instruction op stack m
    block returns args rest values memory

/-- `block` on a method's code, from an empty stack. -/
def methodBlock (body : CIL.Method) (args : List Value) (memory : Memory) :
    ExecutionResult (Memory × List Value) :=
  block body.returnsValue args body.code [] memory

end CIL.Safety
