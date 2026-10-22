import CIL.Safety.SnapshotMemory
import CIL.Semantics

namespace CIL.Safety

/-- References are not encoded as ordinary integers or untracked CIL addresses. -/
inductive Value where
  | scalar (value : CIL.Value)
  | reference (value : ManagedReference)
  | span (reference : ManagedReference) (length : Nat)
  deriving DecidableEq, Repr

inductive ExecutionFault where
  | arithmetic (fault : CIL.ArithmeticFault)
  | memory (rule : Fault) (reference : ManagedReference) (width : Nat)
  | invalidState
  | unsupported (description : String)
  | thrown (exception : String)
  | fuelExhausted
  deriving DecidableEq, Repr

abbrev ExecutionResult := Except ExecutionFault

def checkedAt (reference : ManagedReference) (width : Nat) (result : Checked α) : ExecutionResult α :=
  result.mapError fun rule => .memory rule reference width

theorem checkedAt_ok {reference : ManagedReference} {width : Nat} {result : Checked α} {value : α}
    (h : checkedAt reference width result = .ok value) : result = .ok value := by
  cases result <;> simp_all [checkedAt, Except.mapError]

def referenceAt : ManagedReference → ExecutionResult Reference
  | .null => .error (.memory .nullDereference .null 0)
  | .address r => .ok r

/-- Byte order is explicit; vector/aggregate values are snapshots. -/
def byteNumber (bytes : List (BitVec 8)) : Nat :=
  bytes.foldr (fun byte high => byte.toNat + 256 * high) 0

def numberBytes (value width : Nat) : List (BitVec 8) :=
  (List.range width).map fun i => BitVec.ofNat 8 (value / 256^i)

def snapshotValue (shape : CIL.SnapshotShape) (bytes : List (BitVec 8 × Bool)) : CIL.Value :=
  if bytes.all Prod.snd then
    let data := bytes.map Prod.fst
    match shape with
    | .aggregate _ => .aggregate data
    | .vector128 => .v128 (BitVec.ofNat 128 (byteNumber data))
    | .vector256 => .v256 (BitVec.ofNat 256 (byteNumber data))
  else .snapshot shape bytes

def valueSnapshot (shape : CIL.SnapshotShape) : CIL.Value → Option (List (BitVec 8 × Bool))
  | .snapshot actual bytes =>
    if actual = shape ∧ bytes.length = shape.width then some bytes else none
  | .aggregate bytes => match shape with
    | .aggregate width => if bytes.length = width then some (bytes.map fun b => (b, true)) else none
    | _ => none
  | .v128 bits => if shape = .vector128 then some ((numberBytes bits.toNat 16).map fun b => (b, true)) else none
  | .v256 bits => if shape = .vector256 then some ((numberBytes bits.toNat 32).map fun b => (b, true)) else none
  | _ => none

def bitcastValue (source target : CIL.SnapshotShape) (value : CIL.Value) : ExecutionResult CIL.Value := do
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
def loadSnapshot (m : Memory) (r : ManagedReference) (shape : CIL.SnapshotShape) : ExecutionResult CIL.Value := do
  let address ← referenceAt r
  let bytes ← checkedAt r shape.width (readSnapshot m address shape.width 1)
  return snapshotValue shape bytes

/-- Ordinary reference-free accesses in the target CoreCLR x64/ARM64 normal-memory
    convention permit byte offsets. This is not the portable CLI natural-alignment
    rule. ALIGNMENT.md records the runtime correspondence boundary; aligned APIs,
    volatile/atomic operations and device memory are not admitted by this rule. -/
abbrev ordinaryAccessAlignment : Nat := 1

def loadValue (m : Memory) (reference : ManagedReference) (width : Nat)
    (signed : Bool := false) : ExecutionResult CIL.Value := do
  if width = 16 || width = 32 then
    if let .error .uninitialized := dereference m reference width ordinaryAccessAlignment then
      return ← loadSnapshot m reference (if width = 16 then .vector128 else .vector256)
  let bytes ← checkedAt reference width (dereference m reference width ordinaryAccessAlignment)
  let number := byteNumber bytes
  match width with
  | 1 => return .i32 (if signed then (BitVec.ofNat 8 number).signExtend 32 else BitVec.ofNat 32 number)
  | 2 => return .i32 (if signed then (BitVec.ofNat 16 number).signExtend 32 else BitVec.ofNat 32 number)
  | 4 => return .i32 (BitVec.ofNat 32 number)
  | 8 => return .i64 (BitVec.ofNat 64 number)
  | 16 => return .v128 (BitVec.ofNat 128 number)
  | 32 => return .v256 (BitVec.ofNat 256 number)
  | _ => .error (.unsupported "Memory value width")

def storeValue (m : Memory) (reference : ManagedReference) (value : CIL.Value) : ExecutionResult Memory := do
  if let .snapshot shape bytes := value then
    if (shape = .vector128 || shape = .vector256) && bytes.length == shape.width then
      let address ← referenceAt reference
      return ← checkedAt reference shape.width (writeSnapshot m address bytes ordinaryAccessAlignment)
    else .error .invalidState
  let (width, number) ← match value with
    | .i64 bits => .ok (8, bits.toNat)
    | .v128 bits => .ok (16, bits.toNat)
    | .v256 bits => .ok (32, bits.toNat)
    | _ => .error .invalidState
  let address ← referenceAt reference
  checkedAt reference width (write m address (numberBytes number width) ordinaryAccessAlignment)

def formValue (m : Memory) (reference : ManagedReference) : ExecutionResult Value := do
  match reference with
  | .null => return .reference .null
  | .address r =>
    let result ← checkedAt reference 0 (form m r)
    return .reference (.address result)

/-- This dispatch uses the actual CIL memory operation, not a source-level
    arithmetic summary. Static/span construction requires extraction-bound
    allocation metadata and is explicitly unsupported until that is supplied. -/
def memoryInstruction (operation : CIL.MemoryOp) (stack : List Value) (m : Memory) :
    ExecutionResult (Memory × List Value) := do
  match operation, stack with
  | .bigMul64, .reference low :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest =>
    return (← storeValue m low (.i64 (left * right)), .scalar (.i64 (CIL.WideMultiply.high64 left right)) :: rest)
  | .copyBlock alignment, .scalar (.i32 count) :: .reference source :: .reference destination :: rest =>
    let width := count.toNat
    if width = 0 then return (m, rest) else
      let src ← referenceAt source
      let dst ← referenceAt destination
      if src.allocation = dst.allocation && src.offset < dst.offset + width && dst.offset < src.offset + width then
        .error (.unsupported "Overlapping block copy")
      else
        let bytes ← checkedAt source width (read m src width alignment)
        return (← checkedAt destination width (write m dst bytes alignment), rest)
  | .initBlock alignment, .scalar (.i32 count) :: .scalar (.i32 value) :: .reference destination :: rest =>
    let width := count.toNat
    if width = 0 then return (m, rest) else
      let dst ← referenceAt destination
      let _ ← checkedAt destination width (access m dst width alignment true)
      return (← checkedAt destination width (write m dst (List.replicate width (value.setWidth 8)) alignment), rest)
  | .load128, .reference r :: rest => return (m, .scalar (← loadValue m r 16) :: rest)
  | .load256, .reference r :: rest => return (m, .scalar (← loadValue m r 32) :: rest)
  | .store128, .scalar (.v128 bits) :: .reference r :: rest =>
    return (← storeValue m r (.v128 bits), rest)
  | .store256, .scalar (.v256 bits) :: .reference r :: rest =>
    return (← storeValue m r (.v256 bits), rest)
  | .store128, .scalar (.snapshot .vector128 bytes) :: .reference r :: rest =>
    return (← storeValue m r (.snapshot .vector128 bytes), rest)
  | .store256, .scalar (.snapshot .vector256 bytes) :: .reference r :: rest =>
    return (← storeValue m r (.snapshot .vector256 bytes), rest)
  | .init256, .reference r :: rest => return (← storeValue m r (.v256 0), rest)
  | .asRef, .reference r :: rest => return (m, (← formValue m r) :: rest)
  | .add size signed, .scalar offset :: .reference r :: rest =>
    let some offset := CIL.offsetValue signed offset | .error .invalidState
    let address ← referenceAt r
    let result ← checkedAt r 0 (add m address size (BitVec.ofInt 64 offset))
    return (m, .reference (.address result) :: rest)
  | .bitcast256, .scalar (.v256 bits) :: rest => return (m, .scalar (.v256 bits) :: rest)
  | .bitcastValue source target, .scalar value :: rest =>
    return (m, .scalar (← bitcastValue source target value) :: rest)
  | .bitcastByteBool, .scalar (.i32 bits) :: rest =>
    if bits.toNat ≤ 1 then return (m, .scalar (.i32 bits) :: rest)
    else .error (.unsupported "Noncanonical Boolean representation")
  | .bitcastByteBool, .scalar (.i8 bits) :: rest =>
    if bits.toNat ≤ 1 then return (m, .scalar (.i32 (bits.zeroExtend 32)) :: rest)
    else .error (.unsupported "Noncanonical Boolean representation")
  | .skipInit, .reference r :: rest =>
    let _ ← formValue m r
    return (m, rest)
  | .spanReference, .span r _ :: rest =>
    return (m, (← formValue m r) :: rest)
  -- Unsigned comparison: a negative index is out of range, as in `ReadOnlySpan<T>.this[int]`.
  | .spanItem width, .scalar (.i32 index) :: .span r length :: rest =>
    if index.toNat < length then
      let address ← referenceAt r
      let result ← checkedAt r 0 (add m address width (BitVec.ofNat 64 index.toNat))
      return (m, .reference (.address result) :: rest)
    else .error (.thrown "System.IndexOutOfRangeException")
  | .spanLength, .span _ length :: rest => return (m, .scalar (.i32 (BitVec.ofNat 32 length)) :: rest)
  | .nullRef, _ => return (m, .reference .null :: stack)
  -- A pure comparison: no access, so a live, expired or end reference all answer false.
  | .isNullRef, .reference r :: rest =>
    return (m, .scalar (.i32 (match r with | .null => 1 | .address _ => 0)) :: rest)
  | .staticAddress _, _ | .staticValue _, _ | .createSpan _, _ | .spanCreate, _ =>
    .error (.unsupported "Extraction-bound static/span allocation metadata")
  | _, _ => .error .invalidState

/-- The memory part of instruction execution. Pure/control instructions and
    calls will be connected by the execution layer; they cannot fall through to
    an unchecked memory interpreter here. -/
def instruction (op : CIL.Op) (stack : List Value) (m : Memory) :
    ExecutionResult (Memory × List Value) := do
  match op, stack with
  | .copyObject size, .reference source :: .reference destination :: rest =>
    let src ← referenceAt source
    let dst ← referenceAt destination
    if src.allocation = dst.allocation && src.offset != dst.offset &&
        src.offset < dst.offset + size && dst.offset < src.offset + size then
      .error (.unsupported "Partially overlapping typed copy")
    else
      let bytes ← checkedAt source size (read m src size ordinaryAccessAlignment)
      return (← checkedAt destination size (write m dst bytes ordinaryAccessAlignment), rest)
  | .loadScalar width signed, .reference r :: rest =>
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
    return (← checkedAt r size (write m address (List.replicate size 0) ordinaryAccessAlignment), rest)
  | .fieldAddress offset, .reference (.address r) :: rest =>
    let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
    return (m, .reference (.address address) :: rest)
  | .fieldAt offset width signed, .scalar (.aggregate bytes) :: rest =>
    if offset + width > bytes.length then .error .invalidState else
      let number := byteNumber ((bytes.drop offset).take width)
      let value ← match width with
        | 1 => .ok (.i32 (if signed then (BitVec.ofNat 8 number).signExtend 32 else BitVec.ofNat 32 number))
        | 2 => .ok (.i32 (if signed then (BitVec.ofNat 16 number).signExtend 32 else BitVec.ofNat 32 number))
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
      return (← checkedAt (.address address) size (write m address bytes ordinaryAccessAlignment), rest)
  | .fieldAt offset width signed, .reference (.address r) :: rest =>
    let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
    return (m, .scalar (← loadValue m (.address address) width signed) :: rest)
  | .setFieldAt offset 16, .scalar value :: .reference (.address r) :: rest =>
    let some bytes := valueSnapshot .vector128 value | .error .invalidState
    let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
    return (← checkedAt (.address address) 16 (writeSnapshot m address bytes ordinaryAccessAlignment), rest)
  | .setFieldAt offset 32, .scalar value :: .reference (.address r) :: rest =>
    let some bytes := valueSnapshot .vector256 value | .error .invalidState
    let address ← checkedAt (.address r) 0 (add m r 1 (BitVec.ofNat 64 offset))
    return (← checkedAt (.address address) 32 (writeSnapshot m address bytes ordinaryAccessAlignment), rest)
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
  | .setFieldAt .., .scalar _ :: .reference .null :: _ | .setLane _, .scalar _ :: .reference .null :: _ =>
    .error (.memory .nullDereference .null 0)
  | .memory operation, _ => memoryInstruction operation stack m
  | .const32 bits, _ => return (m, .scalar (.i32 bits) :: stack)
  | .const64 bits, _ => return (m, .scalar (.i64 bits) :: stack)
  | .load64, .reference r :: rest => return (m, .scalar (← loadValue m r 8) :: rest)
  | .store64, .scalar (.i64 bits) :: .reference r :: rest =>
    return (← storeValue m r (.i64 bits), rest)
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
  | .skipInit, .reference r :: rest =>
    let _ ← formValue m r
    return (m, rest)
  | .asRef, .reference r :: rest => return (m, (← formValue m r) :: rest)
  | .dup, value :: rest => return (m, value :: value :: rest)
  | .pop, _ :: rest => return (m, rest)
  | _, _ => .error (.unsupported "Non-memory instruction requires execution adapter")

/-- Sequential semantic examples stop at the first fault. This is not the
    branch/call interpreter used to issue production certificates. -/
def instructions (ops : List CIL.Op) (stack : List Value) (m : Memory) :
    ExecutionResult (Memory × List Value) := do
  match ops with
  | [] => return (m, stack)
  | op :: rest =>
    let (memory, values) ← instruction op stack m
    instructions rest values memory

structure LocatedFault where
  method : Nat
  instruction : Nat
  fault : ExecutionFault
  deriving DecidableEq, Repr

def instructionAt (method pc : Nat) (op : CIL.Op) (stack : List Value) (m : Memory) :
    Except LocatedFault (Memory × List Value) :=
  (instruction op stack m).mapError fun fault => ⟨method, pc, fault⟩

/-- Actual straight-line CIL bodies, including argument loads and return
    shape. Branch/call/frame support remains an explicit next integration step. -/
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
    block returns args rest (value :: stack) m
  | .ret none :: _ =>
    if stack.length = (if returns then 1 else 0) then return (m, stack)
    else .error .invalidState
  | op :: rest =>
    let (memory, values) ← instruction op stack m
    block returns args rest values memory

def methodBlock (body : CIL.Method) (args : List Value) (m : Memory) :
    ExecutionResult (Memory × List Value) :=
  block body.returnsValue args body.code [] m

end CIL.Safety
