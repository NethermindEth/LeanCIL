import CIL.Safety.InstructionMemory

/-!
# Readonly statics in the checked interpreter

`staticReference` resolves an extracted readonly static field to immutable storage, creating
it on first use and revalidating a cached binding on every later use. An opaque field's value
is not extracted, so it must already be bound by the caller and is never created. `staticLoad`
and `staticAddress` run `ldsfld`, `ldsflda` and a field `ldtoken` through the descriptor
bound to their pc. `staticInstruction` runs the span constructors over static storage and hands
every other memory instruction to `memoryInstruction`. `staticSpanAligned` is the element
alignment a typed static span needs.
-/

namespace CIL.Safety

/-- Decode a readonly field using its storage width and narrow signedness. -/
def staticLoadedValue (descriptor : CIL.StaticDescriptor) : Option CIL.Value :=
  match descriptor.scalar with
  | none => some (.aggregate descriptor.bytes)
  | some signed =>
    let number := byteNumber descriptor.bytes
    match descriptor.bytes.length with
    | 1 => some (.i32 (if signed then (BitVec.ofNat 8 number).signExtend 32
        else BitVec.ofNat 32 number))
    | 2 => some (.i32 (if signed then (BitVec.ofNat 16 number).signExtend 32
        else BitVec.ofNat 32 number))
    | 4 => some (.i32 (BitVec.ofNat 32 number))
    | 8 => some (.i64 (BitVec.ofNat 64 number))
    | _ => none

/-- Static initialization occurs before exposing the readonly view. Existing
    bindings are checked against the freshly extracted field bytes, lifetime
    and layout; cached contents are never trusted just because names match.
    An opaque binding may hold any bytes of the field's width, and without one the
    lookup faults: nothing supplies an opaque value except the caller's memory. -/
def staticReference (descriptor : CIL.StaticDescriptor) (m : Memory) :
    ExecutionResult (Memory × Reference) := do
  match m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some (_, reference) =>
    let allocation ← checkedAt (.address reference) descriptor.bytes.length
      (liveAllocation m reference.allocation)
    if allocation.kind == .immutableStatic && reference.offset == 0 &&
        allocation.layout.size == descriptor.bytes.length &&
        allocation.layout.alignment == descriptor.alignment then pure () else .error .invalidState
    let bytes ← checkedAt (.address reference) descriptor.bytes.length
      (read m reference descriptor.bytes.length 1)
    if descriptor.opaqueValue || bytes == descriptor.bytes then return (m, reference)
    else .error .invalidState
  | none =>
    if descriptor.opaqueValue then
      .error (.unsupported "Opaque static field value is not bound by the caller")
    let (id, memory) ← checkedAt .null descriptor.bytes.length (allocate m {
      kind := .immutableStatic
      layout := ⟨descriptor.bytes.length, descriptor.alignment, []⟩
      sentinels := [descriptor.bytes.length] })
    let reference : Reference := ⟨id, 0⟩
    return ({ memory with
      cells := fun other offset => if other == id then
        match descriptor.bytes[offset]? with
        | some byte => ⟨byte, true⟩
        | none => ⟨0, false⟩
        else memory.cells other offset
      views := ⟨id, 0, descriptor.bytes.length, true, false⟩ :: memory.views
      staticBindings := (descriptor.identity, reference) :: memory.staticBindings }, reference)

/-- `ldsfld` at `pc`: an opaque value read from the caller's binding, or the value an initializer
    was checked to produce. RVA data has no extracted value to load. -/
def staticLoad (body : CIL.Method) (pc : Nat) (memory : Memory) :
    ExecutionResult (Memory × Value) := do
  let some descriptor := body.staticAt pc |
    .error (.unsupported "Missing extracted static field identity")
  if descriptor.opaqueValue then
    let (memory, reference) ← staticReference descriptor memory
    let loaded ← checkedAt (.address reference) descriptor.bytes.length
      (read memory reference descriptor.bytes.length 1)
    let some value := staticLoadedValue { descriptor with bytes := loaded } | .error .invalidState
    return (memory, .scalar value)
  -- The translation certificate checks each initializer's result against these bytes.
  else if descriptor.initializer.isSome then
    let some value := staticLoadedValue descriptor | .error .invalidState
    return (memory, .scalar value)
  else .error (.unsupported "Static field value is not extracted")

/-- `ldsflda` or a field `ldtoken` at `pc`: the reference to the read-only storage of the
    descriptor bound there. -/
def staticAddress (body : CIL.Method) (pc : Nat) (memory : Memory) :
    ExecutionResult (Memory × Value) := do
  let some descriptor := body.staticAt pc |
    .error (.unsupported "Missing extracted static field identity")
  let (memory, reference) ← staticReference descriptor memory
  return (memory, .reference (.address reference))

/-- CoreCLR's `CreateSpan<T>` throws unless the field data is aligned to `sizeof(T)`, so a typed
    span needs `width` to divide the allocation's guaranteed alignment. -/
def staticSpanAligned (allocation : Allocation) (width : Nat) : Bool :=
  0 < width && allocation.layout.alignment % width == 0

/-- Runs a memory instruction, reading neither the method nor the pc; span constructors over raw
    pointers are accepted only inside extracted static data. -/
def staticInstruction (_body : CIL.Method) (_pc : Nat) (operation : CIL.MemoryOp)
    (stack : List Value) (m : Memory) : ExecutionResult (Memory × List Value) := do
  match operation, stack with
  | .spanCreate, .scalar (.i32 length) :: .reference (.address reference) :: rest =>
    if length.toInt < 0 then .error .invalidState else pure ()
    let allocation ← checkedAt (.address reference) length.toNat
      (liveAllocation m reference.allocation)
    if allocation.kind == .immutableStatic then pure () else
      .error (.unsupported "Span pointer constructor outside extracted static data")
    let _ ← formValue m (.address reference)
    if reference.offset + length.toNat ≤ allocation.layout.size then pure () else
      .error (.memory .outsideAllocation (.address reference) length.toNat)
    return (m, .span (.address reference) length.toNat :: rest)
  | .createSpan width, .reference (.address reference) :: rest =>
    let allocation ← checkedAt (.address reference) 0 (liveAllocation m reference.allocation)
    if allocation.kind == .immutableStatic && reference.offset == 0 && 0 < width &&
        allocation.layout.size % width == 0 then
      if staticSpanAligned allocation width then
        return (m, .span (.address reference) (allocation.layout.size / width) :: rest)
      else .error (.unsupported "Typed span element width does not divide the field alignment")
    else .error (.unsupported "Typed span outside a whole extracted static field")
  | .spanCreate, .scalar (.i32 length) :: .reference .null :: rest =>
    if length == 0 then return (m, .span .null 0 :: rest)
    else .error (.memory .nullDereference .null length.toNat)
  | _, _ => memoryInstruction operation stack m

end CIL.Safety
