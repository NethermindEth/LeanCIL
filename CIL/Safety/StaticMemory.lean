import CIL.Safety.InstructionMemory

/-!
# Readonly statics in the checked interpreter

`staticReference` resolves an extracted readonly static field to immutable storage, creating
it on first use and revalidating a cached binding on every later use. An opaque field's value
is not extracted, so it must already be bound by the caller and is never created.
`staticInstruction` runs the static field instructions on top of it and hands every other
memory instruction, static spans included, to `memoryInstruction`.
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

/-- Runs a memory instruction at `pc`. Static loads use the field identity extracted for that
    pc; every other operation is `memoryInstruction`. -/
def staticInstruction (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp)
    (stack : List Value) (m : Memory) : ExecutionResult (Memory × List Value) := do
  match operation, stack with
  | .staticAddress bytes, _ =>
    let some (_, descriptor) := body.staticSites.find? (fun site => site.1 == pc) |
      .error (.unsupported "Missing extracted static field identity")
    if descriptor.bytes == bytes then pure () else .error .invalidState
    let (memory, reference) ← staticReference descriptor m
    return (memory, .reference (.address reference) :: stack)
  | .staticValue bytes, _ =>
    let some (_, descriptor) := body.staticSites.find? (fun site => site.1 == pc) |
      .error (.unsupported "Missing extracted static field identity")
    -- An opaque value is whatever the caller's binding holds; `bytes` fixes only its width.
    if descriptor.opaqueValue then
      if descriptor.bytes == bytes then
        let (memory, reference) ← staticReference descriptor m
        let loaded ← checkedAt (.address reference) bytes.length
          (read memory reference bytes.length 1)
        let some value := staticLoadedValue { descriptor with bytes := loaded } |
          .error .invalidState
        return (memory, .scalar value :: stack)
      else .error .invalidState
    -- The translation certificate checks each initializer's result against these bytes.
    else if descriptor.bytes == bytes && descriptor.initializer.isSome then
      let some value := staticLoadedValue descriptor | .error .invalidState
      return (m, .scalar value :: stack)
    else .error .invalidState
  | _, _ => memoryInstruction operation stack m

end CIL.Safety
