import CIL.Safety.ArrayAllocation

/-!
# Heap objects

Class instances on the checked heap. An object reference is null or offset 0 of a live
allocation whose kind records the object's runtime type (`formObject`). It carries no byte
position, so code can neither observe nor forge one, and since allocation identities are never
reused, reference equality compares identities alone. `CIL/Safety/Execution.lean` uses these
observations for `ceq`, `beq`, `bne`, `brtrue`, `brfalse` and `cgt.un` against null, and
`allocateObject` for `newobj`, which charges each instance to `Memory.heapBudget`.
-/

namespace CIL.Safety

/-- Whether a formed object reference is non-null, as `brtrue` and `x != null` observe it. -/
def objectNonNull (memory : Memory) (reference : ManagedReference) : ExecutionResult Bool := do
  let _ ← formObject memory reference
  return reference != .null

/-- Reference equality of two formed object references: both null, or the same allocation. -/
def objectEqual (memory : Memory) (left right : ManagedReference) : ExecutionResult Bool := do
  let _ ← formObject memory left
  let _ ← formObject memory right
  return left == right

/-- `cgt.un` on object references: defined only against null, where it tests presence. -/
def objectAboveNull (memory : Memory) (left right : ManagedReference) :
    ExecutionResult Bool := do
  match right with
  | .null => objectNonNull memory left
  | .address _ => .error .invalidState

/-- Object storage is aligned to the 8-byte field slots of the admitted 64-bit targets. -/
def objectAlignment : Nat := 8

/-- `memory` with a `size`-byte instance of `type` at its next identity: live, zeroed, fully
    readable and writable, and charged to the heap budget. -/
def objectMemory (memory : Memory) (type : RuntimeType) (size : Nat) : Memory :=
  { memory with
    allocations := fun identity => if identity = memory.nextIdentity then
      some ⟨.object type, ⟨size, objectAlignment, []⟩, true, [size]⟩
      else memory.allocations identity
    cells := fun identity offset =>
      if identity = memory.nextIdentity then ⟨0, true⟩ else memory.cells identity offset
    views := ⟨memory.nextIdentity, 0, size, true, true⟩ :: memory.views
    nextIdentity := memory.nextIdentity + 1
    heapBudget := memory.heapBudget - size }

/-- A fresh instance of `type` with `size` zeroed bytes and authority over all of them, or
    `allocationFailure` when `size` exceeds the heap budget, which it otherwise consumes. No
    frame owns the instance, so it lives as long as some reference to it can be observed. -/
def allocateObject (memory : Memory) (type : RuntimeType) (size : Nat) :
    ExecutionResult (Reference × Memory) := do
  if size > memory.heapBudget then
    .error (.allocationFailure size memory.heapBudget) else pure ()
  let (identity, allocated) ← checkedAt .null size
    (allocate memory ⟨.object type, ⟨size, objectAlignment, []⟩, true, [size]⟩)
  return (⟨identity, 0⟩,
    { arrayMemory allocated identity size with heapBudget := memory.heapBudget - size })

end CIL.Safety
