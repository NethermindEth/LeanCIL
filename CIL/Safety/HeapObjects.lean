import CIL.Safety.InstructionMemory

/-!
# Heap objects

Class instances on the checked heap. An object reference is null or offset 0 of a live
allocation whose kind records the object's runtime type (`formObject`). It carries no byte
position, so code can neither observe nor forge one, and since allocation identities are never
reused, reference equality compares identities alone. `CIL/Safety/Execution.lean` uses these
observations for `ceq`, `beq`, `bne`, `brtrue`, `brfalse` and `cgt.un` against null.
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

end CIL.Safety
