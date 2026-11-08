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

/-- The runtime type the allocation of the live object `receiver` records. A reference to
    anything but an object is ill-typed. -/
def runtimeTypeOf (memory : Memory) (receiver : Reference) : ExecutionResult RuntimeType := do
  let allocation ← checkedAt (.address receiver) 0 (liveAllocation memory receiver.allocation)
  match allocation.kind with
  | .object type => .ok type
  | _ => .error .invalidState

/-- The model fault of a virtual call on an instance of a class its dispatch table omits: the
    class is outside the extraction's closed set, so the model selects no body for it. -/
def outsideDispatchTable : ExecutionFault :=
  .unsupported "Virtual call on an instance of a class outside its dispatch table"

/-- The body a virtual call enters for the live object `receiver`: the entry of `targets` for
    its exact runtime class, or `outsideDispatchTable`. -/
def virtualTarget (memory : Memory) (targets : List (CIL.Extraction.TypeExpr × Nat))
    (receiver : Reference) : ExecutionResult Nat := do
  let type ← runtimeTypeOf memory receiver
  match targets.lookup type.identity with
  | some callee => .ok callee
  | none => .error outsideDispatchTable

/-- A selected body is one the table lists. -/
theorem virtualTarget_mem {memory : Memory} {targets : List (CIL.Extraction.TypeExpr × Nat)}
    {receiver : Reference} {callee : Nat}
    (selected : virtualTarget memory targets receiver = .ok callee) :
    callee ∈ targets.map Prod.snd := by
  unfold virtualTarget at selected
  cases typed : runtimeTypeOf memory receiver with
  | error fault => simp [typed, Bind.bind, Except.bind] at selected
  | ok type =>
    simp only [typed, Bind.bind, Except.bind] at selected
    cases found : targets.lookup type.identity with
    | none => simp [found] at selected
    | some entry =>
      simp only [found, Except.ok.injEq] at selected
      subst selected
      induction targets with
      | nil => simp at found
      | cons head tail ih =>
        obtain ⟨identity, index⟩ := head
        simp only [List.lookup_cons] at found
        split at found
        · cases found; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih found)

#print axioms virtualTarget_mem

/-- `castclass` (`throwing`) or `isinst` of class `type` on a formed object reference: null and
    an object whose runtime lineage contains `type` pass unchanged; any other object becomes
    null, or throws `System.InvalidCastException` for `castclass` (ECMA-335 III.4.3, III.4.6). -/
def objectTest (memory : Memory) (type : CIL.Extraction.TypeExpr) (throwing : Bool)
    (reference : ManagedReference) : ExecutionResult ManagedReference := do
  let _ ← formObject memory reference
  match reference with
  | .null => pure .null
  | .address object =>
    let runtime ← runtimeTypeOf memory object
    if type ∈ runtime.lineage then pure reference
    else if throwing then .error (.thrown "System.InvalidCastException")
    else pure .null

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
    slots := fun identity offset =>
      if identity = memory.nextIdentity then .null else memory.slots identity offset
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
