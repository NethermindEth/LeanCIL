import CIL.Safety.AllocationExtension

/-!
# Steps that create no instance

`ObjectsKept before after` says `after` holds no class instance that `before` did not already
hold with the same runtime type. Writes, frame homes, statics, arrays and expiry establish it;
only `newobj` breaks it, which `CIL/Safety/ExecutionClasses.lean` accounts for separately.
-/

namespace CIL.Safety

/-- Every instance in `after` was already an instance of the same runtime type in `before`. -/
def ObjectsKept (before after : Memory) : Prop :=
  ∀ id allocation type, after.allocations id = some allocation → allocation.kind = .object type →
    ∃ earlier, before.allocations id = some earlier ∧ earlier.kind = .object type

theorem ObjectsKept.refl (memory : Memory) : ObjectsKept memory memory :=
  fun _ allocation _ present kind => ⟨allocation, present, kind⟩

theorem ObjectsKept.trans {first middle last : Memory} (left : ObjectsKept first middle)
    (right : ObjectsKept middle last) : ObjectsKept first last := by
  intro id allocation type present kind
  obtain ⟨earlier, found, earlierKind⟩ := right id allocation type present kind
  exact left id earlier type found earlierKind

/-- An operation that leaves the allocation table as it was creates no instance. -/
theorem ObjectsKept.of_allocations {before after : Memory}
    (same : after.allocations = before.allocations) : ObjectsKept before after := by
  intro id allocation _ present kind
  exact ⟨allocation, same ▸ present, kind⟩

/-- Allocating storage that is not an object creates no instance. -/
theorem allocate_objectsKept {memory result : Memory} {allocation : Allocation}
    {identity : AllocationId} (notObject : ∀ type, allocation.kind ≠ .object type)
    (allocated : allocate memory allocation = .ok (identity, result)) :
    ObjectsKept memory result := by
  unfold allocate at allocated
  split at allocated
  · cases allocated
  split at allocated
  · cases allocated
  cases allocated
  intro id found type present kind
  by_cases fresh : id = memory.nextIdentity
  · simp only [fresh, ite_true, Option.some.injEq] at present
    subst present
    exact absurd kind (notObject type)
  · simp only [fresh, ite_false] at present
    exact ⟨found, present, kind⟩

/-- A checked byte write creates no instance. -/
theorem write_objectsKept {memory result : Memory} {reference : Reference}
    {bytes : List (BitVec 8)} {alignment : Nat}
    (written : write memory reference bytes alignment = .ok result) :
    ObjectsKept memory result := by
  apply ObjectsKept.of_allocations
  unfold write at written
  cases checked : access memory reference bytes.length alignment true <;>
    simp only [checked, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
  · cases written
  · cases written; rfl

/-- Expiry ends an allocation's lifetime and keeps its kind. -/
theorem expire_objectsKept (memory : Memory) (identity : AllocationId) :
    ObjectsKept memory (expire memory identity) := by
  intro id allocation type present kind
  by_cases same : id = identity
  · simp only [expire, same, ite_true] at present
    cases found : memory.allocations identity with
    | none => simp [found] at present
    | some earlier =>
      simp only [found, Option.map_some, Option.some.injEq] at present
      subst present
      exact ⟨earlier, same ▸ found, kind⟩
  · simp only [expire, same, ite_false] at present
    exact ⟨allocation, present, kind⟩

/-- Expiring a list of allocations, as a returning frame does, creates no instance. -/
theorem expireAll_objectsKept (ids : List AllocationId) (memory : Memory) :
    ObjectsKept memory (ids.foldl expire memory) := by
  induction ids generalizing memory with
  | nil => exact .refl _
  | cons id ids ih => exact (expire_objectsKept memory id).trans (ih _)

#print axioms ObjectsKept.trans
#print axioms allocate_objectsKept
#print axioms write_objectsKept
#print axioms expireAll_objectsKept

end CIL.Safety
