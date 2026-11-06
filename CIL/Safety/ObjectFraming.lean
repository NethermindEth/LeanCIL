import CIL.Safety.HeapObjectFacts
import CIL.Safety.MethodContract

/-!
# Object framing across calls

What a caller keeps about class instances across a call confined to a footprint. An object's
identity, runtime type and field positions are allocation metadata, which `Confined` keeps for
every allocation that existed before the call, so a reference that formed and a field that was
located still do afterwards (`formObject_of_confined`, `objectFieldAddress_of_confined`).
Distinct objects are distinct allocations, so the fields of one are `Apart` from every field
of another (`objectField_apart_of_ne`), and a write through one object keeps the other's bytes
(`Confined.objectField_read_of_ne`). Equal references locate the same field
(`objectFieldAddress_same`), so a proof about aliased arguments rewrites one to the other.
-/

namespace CIL.Safety

/-- Object formation reads only the metadata of the reference's own allocation. -/
theorem formObject_of_allocation {before after : Memory} {reference : Reference}
    (same : after.allocations reference.allocation = before.allocations reference.allocation) :
    formObject after (.address reference) = formObject before (.address reference) := by
  simp only [formObject, liveAllocation, same]
#print axioms formObject_of_allocation

/-- Locating a field reads only the metadata of the object's own allocation. -/
theorem objectFieldAddress_of_allocation {before after : Memory} {reference : Reference}
    (same : after.allocations reference.allocation = before.allocations reference.allocation)
    (owner : CIL.Extraction.TypeExpr) (offset : Nat) :
    objectFieldAddress after (.address reference) owner offset =
      objectFieldAddress before (.address reference) owner offset := by
  simp only [objectFieldAddress, liveAllocation, add, form, same]
#print axioms objectFieldAddress_of_allocation

/-- A formed non-null object reference names an allocation below the next fresh identity. -/
theorem Memory.WellFormed.object_below {memory : Memory} (formed : memory.WellFormed)
    {reference : Reference} {value : Value}
    (success : formObject memory (.address reference) = .ok value) :
    reference.allocation < memory.nextIdentity := by
  simp only [formObject, checkedAt, Except.mapError, Bind.bind, Except.bind] at success
  cases found : liveAllocation memory reference.allocation with
  | error fault => simp only [found] at success; cases success
  | ok allocation => exact (formed.allocations _ _ (liveAllocation_ok _ _ _ found).1).1
#print axioms Memory.WellFormed.object_below

/-- An object reference that formed before a confined call still forms after it. -/
theorem formObject_of_confined {footprint : List (Reference × Nat)} {before after : Memory}
    {reference : ManagedReference} (framed : Confined footprint before after)
    (formedMemory : before.WellFormed)
    (formed : formObject before reference = .ok (.object reference)) :
    formObject after reference = .ok (.object reference) := by
  cases reference with
  | null => rfl
  | address address =>
    rw [formObject_of_allocation (framed.allocations _ (formedMemory.object_below formed))]
    exact formed
#print axioms formObject_of_confined

/-- A reference whose field is located is a formed object reference. -/
theorem formObject_of_objectFieldAddress {memory : Memory} {reference : ManagedReference}
    {owner : CIL.Extraction.TypeExpr} {offset : Nat} {field : Reference}
    (located : objectFieldAddress memory reference owner offset = .ok field) :
    formObject memory reference = .ok (.object reference) := by
  cases reference with
  | null => cases located
  | address address =>
    simp only [objectFieldAddress, Bind.bind, Except.bind, checkedAt, Except.mapError]
      at located
    simp only [formObject, Bind.bind, Except.bind, checkedAt, Except.mapError]
    cases found : liveAllocation memory address.allocation with
    | error fault => simp only [found] at located; cases located
    | ok allocation =>
      simp only [found] at located ⊢
      cases kind : allocation.kind <;> simp only [kind] at located ⊢ <;> try cases located
      by_cases origin : address.offset = 0
      · simp [origin]
      · simp [origin] at located
#print axioms formObject_of_objectFieldAddress

/-- A located field lies in an existing allocation. -/
theorem objectFieldAddress_allocated {memory : Memory} {reference : ManagedReference}
    {owner : CIL.Extraction.TypeExpr} {offset : Nat} {field : Reference}
    (located : objectFieldAddress memory reference owner offset = .ok field) :
    ∃ allocation, memory.allocations field.allocation = some allocation := by
  obtain ⟨origin, -⟩ := objectFieldAddress_position located
  subst origin
  simp only [objectFieldAddress, Bind.bind, Except.bind, checkedAt, Except.mapError] at located
  cases found : liveAllocation memory field.allocation with
  | error fault => simp only [found] at located; cases located
  | ok allocation => exact ⟨allocation, (liveAllocation_ok _ _ _ found).1⟩
#print axioms objectFieldAddress_allocated

/-- A field located before a confined call is located at the same address after it. -/
theorem objectFieldAddress_of_confined {footprint : List (Reference × Nat)}
    {before after : Memory} {reference : ManagedReference} {owner : CIL.Extraction.TypeExpr}
    {offset : Nat} {field : Reference} (framed : Confined footprint before after)
    (formedMemory : before.WellFormed)
    (located : objectFieldAddress before reference owner offset = .ok field) :
    objectFieldAddress after reference owner offset = .ok field := by
  obtain ⟨allocation, found⟩ := objectFieldAddress_allocated located
  have old := (formedMemory.allocations _ _ found).1
  obtain ⟨origin, -⟩ := objectFieldAddress_position located
  subst origin
  rw [objectFieldAddress_of_allocation (reference := ⟨field.allocation, 0⟩)
    (framed.allocations _ old)]
  exact located
#print axioms objectFieldAddress_of_confined

/-- Fields of two different objects lie in different allocations, so they share no byte. -/
theorem objectField_apart_of_ne {memory : Memory} {left right : ManagedReference}
    {leftOwner rightOwner : CIL.Extraction.TypeExpr} {leftOffset rightOffset : Nat}
    {leftField rightField : Reference}
    (leftLocated : objectFieldAddress memory left leftOwner leftOffset = .ok leftField)
    (rightLocated : objectFieldAddress memory right rightOwner rightOffset = .ok rightField)
    (distinct : left ≠ right) (leftWidth rightWidth : Nat) :
    Apart rightField rightWidth (leftField, leftWidth) := by
  obtain ⟨leftOrigin, -⟩ := objectFieldAddress_position leftLocated
  obtain ⟨rightOrigin, -⟩ := objectFieldAddress_position rightLocated
  left
  intro same
  apply distinct
  rw [leftOrigin, rightOrigin, same]
#print axioms objectField_apart_of_ne

/-- Equal object references locate a field at the same address. -/
theorem objectFieldAddress_same {memory : Memory} {left right : ManagedReference}
    {owner : CIL.Extraction.TypeExpr} {offset : Nat} {leftField rightField : Reference}
    (leftLocated : objectFieldAddress memory left owner offset = .ok leftField)
    (rightLocated : objectFieldAddress memory right owner offset = .ok rightField)
    (same : left = right) : leftField = rightField := by
  subst same
  rw [leftLocated] at rightLocated
  cases rightLocated
  rfl
#print axioms objectFieldAddress_same

/-- A call confined to a field of one object keeps the bytes of a field of a different, older
    object: reading it after the call gives what it held before. -/
theorem Confined.objectField_read_of_ne {before after : Memory} {written read : ManagedReference}
    {writtenOwner readOwner : CIL.Extraction.TypeExpr} {writtenOffset readOffset : Nat}
    {writtenField readField : Reference} {writtenWidth width alignment : Nat}
    {bytes : List (BitVec 8)}
    (framed : Confined [(writtenField, writtenWidth)] before after)
    (old : readField.allocation < before.nextIdentity)
    (writtenLocated :
      objectFieldAddress before written writtenOwner writtenOffset = .ok writtenField)
    (readLocated : objectFieldAddress before read readOwner readOffset = .ok readField)
    (distinct : written ≠ read)
    (loaded : CIL.Safety.read before readField width alignment = .ok bytes) :
    CIL.Safety.read after readField width alignment = .ok bytes :=
  (framed.read_eq readField old width alignment (Outside.of_apart (by
    intro entry member
    simp only [List.mem_singleton] at member
    subst member
    exact objectField_apart_of_ne writtenLocated readLocated distinct writtenWidth width))).trans
    loaded
#print axioms Confined.objectField_read_of_ne

end CIL.Safety
