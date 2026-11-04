import CIL.Safety.LoopFrames
import CIL.Safety.FieldValues

/-!
# Struct locals in loop frames

The `LoopFrame` steps of a struct local remembered by its field values, as
`.aggregate (layout.encode values)` (see `CIL.Safety.FieldValues`): `initobj` through its address
(`LoopFrame.zero_aggregate`), a field store through its address (`LoopFrame.store_field`) and a
field load through its address (`LoopFrame.load_field`). Each continues the frame facts with the
struct's new field values, from the `LocalSnapshots` laws of `CIL.Safety.AggregateFields`, so a
loop state names the fields rather than the struct's bytes. A by-value field read, `ldloc` then
`ldfld`, is `step_fieldAt_encode` on the value `LoopFrame.load` pushes.
-/

namespace CIL.Safety

variable {footprint : List (Reference × Nat)} {caller current : Memory}
  {kinds : List CIL.LocalKind} {slots : List LocalSlot}

/-- `initobj` through the address of a listed struct home zeroes it, which lists the struct whose
    fields hold `fields` when those encode as zeros, and keeps every other frame fact; nothing
    below the caller's watermark changes. -/
theorem LoopFrame.zero_aggregate {values : List (Option CIL.Value)}
    (frame : LoopFrame footprint caller current kinds slots (knownLocals values)) (index : Nat)
    (layout : AggregateLayout) (fields : List CIL.Value) {width : Nat} {bounded : width < 2 ^ 64}
    {home : Reference}
    (slot : slots[index]? = some (.bytes (.aggregate ⟨width, bounded⟩) home) := by rfl)
    (zeroed : layout.encode fields = List.replicate width 0 := by decide)
    (present : index < values.length := by simp) :
    ∃ after, (∀ body pc args stacked rest,
        step body (.initAggregate width) pc args stacked (.reference (.address home) :: rest)
          current = .ok (.next (pc + 1) rest stacked after)) ∧
      LoopFrame footprint caller after kinds slots
        (knownLocals (values.set index (some (.aggregate (layout.encode fields))))) ∧
      MemoryBelow caller.nextIdentity current after := by
  obtain ⟨after, stepped, snapshots, formed, below, -, -, written⟩ :=
    frame.snapshots.zero_aggregate frame.homes frame.wellFormed slot (frame.homes.writable_at slot)
  refine ⟨after, stepped, ⟨frame.confined.then_below below
    (Nat.le_of_eq (write_nextIdentity written).symm), formed, frame.homes.after_write written,
    ?_⟩, below⟩
  rw [← rememberLocal_knownLocals present, zeroed]
  exact snapshots

/-- Storing `value` into field `fieldIndex` of a listed struct of a valid, disjoint layout lists
    the struct with that field value replaced and keeps every other frame fact; nothing below the
    caller's watermark changes. The value is an int, word or vector its field stores. -/
theorem LoopFrame.store_field {values : List (Option CIL.Value)}
    (frame : LoopFrame footprint caller current kinds slots (knownLocals values)) (index : Nat)
    {layout : AggregateLayout} (valid : layout.Valid) (fieldIndex : Nat) (value : CIL.Value)
    {size : Fin (2 ^ 64)} {home : Reference} {fields : List CIL.Value}
    (slot : slots[index]? = some (.bytes (.aggregate size) home) := by rfl)
    (present : values[index]? = some (some (.aggregate (layout.encode fields))) := by rfl)
    (sized : layout.size = size := by rfl) (disjoint : layout.Disjoint := by decide)
    {offset width : Nat} {aggregate : Bool}
    (found : layout.fields[fieldIndex]? = some ⟨offset, width, aggregate⟩ := by rfl)
    {number : Nat} (encoded : fieldStoreNumber width value = some number := by rfl)
    (listed : fieldIndex < fields.length := by simp) :
    ∃ after, (∀ body pc args stacked rest,
        step body (.setFieldAt offset width) pc args stacked
          (.scalar value :: .reference (.address home) :: rest) current =
          .ok (.next (pc + 1) rest stacked after)) ∧
      LoopFrame footprint caller after kinds slots (knownLocals
        (values.set index (some (.aggregate (layout.encode (fields.set fieldIndex value)))))) ∧
      MemoryBelow caller.nextIdentity current after := by
  have listedLocal : index < values.length := (List.getElem?_eq_some_iff.1 present).1
  obtain ⟨after, stepped, snapshots, formed, below, -, -, -, written⟩ :=
    frame.snapshots.store_field frame.homes frame.wellFormed slot
      (show knownLocals values index = some (.aggregate (layout.encode fields)) by
        simp [knownLocals, present])
      (frame.homes.writable_at slot) valid disjoint sized rfl found value encoded
  refine ⟨after, stepped, ⟨frame.confined.then_below below
    (Nat.le_of_eq (write_nextIdentity written).symm), formed, frame.homes.after_write written,
    ?_⟩, below⟩
  have replaced := layout.setIn_encode valid disjoint found listed value
  have stored : fieldNumber width value = number := by simp [fieldNumber, encoded]
  dsimp only at replaced
  rw [stored] at replaced
  rw [← replaced, ← rememberLocal_knownLocals listedLocal]
  exact snapshots

/-- `ldfld` of field `fieldIndex` through the address of a listed struct of a valid, disjoint
    layout pushes that field's value when the field holds it exactly, and changes nothing. -/
theorem LoopFrame.load_field {values : List (Option CIL.Value)}
    (frame : LoopFrame footprint caller current kinds slots (knownLocals values)) (index : Nat)
    {layout : AggregateLayout} (valid : layout.Valid) (fieldIndex : Nat)
    {size : Fin (2 ^ 64)} {home : Reference} {fields : List CIL.Value}
    (slot : slots[index]? = some (.bytes (.aggregate size) home) := by rfl)
    (present : values[index]? = some (some (.aggregate (layout.encode fields))) := by rfl)
    (disjoint : layout.Disjoint := by decide) {offset width : Nat} {aggregate : Bool}
    (found : layout.fields[fieldIndex]? = some ⟨offset, width, aggregate⟩ := by rfl)
    {value : CIL.Value} (listed : fields[fieldIndex]? = some value := by rfl)
    (exact : FieldExact width value := by trivial) :
    ∀ body pc args stacked rest signed,
      step body (.fieldAt offset width signed) pc args stacked
        (.reference (.address home) :: rest) current =
        .ok (.next (pc + 1) (.scalar value :: rest) stacked current) := by
  obtain ⟨-, loaded⟩ := frame.snapshots.aggregate (bytes := layout.encode fields) slot
    (by simp [knownLocals, present])
  exact fieldAt_encode_home frame.wellFormed valid disjoint loaded found listed exact

#print axioms LoopFrame.zero_aggregate
#print axioms LoopFrame.store_field
#print axioms LoopFrame.load_field

end CIL.Safety
