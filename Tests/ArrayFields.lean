import CIL.Safety.ObjectSteps

/-! A class field typed as a value array holds, in its object's reference slot, the origin of a
    whole array of its element type. A load rebuilds the array from that allocation's size, so a
    store accepts only an array covering its whole allocation from offset 0, and null. -/

namespace Tests.ArrayFields

open CIL CIL.Safety

private def node : RuntimeType := ⟨.object "Examples" "Examples.Node", []⟩

/-- Allocation 0 is a 16-byte node, 1 a read-only node, 2 an array of three `int` values and 3 a
    caller stack buffer. -/
private def holding : CIL.Safety.Memory :=
  { allocations := fun identity => match identity with
      | 0 | 1 => some ⟨.object node, ⟨16, 8, []⟩, true, [16]⟩
      | 2 => some ⟨.managedHeap, ⟨12, 8, []⟩, true, [12]⟩
      | 3 => some ⟨.callerStack, ⟨12, 8, []⟩, true, []⟩
      | _ => none
    cells := fun _ _ => ⟨0, true⟩
    views := [⟨0, 0, 16, true, true⟩, ⟨1, 0, 16, true, false⟩, ⟨2, 0, 12, true, true⟩,
      ⟨3, 0, 12, true, true⟩]
    nextIdentity := 4 }

private def first : ManagedReference := .address ⟨0, 0⟩
private def readOnly : ManagedReference := .address ⟨1, 0⟩

/-- The three `int` values of allocation 2. -/
private def numbers : ArrayView := ⟨.address ⟨2, 0⟩, 3, .signed32⟩

/-- `stfld` of `array` into the field at offset 8 of `object`. -/
private def store (array : ArrayView) (object : ManagedReference) :=
  objectFieldInstruction (.setArrayField node.identity 8 .signed32) [.array array, .object object]
    holding

/-- `ldfld` of the field at offset 8 of `object` in `memory`. -/
private def load (memory : CIL.Safety.Memory) (object : ManagedReference) :=
  objectFieldInstruction (.arrayField node.identity 8 .signed32) [.object object] memory

/-- A stored array loads back whole, and only the field's slot changes, not its bytes. -/
theorem field_reads_back :
    ((store numbers first).bind fun stored => load stored.1 first).map Prod.snd =
      .ok [.array numbers] ∧
    (store numbers first).map (fun stored => (stored.1.slots 0 8, stored.1.cells 0 8)) =
      .ok (.address ⟨2, 0⟩, ⟨0, true⟩) := ⟨rfl, rfl⟩
#print axioms field_reads_back

/-- A fresh field holds the null array, and storing the null array keeps null in the slot. -/
theorem field_starts_null :
    (load holding first).map Prod.snd = .ok [.array ⟨.null, 0, .signed32⟩] ∧
    ((store ⟨.null, 0, .signed32⟩ first).bind fun stored => load stored.1 first).map Prod.snd =
      .ok [.array ⟨.null, 0, .signed32⟩] := ⟨rfl, rfl⟩
#print axioms field_starts_null

/-- A null receiver throws on both the load and the store. -/
theorem null_receiver_throws :
    load holding .null = .error (.thrown "System.NullReferenceException") ∧
    store numbers .null = .error (.thrown "System.NullReferenceException") := ⟨rfl, rfl⟩
#print axioms null_receiver_throws

/-- A store needs write authority over the field's slot. -/
theorem store_checks_slot :
    store numbers readOnly = .error (.memory .unwritable (.address ⟨1, 8⟩) 8) := rfl
#print axioms store_checks_slot

/-- Only a whole array of the field's element type is stored: a suffix, a prefix, an array of
    another element and caller stack bytes are ill-typed states, never a stored array whose
    length a later load would misread. -/
theorem store_rejects_partial_arrays :
    store ⟨.address ⟨2, 4⟩, 2, .signed32⟩ first = .error .invalidState ∧
    store ⟨.address ⟨2, 0⟩, 2, .signed32⟩ first = .error .invalidState ∧
    store ⟨.address ⟨2, 0⟩, 3, .unsigned32⟩ first = .error .invalidState ∧
    store ⟨.address ⟨3, 0⟩, 3, .signed32⟩ first = .error .invalidState := ⟨rfl, rfl, rfl, rfl⟩
#print axioms store_rejects_partial_arrays

/-- A slot naming an object rather than an array is an ill-typed state on load. -/
theorem load_rejects_object :
    load { holding with slots := fun identity offset =>
      if identity = 0 ∧ offset = 8 then first else .null } first = .error .invalidState := rfl
#print axioms load_rejects_object

end Tests.ArrayFields
