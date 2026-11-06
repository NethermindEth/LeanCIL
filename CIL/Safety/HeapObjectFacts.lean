import CIL.Safety.ObjectSteps
import CIL.Safety.WordMemory

/-!
# Heap object facts

Facts about class instance fields that proofs about extracted methods compose. An object's
identity, runtime type and field positions live in allocation metadata, which byte writes
never change, so a reference formed or a field located before a write stays so after it
(`formObject_of_allocations`, `objectFieldAddress_of_allocations`). A field written with a value
reads back as that value (`objectField_readback_i64`).
-/

namespace CIL.Safety

/-- Object formation reads only allocation metadata. -/
theorem formObject_of_allocations {memory after : Memory}
    (unchanged : after.allocations = memory.allocations) (reference : ManagedReference) :
    formObject after reference = formObject memory reference := by
  cases reference <;> simp only [formObject, liveAllocation, unchanged]
#print axioms formObject_of_allocations

/-- Locating an object field reads only allocation metadata. -/
theorem objectFieldAddress_of_allocations {memory after : Memory}
    (unchanged : after.allocations = memory.allocations) (reference : ManagedReference)
    (owner : CIL.Extraction.TypeExpr) (offset : Nat) :
    objectFieldAddress after reference owner offset =
      objectFieldAddress memory reference owner offset := by
  cases reference <;> simp only [objectFieldAddress, liveAllocation, add, form, unchanged]
#print axioms objectFieldAddress_of_allocations

/-- A 64-bit field written with `bits` loads back as `bits`. -/
theorem objectField_readback_i64 {memory after : Memory} {field : Reference} {bits : BitVec 64}
    (written : write memory field (numberBytes bits.toNat 8) 1 = .ok after) :
    loadValue after (.address field) 8 = .ok (.i64 bits) := by
  have readback := write_readback _ _ _ _ _ written
  rw [numberBytes_length] at readback
  have loaded := load_scalar_of_read (x := bits) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) readback
  simpa [numericOfWidth] using loaded
#print axioms objectField_readback_i64

/-- A located field lies at its offset in the object's own allocation, whose reference is the
    allocation's origin. -/
theorem objectFieldAddress_position {memory : Memory} {reference : ManagedReference}
    {owner : CIL.Extraction.TypeExpr} {offset : Nat} {field : Reference}
    (located : objectFieldAddress memory reference owner offset = .ok field) :
    reference = .address ⟨field.allocation, 0⟩ ∧ field.offset = offset % 2 ^ 64 := by
  cases reference with
  | null => cases located
  | address origin =>
    simp only [objectFieldAddress, Bind.bind, Except.bind, checkedAt, Except.mapError]
      at located
    cases live : liveAllocation memory origin.allocation with
    | error => simp only [live] at located; cases located
    | ok allocation =>
      simp only [live] at located
      cases kind : allocation.kind <;> simp only [kind] at located <;> try cases located
      rename_i type
      by_cases origin0 : origin.offset = 0 <;>
        by_cases typed : type.identity = owner <;>
        simp only [origin0, typed, ne_eq, not_true_eq_false, not_false_eq_true, ite_true,
          ite_false] at located <;> try cases located
      cases moved : add memory origin 1 (BitVec.ofNat 64 offset) <;>
        simp only [moved] at located <;> cases located
      simp only [add, Bind.bind, Except.bind] at moved
      cases formed : form memory origin <;> simp only [formed] at moved
      · cases moved
      · have positioned := form_preserves_provenance _ _ _ moved
        subst positioned
        obtain ⟨allocationId, originOffset⟩ := origin
        simp only at origin0
        subst origin0
        simp [BitVec.toNat_ofNat]
#print axioms objectFieldAddress_position

/-- Writing a field of an object leaves the bytes of an earlier field unchanged. -/
theorem objectField_write_preserves_earlier {memory after : Memory}
    {reference : ManagedReference} {owner : CIL.Extraction.TypeExpr}
    {earlier later width : Nat} {earlierField laterField : Reference}
    {bytes old : List (BitVec 8)}
    (earlierLocated : objectFieldAddress memory reference owner earlier = .ok earlierField)
    (laterLocated : objectFieldAddress memory reference owner later = .ok laterField)
    (apart : earlier + width ≤ later) (small : later < 2 ^ 64)
    (written : write memory laterField bytes 1 = .ok after)
    (readable : read memory earlierField width 1 = .ok old) :
    read after earlierField width 1 = .ok old := by
  obtain ⟨earlierOrigin, earlierOffset⟩ := objectFieldAddress_position earlierLocated
  obtain ⟨laterOrigin, laterOffset⟩ := objectFieldAddress_position laterLocated
  apply write_preserves_disjoint_read written readable
  right; left
  rw [earlierOffset, laterOffset, Nat.mod_eq_of_lt small]
  have := Nat.mod_le earlier (2 ^ 64)
  omega
#print axioms objectField_write_preserves_earlier

end CIL.Safety
