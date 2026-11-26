import CIL.Safety.Execution
import CIL.Extraction.Translation

/-! # Array element addresses preserve bounds, lifetime and access authority -/

namespace Tests.ArrayElementReferences
open CIL.Safety

private def memory : Memory := {
  allocations := fun identity => if identity == 0 then
    some ⟨.managedHeap, ⟨8, 4, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, false⟩
  views := []
  nextIdentity := 1 }
private def array : ArrayView := ⟨.address ⟨0, 0⟩, 2, .signed32⟩

/-- Address formation needs a live extent, not initialized contents or access authority. -/
theorem address_without_authority :
    elementAddressInstruction (.value .signed32) false [.scalar (.i32 1), .array array] memory =
      .ok (memory, [.reference (.address ⟨0, 4⟩)]) := rfl
#print axioms address_without_authority

/-- Merely obtaining an element address grants no write authority. -/
theorem address_cannot_grant_write :
    write memory ⟨0, 4⟩ (numberBytes 7 4) 1 = .error .unwritable := rfl
#print axioms address_cannot_grant_write

/-- The end position is not an array element, even though it can be a valid pointer position. -/
theorem end_address_rejected :
    elementAddressInstruction (.value .signed32) false [.scalar (.i32 2), .array array] memory =
      .error (.thrown .indexOutOfRange) := rfl
#print axioms end_address_rejected

/-- A null array has no element address. -/
theorem null_address_rejected :
    elementAddressInstruction (.value .signed32) false [.scalar (.i32 0), .object .null] memory =
      .error (.thrown .nullReference) := rfl
#print axioms null_address_rejected

/-- Negative indices cannot wrap back into the allocation. -/
theorem negative_address_rejected :
    elementAddressInstruction (.value .signed32) false
      [.scalar (.i32 (BitVec.ofInt 32 (-1))), .array array] memory =
      .error (.thrown .indexOutOfRange) := rfl
#print axioms negative_address_rejected

/-- Empty arrays have no element, including at their valid end position. -/
theorem empty_address_rejected :
    elementAddressInstruction (.value .signed32) false
      [.scalar (.i32 0), .array ⟨.address ⟨0, 8⟩, 0, .signed32⟩] memory =
      .error (.thrown .indexOutOfRange) := rfl
#print axioms empty_address_rejected

/-- A returned element reference becomes invalid when its backing allocation expires. -/
theorem expired_element_rejected :
    checkedValue (expire memory 0) (.reference (.address ⟨0, 4⟩)) =
      .error (.memory .expiredLifetime (.address ⟨0, 4⟩) 0) := rfl
#print axioms expired_element_rejected

/-- An address needs inline element storage: a class element is an ill-typed state, and no heap
    array holds a by-ref-like struct. -/
theorem address_shapes_refused :
    elementAddressInstruction (.reference (.atom CIL.Extraction.runtimeScope "System.String"
        .classType))
      false [.scalar (.i32 0), .array array] memory = .error .invalidState ∧
    elementAddressInstruction (.unsupported CIL.ElementShape.byRefLikeElement) true
      [.scalar (.i32 0), .array array] memory =
      .error (.unsupported CIL.ElementShape.byRefLikeElement) := ⟨rfl, rfl⟩
#print axioms address_shapes_refused

/-- A same-width element token does not justify a different typed element address. -/
theorem wrong_address_token :
    CIL.Extraction.scalarOpMatches none
      ⟨0, 143, .type (.primitive .int32)⟩
      [.word32, .array .signed32]
      (.ldelema (.primitive .uint32) false) = false := by
  decide +kernel
#print axioms wrong_address_token

end Tests.ArrayElementReferences
