import CIL.Safety.WriteEffects

/-!
# Indexed snapshot writes

Array-backed snapshots expose the same sequence readback and outside-range preservation as
ordinary checked writes. These facts apply to overlapping copies because bytes are captured
before any destination change.
-/

namespace CIL.Safety

/-- A successful indexed snapshot write reads back exactly its captured byte sequence. -/
theorem writeIndexed_readback (memory result : Memory) (reference : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat)
    (written : writeIndexed memory reference bytes alignment = .ok result) :
    read result reference bytes.length alignment = .ok bytes :=
  write_readback _ _ _ _ _ (by simpa only [writeIndexed_eq] using written)
#print axioms writeIndexed_readback

/-- Copying an indexed snapshot preserves every neighboring cell, even in the same allocation. -/
theorem writeIndexed_outside (memory result : Memory) (reference : Reference)
    (bytes : List (BitVec 8)) (alignment identity offset : Nat)
    (written : writeIndexed memory reference bytes alignment = .ok result)
    (outside : identity ≠ reference.allocation ∨ offset < reference.offset ∨
      reference.offset + bytes.length ≤ offset) :
    result.cells identity offset = memory.cells identity offset :=
  write_outside _ _ _ _ _ _ _ (by simpa only [writeIndexed_eq] using written) outside
#print axioms writeIndexed_outside

end CIL.Safety
