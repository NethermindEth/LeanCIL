import CIL.Safety.InstructionMemory
import CIL.Safety.AccessRequirements

/-!
# Typed copies

What a successful `cpobj` (`copyObject`) leaves in memory: each destination byte holds the
matching source byte, now marked initialized. Consumers use this to read copied structs
back without unfolding the instruction.
-/

namespace CIL.Safety

/-- Every successful typed copy initializes each destination byte to the
    corresponding byte in the source snapshot, for arbitrary memories and sizes. -/
theorem copyObject_writes_snapshot (m result : Memory) (source destination : Reference)
    (size index : Nat) (rest : List Value) (within : index < size)
    (copied : instruction (.copyObject size)
      (.reference (.address source) :: .reference (.address destination) :: rest) m =
        .ok (result, rest)) :
    result.cells destination.allocation (destination.offset + index) =
      ⟨(m.cells source.allocation (source.offset + index)).bits, true⟩ := by
  change (if source.allocation = destination.allocation && source.offset != destination.offset &&
      source.offset < destination.offset + size && destination.offset < source.offset + size then
    .error (.unsupported "Partially overlapping typed copy") else do
      let bytes ← checkedAt (.address source) size (read m source size ordinaryAccessAlignment)
      return (← checkedAt (.address destination) size
        (write m destination bytes ordinaryAccessAlignment), rest)) =
    .ok (result, rest) at copied
  simp only [Bind.bind, Except.bind] at copied
  split at copied
  · cases copied
  · cases hr : read m source size ordinaryAccessAlignment <;>
      simp only [hr, checkedAt, Except.mapError] at copied
    · cases copied
    · rename_i bytes
      cases hw : write m destination bytes ordinaryAccessAlignment <;>
        simp only [hw, Pure.pure, Except.pure] at copied
      · cases copied
      · rename_i updated
        cases copied
        have snapshot := read_result_snapshot hr
        subst bytes
        have initialized := write_initializes _ _ _ _ _ index hw (by simpa using within)
        simpa using initialized

#print axioms copyObject_writes_snapshot
end CIL.Safety
