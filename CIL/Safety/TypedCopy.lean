import CIL.Safety.StepComposition
import CIL.Safety.AccessRequirements

/-!
# Typed copies

What a successful `cpobj` leaves in memory: each destination byte holds the
matching source byte, now marked initialized. Consumers use this to read copied structs
back without unfolding the instruction.
-/

namespace CIL.Safety

/-- Every successful typed copy initializes each destination byte to the
    corresponding byte in the source snapshot, for arbitrary memories and sizes. -/
theorem cpobj_writes_snapshot (m result : Memory) (source destination : Reference)
    (size index : Nat) (rest : List Value) (within : index < size)
    {body : Method} {type : Extraction.TypeExpr} {pc : Nat} {args : List Value} {frame : Frame}
    (width : (body.valueShape type).size? = some size)
    (stepped : step body (.cpobj type) pc args frame
      (.reference (.address source) :: .reference (.address destination) :: rest) m =
        .ok (.next (pc + 1) rest frame result)) :
    result.cells destination.allocation (destination.offset + index) =
      ⟨(m.cells source.allocation (source.offset + index)).bits, true⟩ := by
  rw [step_cpobj_eq body pc args frame m width] at stepped
  let operands := .reference (.address source) :: .reference (.address destination) :: rest
  have copied : copyInitializedBytes size operands m = .ok (result, rest) := by
    change (do
      let (updated, values) ← copyInitializedBytes size operands m
      pure (FrameAction.next (pc + 1) values frame updated)) = .ok _ at stepped
    cases executed : copyInitializedBytes size operands m with
    | error _ => rw [executed] at stepped; cases stepped
    | ok pair =>
      cases pair
      rw [executed] at stepped
      cases stepped
      rfl
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

#print axioms cpobj_writes_snapshot
end CIL.Safety
