import CIL.Safety.Execution

/-!
# Word branch step

The checked step for `brnonzero` on a 64-bit scalar, in the `if value = 0` form that loop and
branch proofs split on.
-/

namespace CIL.Safety

/-- A word-valued conditional branch checks the scalar operand and preserves memory. -/
theorem step_word_nonzero (body : CIL.Method) (pc target : Nat) (args : List Value)
    (frame : Frame) (value : BitVec 64) (memory : Memory) :
    step body (.brnonzero target) pc args frame [.scalar (.i64 value)] memory =
      .ok (.next (if value = 0 then pc + 1 else target) [] frame memory) := by
  change Except.ok (FrameAction.next (if value != 0 then target else pc + 1) [] frame memory) = _
  by_cases h : value = 0 <;> simp [h]

#print axioms step_word_nonzero
end CIL.Safety
