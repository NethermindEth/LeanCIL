import CIL.Safety.FrameEquivalence
import CIL.Safety.StackAllocation

/-! # Dynamic stack allocation respects caller resources and memory equivalence -/

namespace CIL.Safety

/-- Dynamic allocations agree on their reference and owner and leave equivalent memory. -/
def StackResultEquivalent (left right : ManagedReference × Frame × Memory) : Prop :=
  left.1 = right.1 ∧ left.2.1 = right.2.1 ∧ left.2.2.Equivalent right.2.2

/-- Equivalent resource grants and memory produce identical allocation success or failure. -/
theorem Memory.Equivalent.allocateStack {memory other : Memory} (same : memory.Equivalent other)
    (frame : Frame) (size : Nat) (initLocals : Bool) :
    ResultEquivalent StackResultEquivalent (allocateStack memory frame size initLocals)
      (allocateStack other frame size initLocals) := by
  simp only [CIL.Safety.allocateStack, same.stackLimit]
  repeat' first
    | exact .error _
    | exact .ok ⟨rfl, rfl, same⟩
    | split
  all_goals
    apply ResultEquivalent.bind (same.allocateHome _ _ _)
    intro left right related
    obtain ⟨reference, allocated⟩ := left
    obtain ⟨otherReference, otherAllocated⟩ := right
    obtain ⟨rfl, equivalent⟩ := related
    first
    | exact .ok ⟨rfl, rfl, equivalent⟩
    | apply ResultEquivalent.bind ((equivalent.write _ _ _).mapError _)
      intro left right written
      exact .ok ⟨rfl, rfl, written⟩

#print axioms Memory.Equivalent.allocateStack

end CIL.Safety
