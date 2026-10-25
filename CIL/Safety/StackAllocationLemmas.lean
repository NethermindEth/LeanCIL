import CIL.Safety.StackAllocation
import CIL.Safety.FrameSetupLemmas
import CIL.Safety.InstructionMemoryLemmas

/-! # Memory and lifetime evidence for dynamic stack allocation -/

namespace CIL.Safety

/-- Successful allocation is either empty or a fresh frame home with optional initialization. -/
inductive StackAllocationEffect (memory : Memory) (frame : Frame) :
    ManagedReference → Frame → Memory → Prop where
  | empty : StackAllocationEffect memory frame .null frame memory
  | fresh {reference allocated result size reserved}
      (allocatedHome : allocateHome memory frame.activation size stackAlignment =
        .ok (reference, allocated))
      (initialized : result = allocated ∨
        write allocated reference (List.replicate size 0) stackAlignment = .ok result) :
      StackAllocationEffect memory frame (.address reference)
        { frame with owned := reference.allocation :: frame.owned
                     stackBytes := frame.stackBytes + reserved } result

/-- Every successful dynamic allocation supplies checked allocation and initialization evidence. -/
theorem allocateStack_effect {memory result : Memory} {frame final : Frame} {size : Nat}
    {initLocals : Bool} {reference : ManagedReference}
    (success : allocateStack memory frame size initLocals = .ok (reference, final, result)) :
    StackAllocationEffect memory frame reference final result := by
  unfold allocateStack at success
  split at success <;> simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  all_goals
  repeat' first
    | solve | exact .empty
    | solve | exact .fresh (by assumption) (Or.inl rfl)
    | solve | exact .fresh (by assumption) (Or.inr (checkedAt_ok (by assumption)))
    | cases success
    | split at success

#print axioms allocateStack_effect

/-- A nonempty successful allocation stays within the explicitly admitted resource quota. -/
theorem allocateStack_bounded {memory result : Memory} {frame final : Frame} {size : Nat}
    {initLocals : Bool} {reference : ManagedReference} (nonempty : size ≠ 0)
    (success : allocateStack memory frame size initLocals = .ok (reference, final, result)) :
    final.stackBytes ≤ memory.stackLimit ∧ memory.stackLimit ≤ maxDynamicStack := by
  unfold allocateStack at success
  split at success <;> simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  all_goals repeat' first
    | solve | exact False.elim (nonempty (by simpa using ‹(size == 0) = true›))
    | solve | simp_all only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
    | cases success
    | split at success

#print axioms allocateStack_bounded

/-- Dynamic allocation preserves well-formed memory. -/
theorem StackAllocationEffect.wellFormed {memory result : Memory} {frame final : Frame}
    {reference : ManagedReference}
    (effect : StackAllocationEffect memory frame reference final result)
    (valid : memory.WellFormed) : result.WellFormed := by
  cases effect with
  | empty => exact valid
  | fresh allocated initialized =>
    have ready := allocateHome_preserves_wellFormed _ _ _ _ _ valid allocated
    rcases initialized with rfl | written
    · exact ready
    · exact write_preserves_wellFormed _ _ _ _ _ ready written

#print axioms StackAllocationEffect.wellFormed

/-- Every old allocation remains available after reserving dynamic storage. -/
theorem StackAllocationEffect.allocations {memory result : Memory} {frame final : Frame}
    {reference : ManagedReference}
    (effect : StackAllocationEffect memory frame reference final result) :
    AllocationExtension memory result := by
  cases effect with
  | empty => exact .refl _
  | fresh allocated initialized =>
    have fresh := (allocateHome_fresh _ _ _ _ _ allocated).1
    rcases initialized with rfl | written
    · exact fresh
    · exact fresh.trans (write_extends_allocations _ _ _ _ _ written)

#print axioms StackAllocationEffect.allocations

/-- The produced reference is valid, including the null result of an empty request. -/
theorem StackAllocationEffect.reference_valid {memory result : Memory} {frame final : Frame}
    {reference : ManagedReference}
    (effect : StackAllocationEffect memory frame reference final result)
    (valid : memory.WellFormed) : (Value.reference reference).Valid result := by
  cases effect with
  | empty => trivial
  | fresh allocated initialized =>
    have formed := allocateHome_reference_valid _ _ _ _ _ allocated
    rcases initialized with rfl | written
    · exact formed
    · exact (write_extends_allocations _ _ _ _ _ written).preserves_reference
        (allocateHome_preserves_wellFormed _ _ _ _ _ valid allocated) _ _ formed

#print axioms StackAllocationEffect.reference_valid

end CIL.Safety
