import CIL.Safety.StackAllocation

/-! # Dynamic stack resource, initialization, alignment and expiry boundaries -/

namespace Tests.StackAllocation
open CIL.Safety

private def memory : Memory := {
  allocations := fun _ => none
  cells := fun _ _ => ⟨0, false⟩
  views := []
  nextIdentity := 0
  stackLimit := 32 }

private def frame : Frame := { activation := 0, locals := [], owned := [] }

/-- localsinit makes all allocated bytes readable as zero. -/
theorem initialized_read :
    (do
      let (reference, _, allocated) ← allocateStack memory frame 8 true
      checkedAt reference 8 (read allocated ⟨0, 0⟩ 8 8)) = .ok (List.replicate 8 0) := rfl
#print axioms initialized_read

/-- Without localsinit, readable authority does not make unwritten bytes initialized. -/
theorem uninitialized_read_rejected :
    (do
      let (_, _, allocated) ← allocateStack memory frame 8 false
      pure (read allocated ⟨0, 0⟩ 8 8)) =
        .ok (.error Fault.uninitialized) := rfl
#print axioms uninitialized_read_rejected

/-- Alignment padding is charged, so three one-byte allocations exceed a 32-byte quota. -/
theorem repeated_allocation_exhausts :
    (do
      let (_, first, allocated) ← allocateStack memory frame 1 false
      let (_, second, allocated) ← allocateStack allocated first 1 false
      let (_, _, _) ← allocateStack allocated second 1 false
      pure ()) = .error (.stackAllocationFailure 16 0) := rfl
#print axioms repeated_allocation_exhausts

/-- A nonempty request cannot succeed with the default zero resource grant. -/
theorem missing_budget_rejected :
    (allocateStack { memory with stackLimit := 0 } frame 8 true).map
      (fun _ => ()) = .error (.stackAllocationFailure 16 0) := rfl
#print axioms missing_budget_rejected

/-- Frame exit expires the dynamic storage through the existing ownership mechanism. -/
theorem escaped_storage_rejected :
    (do
      let (_, owner, allocated) ← allocateStack memory frame 8 true
      pure (read (leaveFrame owner allocated) ⟨0, 0⟩ 8 8)) =
        .ok (.error Fault.expiredLifetime) := rfl
#print axioms escaped_storage_rejected

/-- Allocation alignment does not allow a misaligned interior address. -/
theorem misaligned_access_rejected :
    (do
      let (_, _, allocated) ← allocateStack memory frame 16 true
      pure (read allocated ⟨0, 1⟩ 8 8)) = .ok (.error Fault.alignment) := rfl
#print axioms misaligned_access_rejected

end Tests.StackAllocation
