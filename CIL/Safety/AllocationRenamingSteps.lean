import CIL.Safety.MemoryRenaming
import CIL.Safety.MemoryLemmas

/-!
# Fresh allocations under renaming

Fresh source and target allocations extend their identity correspondence. Views in a
well-formed memory cannot grant permissions to an identity not yet allocated.
-/

namespace CIL.Safety

/-- A well-formed memory has no allocation at its next fresh identity. -/
theorem Memory.WellFormed.fresh {memory : Memory} (formed : memory.WellFormed) :
    memory.allocations memory.nextIdentity = none := by
  cases found : memory.allocations memory.nextIdentity with
  | none => rfl
  | some allocation => exact False.elim (Nat.lt_irrefl _ (formed.1 _ _ found).1)
#print axioms Memory.WellFormed.fresh

/-- Existing well-formed views grant no authority to future allocation identities. -/
theorem Memory.WellFormed.future_permission {memory : Memory} (formed : memory.WellFormed)
    (reference : Reference) (future : memory.nextIdentity ≤ reference.allocation) (writing : Bool) :
    permitted memory writing reference = false := by
  simp only [permitted, List.any_eq_false]
  intro view member
  obtain ⟨allocation, present, _⟩ := formed.2 view member
  have bound : view.allocation < memory.nextIdentity :=
    (formed.1 view.allocation allocation present).1
  have different : view.allocation ≠ reference.allocation :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le bound future)
  simp [viewContains, different]
#print axioms Memory.WellFormed.future_permission

/-- Paired fresh allocations extend the identity map and preserve all related observations. -/
theorem Memory.Renamed.allocate {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceDescriptor targetDescriptor : Allocation)
    (descriptors : Allocation.Related scopes sourceDescriptor targetDescriptor)
    (valid : sourceDescriptor.valid = true) :
    ∃ sourceAfter targetAfter,
      allocate source sourceDescriptor = .ok (source.nextIdentity, sourceAfter) ∧
      allocate target targetDescriptor = .ok (target.nextIdentity, targetAfter) ∧
      Memory.Renamed mapping.allocate scopes sourceAfter targetAfter := by
  let sourceAfter : Memory := { source with
    allocations := fun identity => if identity = source.nextIdentity then some sourceDescriptor
      else source.allocations identity
    cells := fun identity offset => if identity = source.nextIdentity then ⟨0, false⟩
      else source.cells identity offset
    nextIdentity := source.nextIdentity + 1 }
  let targetAfter : Memory := { target with
    allocations := fun identity => if identity = target.nextIdentity then some targetDescriptor
      else target.allocations identity
    cells := fun identity offset => if identity = target.nextIdentity then ⟨0, false⟩
      else target.cells identity offset
    nextIdentity := target.nextIdentity + 1 }
  have freshImage : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
    rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
  refine ⟨sourceAfter, targetAfter, ?_, ?_, ?_⟩
  · simp [CIL.Safety.allocate, valid, sourceFormed.fresh, sourceAfter]
  · simp [CIL.Safety.allocate, ← descriptors.valid, valid, targetFormed.fresh, targetAfter]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, related.stackLimit⟩
  · simp only [AllocationRenaming.allocate, sourceAfter, related.sourceLimit]
  · simp only [AllocationRenaming.allocate, targetAfter, related.targetLimit]
  · intro identity bound
    change identity < mapping.sourceLimit + 1 at bound
    by_cases old : identity < mapping.sourceLimit
    · have sourceDifferent : identity ≠ source.nextIdentity := by
        rw [← related.sourceLimit]
        exact Nat.ne_of_lt old
      have targetDifferent : mapping.image identity ≠ target.nextIdentity := by
        rw [← related.targetLimit]
        exact Nat.ne_of_lt (mapping.bounded identity old)
      simpa only [sourceAfter, targetAfter, AllocationRenaming.allocate, old, ite_true,
        sourceDifferent, targetDifferent, ite_false] using related.allocations identity old
    · have fresh : identity = mapping.sourceLimit := by omega
      subst identity
      simp only [sourceAfter, targetAfter, related.sourceLimit, freshImage, ite_true]
      exact .some descriptors
  · intro identity bound offset
    change identity < mapping.sourceLimit + 1 at bound
    by_cases old : identity < mapping.sourceLimit
    · have sourceDifferent : identity ≠ source.nextIdentity := by
        rw [← related.sourceLimit]
        exact Nat.ne_of_lt old
      have targetDifferent : mapping.image identity ≠ target.nextIdentity := by
        rw [← related.targetLimit]
        exact Nat.ne_of_lt (mapping.bounded identity old)
      simpa only [sourceAfter, targetAfter, AllocationRenaming.allocate, old, ite_true,
        sourceDifferent, targetDifferent, ite_false] using related.cells identity old offset
    · have fresh : identity = mapping.sourceLimit := by omega
      subst identity
      simp [sourceAfter, targetAfter, related.sourceLimit, freshImage]
  · intro reference bound writing
    change reference.allocation < mapping.sourceLimit + 1 at bound
    by_cases old : reference.allocation < mapping.sourceLimit
    · change permitted target writing (mapping.allocate.reference reference) =
        permitted source writing reference
      rw [mapping.allocate_extends.reference reference old]
      exact related.permissions reference old writing
    · have fresh : reference.allocation = mapping.sourceLimit :=
        Nat.le_antisymm (Nat.le_of_lt_succ bound) (Nat.le_of_not_gt old)
      have sourceFresh : source.nextIdentity ≤ reference.allocation := by
        simp only [fresh, related.sourceLimit, Nat.le_refl]
      have targetFresh : target.nextIdentity ≤
          (mapping.allocate.reference reference).allocation := by
        simp only [AllocationRenaming.reference, fresh, AllocationRenaming.allocate_fresh,
          related.targetLimit, Nat.le_refl]
      exact (targetFormed.future_permission _ targetFresh writing).trans
        (sourceFormed.future_permission _ sourceFresh writing).symm
  · change target.staticBindings = source.staticBindings.map _
    rw [related.staticBindings]
    apply List.map_congr_left
    intro binding member
    exact congrArg (fun reference => (binding.1, reference))
      (mapping.allocate_extends.reference binding.2 (staticBounds binding member)).symm
#print axioms Memory.Renamed.allocate
/-- A private target-only allocation leaves every source observation unchanged. -/
theorem Memory.Renamed.skipTarget {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (formed : target.WellFormed) (descriptor : Allocation) (valid : descriptor.valid = true) :
    ∃ targetAfter, CIL.Safety.allocate target descriptor = .ok (target.nextIdentity, targetAfter) ∧
      Memory.Renamed mapping.skipTarget scopes source targetAfter := by
  let targetAfter : Memory := { target with
    allocations := fun identity => if identity = target.nextIdentity then some descriptor
      else target.allocations identity
    cells := fun identity offset => if identity = target.nextIdentity then ⟨0, false⟩
      else target.cells identity offset
    nextIdentity := target.nextIdentity + 1 }
  refine ⟨targetAfter, ?_, related.sourceLimit, ?_, ?_, ?_, related.permissions,
    related.staticBindings, related.stackLimit⟩
  · simp [CIL.Safety.allocate, valid, formed.fresh, targetAfter]
  · simp only [AllocationRenaming.skipTarget, targetAfter, related.targetLimit]
  · intro identity bound
    have different : mapping.image identity ≠ target.nextIdentity := by
      rw [← related.targetLimit]
      exact Nat.ne_of_lt (mapping.bounded identity bound)
    simpa only [targetAfter, AllocationRenaming.skipTarget, different, ite_false]
      using related.allocations identity bound
  · intro identity bound offset
    have different : mapping.image identity ≠ target.nextIdentity := by
      rw [← related.targetLimit]
      exact Nat.ne_of_lt (mapping.bounded identity bound)
    simpa only [targetAfter, AllocationRenaming.skipTarget, different, ite_false]
      using related.cells identity bound offset
#print axioms Memory.Renamed.skipTarget
end CIL.Safety
