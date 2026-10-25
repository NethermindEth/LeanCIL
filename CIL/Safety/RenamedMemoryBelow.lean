import CIL.Safety.AllocationRenamingSteps
import CIL.Safety.MemoryBelow

/-!
# Caller memory under allocation renaming

A fixed caller prefix retains its exact allocation descriptors, cells and authority.
This stronger relation supports MemoryBelow conclusions without exposing identities
or frame labels of fresh allocations to a transferred contract.
-/

namespace CIL.Safety

/-- Related executions agree exactly below the caller's original allocation watermark. -/
structure Memory.RenamedBelow (watermark : Nat) (mapping : AllocationRenaming)
    (scopes : Nat → Nat → Prop) (source target : Memory) : Prop
    extends Memory.Renamed mapping scopes source target where
  sourceBound : watermark ≤ mapping.sourceLimit
  targetBound : watermark ≤ mapping.targetLimit
  fixed : ∀ identity, identity < watermark → mapping.image identity = identity
  descriptors : ∀ identity, identity < watermark →
    target.allocations identity = source.allocations identity

/-- The original caller memory satisfies the exact-prefix relation. -/
theorem Memory.RenamedBelow.refl (memory : Memory) (scopes : Nat → Nat → Prop) :
    Memory.RenamedBelow memory.nextIdentity (.identity memory.nextIdentity) scopes memory memory :=
  ⟨Memory.Renamed.refl memory scopes, Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl,
    fun _ _ => rfl⟩
#print axioms Memory.RenamedBelow.refl

/-- The caller's metadata, bytes and authority agree exactly between related executions. -/
theorem Memory.RenamedBelow.memoryBelow {watermark : Nat} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.RenamedBelow watermark mapping scopes source target) :
    MemoryBelow watermark source target := by
  refine ⟨related.descriptors, ?_, ?_⟩
  · intro identity bound offset
    have cells := related.cells identity (Nat.lt_of_lt_of_le bound related.sourceBound) offset
    simpa only [related.fixed identity bound] using cells
  · intro identity bound offset writing
    have permissions := related.permissions ⟨identity, offset⟩
      (Nat.lt_of_lt_of_le bound related.sourceBound) writing
    simpa only [AllocationRenaming.reference, related.fixed identity bound] using permissions
#print axioms Memory.RenamedBelow.memoryBelow

/-- Caller confinement transfers without referring to fresh allocation identities. -/
theorem Memory.RenamedBelow.confined {watermark : Nat} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {initial source target : Memory}
    (related : Memory.RenamedBelow watermark mapping scopes source target)
    (preserved : MemoryBelow watermark initial source) : MemoryBelow watermark initial target :=
  preserved.trans related.memoryBelow
#print axioms Memory.RenamedBelow.confined

/-- A paired allocation retains the exact caller prefix as well as the evolving map. -/
theorem Memory.RenamedBelow.allocate {watermark : Nat} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.RenamedBelow watermark mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceDescriptor targetDescriptor : Allocation)
    (descriptors : Allocation.Related scopes sourceDescriptor targetDescriptor)
    (valid : sourceDescriptor.valid = true) :
    ∃ sourceAfter targetAfter,
      CIL.Safety.allocate source sourceDescriptor = .ok (source.nextIdentity, sourceAfter) ∧
      CIL.Safety.allocate target targetDescriptor = .ok (target.nextIdentity, targetAfter) ∧
      Memory.RenamedBelow watermark mapping.allocate scopes sourceAfter targetAfter := by
  obtain ⟨sourceAfter, targetAfter, sourceAllocated, targetAllocated, renamed⟩ :=
    related.toRenamed.allocate sourceFormed targetFormed staticBounds sourceDescriptor
      targetDescriptor descriptors valid
  refine ⟨sourceAfter, targetAfter, sourceAllocated, targetAllocated, renamed,
    Nat.le_trans related.sourceBound mapping.allocate_extends.source,
    Nat.le_trans related.targetBound mapping.allocate_extends.target, ?_, ?_⟩
  · intro identity bound
    exact (mapping.allocate_extends.image identity
      (Nat.lt_of_lt_of_le bound related.sourceBound)).trans (related.fixed identity bound)
  · intro identity bound
    have sourceBound : identity < source.nextIdentity := by
      rw [← related.sourceLimit]
      exact Nat.lt_of_lt_of_le bound related.sourceBound
    have targetBound : identity < target.nextIdentity := by
      rw [← related.targetLimit]
      exact Nat.lt_of_lt_of_le bound related.targetBound
    rw [(allocate_extends_allocations _ _ _ _ targetAllocated).lookup identity targetBound,
      (allocate_extends_allocations _ _ _ _ sourceAllocated).lookup identity sourceBound,
      related.descriptors identity bound]
#print axioms Memory.RenamedBelow.allocate

/-- A target-only dead home is outside the exact caller prefix. -/
theorem Memory.RenamedBelow.skipTarget {watermark : Nat} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.RenamedBelow watermark mapping scopes source target)
    (formed : target.WellFormed) (descriptor : Allocation) (valid : descriptor.valid = true) :
    ∃ targetAfter, CIL.Safety.allocate target descriptor = .ok (target.nextIdentity, targetAfter) ∧
      Memory.RenamedBelow watermark mapping.skipTarget scopes source targetAfter := by
  obtain ⟨after, allocated, renamed⟩ := related.toRenamed.skipTarget formed descriptor valid
  refine ⟨after, allocated, renamed, related.sourceBound,
    Nat.le_trans related.targetBound mapping.skipTarget_extends.target, related.fixed, ?_⟩
  intro identity bound
  have targetBound : identity < target.nextIdentity := by
    rw [← related.targetLimit]
    exact Nat.lt_of_lt_of_le bound related.targetBound
  rw [(allocate_extends_allocations _ _ _ _ allocated).lookup identity targetBound,
    related.descriptors identity bound]
#print axioms Memory.RenamedBelow.skipTarget

end CIL.Safety
