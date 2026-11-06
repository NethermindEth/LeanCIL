import CIL.Safety.ArrayAllocationLemmas
import CIL.Safety.HeapObjects
import CIL.Safety.AllocationRenamingSteps
import CIL.Safety.MemoryRenamingOperations
import CIL.Safety.ValueRenaming

/-! # Fresh heap array and class instance identities under allocation renaming -/

namespace CIL.Safety

/-- Corresponding newly allocated payloads receive identical zero bytes and authority. -/
theorem Memory.Renamed.arrayMemory {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (identity size : Nat) (bound : identity < mapping.sourceLimit) :
    Memory.Renamed mapping scopes (arrayMemory source identity size)
      (arrayMemory target (mapping.image identity) size) := by
  have initialized : Memory.Renamed mapping scopes
      { source with cells := fun other offset =>
          if other == identity then ⟨0, true⟩ else source.cells other offset }
      { target with cells := fun other offset =>
          if other == mapping.image identity then ⟨0, true⟩ else target.cells other offset } := by
    refine ⟨related.sourceLimit, related.targetLimit, related.allocations, ?_,
      related.permissions, related.staticBindings, related.stackLimit, related.heapBudget⟩
    intro other otherBound offset
    have same : mapping.image other = mapping.image identity ↔ other = identity :=
      ⟨mapping.injective _ _ otherBound bound, congrArg mapping.image⟩
    simp only [beq_iff_eq, same]
    split <;> first | rfl | exact related.cells other otherBound offset
  exact initialized.prependView ⟨identity, 0, size, true, true⟩ bound

#print axioms Memory.Renamed.arrayMemory

/-- Successful heap allocation extends the existing allocation map exactly once. -/
theorem Memory.Renamed.allocateArray {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (element : CIL.ArrayElement) (length : Nat) (view : ArrayView) (sourceAfter : Memory)
    (success : allocateArray source element length = .ok (view, sourceAfter)) :
    ∃ targetAfter,
      allocateArray target element length = .ok (mapping.allocate.arrayView view, targetAfter) ∧
      Memory.Renamed mapping.allocate scopes sourceAfter targetAfter := by
  unfold CIL.Safety.allocateArray at success
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  split at success
  · cases success
  · rename_i supported
    split at success
    · cases success
    · rename_i bounded
      cases allocated : CIL.Safety.allocate source
          ⟨.managedHeap, ⟨length * element.width, element.allocationAlignment, []⟩, true,
            [length * element.width]⟩ with
      | error fault => simp [allocated, checkedAt, Except.mapError] at success
      | ok pair =>
        obtain ⟨identity, memory⟩ := pair
        have valid : (Allocation.mk .managedHeap
            ⟨length * element.width, element.allocationAlignment, []⟩ true
            [length * element.width]).valid = true := by
          unfold CIL.Safety.allocate at allocated
          split at allocated <;> first | cases allocated | simp_all
        obtain ⟨sourceMade, targetMade, sourceAllocated, targetAllocated, allocations⟩ :=
          related.allocate sourceFormed targetFormed staticBounds _ _ (.refl scopes _) valid
        rw [sourceAllocated] at allocated
        cases allocated
        simp only [sourceAllocated, checkedAt, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
        obtain ⟨rfl, rfl⟩ := success
        have fresh : source.nextIdentity < mapping.allocate.sourceLimit := by
          simp [AllocationRenaming.allocate, related.sourceLimit]
        have image : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
          rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
        refine ⟨CIL.Safety.arrayMemory targetMade target.nextIdentity
          (length * element.width), ?_, ?_⟩
        · simp [CIL.Safety.allocateArray, supported, bounded, targetAllocated, checkedAt,
            AllocationRenaming.arrayView, AllocationRenaming.managedReference,
            AllocationRenaming.reference, image, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        · simpa only [image] using allocations.arrayMemory source.nextIdentity
            (length * element.width) fresh

#print axioms Memory.Renamed.allocateArray

/-- Renamed memories stay renamed when both are given the same heap budget. -/
theorem Memory.Renamed.withHeapBudget {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (budget : Nat) :
    Memory.Renamed mapping scopes { source with heapBudget := budget }
      { target with heapBudget := budget } :=
  ⟨related.sourceLimit, related.targetLimit, related.allocations, related.cells,
    related.permissions, related.staticBindings, related.stackLimit, rfl⟩

#print axioms Memory.Renamed.withHeapBudget

/-- Successful object allocation extends the allocation map exactly once and charges the same
    budget on both sides. -/
theorem Memory.Renamed.allocateObject {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (type : RuntimeType) (size : Nat) (object : Reference) (sourceAfter : Memory)
    (success : allocateObject source type size = .ok (object, sourceAfter)) :
    ∃ targetAfter,
      allocateObject target type size = .ok (mapping.allocate.reference object, targetAfter) ∧
      Memory.Renamed mapping.allocate scopes sourceAfter targetAfter := by
  unfold CIL.Safety.allocateObject at success
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  split at success
  · cases success
  · rename_i affordable
    cases allocated : CIL.Safety.allocate source
        ⟨.object type, ⟨size, objectAlignment, []⟩, true, [size]⟩ with
    | error fault => simp [allocated, checkedAt, Except.mapError] at success
    | ok pair =>
      obtain ⟨identity, memory⟩ := pair
      have valid : (Allocation.mk (.object type) ⟨size, objectAlignment, []⟩ true
          [size]).valid = true := by
        unfold CIL.Safety.allocate at allocated
        split at allocated <;> first | cases allocated | simp_all
      obtain ⟨sourceMade, targetMade, sourceAllocated, targetAllocated, allocations⟩ :=
        related.allocate sourceFormed targetFormed staticBounds _ _ (.refl scopes _) valid
      rw [sourceAllocated] at allocated
      cases allocated
      simp only [sourceAllocated, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
      obtain ⟨rfl, rfl⟩ := success
      have fresh : source.nextIdentity < mapping.allocate.sourceLimit := by
        simp [AllocationRenaming.allocate, related.sourceLimit]
      have image : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
        rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
      refine ⟨{ CIL.Safety.arrayMemory targetMade target.nextIdentity size with
        heapBudget := source.heapBudget - size }, ?_, ?_⟩
      · simp [CIL.Safety.allocateObject, related.heapBudget, affordable, targetAllocated,
          checkedAt, AllocationRenaming.reference, image, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      · have renamed := allocations.arrayMemory source.nextIdentity size fresh
        rw [image] at renamed
        exact renamed.withHeapBudget _

#print axioms Memory.Renamed.allocateObject

end CIL.Safety
