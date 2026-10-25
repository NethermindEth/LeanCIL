import CIL.Safety.AllocationRenamingSteps
import CIL.Safety.MemoryRenamingOperations
import CIL.Safety.StaticWorld
import CIL.Safety.Frames

/-!
# Frame homes under allocation renaming

Corresponding homes extend the allocation map, while deleted target-only homes leave
the source image untouched. Activation labels are related separately from allocation
identities, including when a source activation allocated no homes.
-/

namespace CIL.Safety

/-- A valid static registry in well-formed memory contains no future allocation identity. -/
theorem StaticRegistryValid.bounded {memory : Memory} (registry : StaticRegistryValid memory)
    (formed : memory.WellFormed) :
    ∀ binding ∈ memory.staticBindings, binding.2.allocation < memory.nextIdentity := by
  intro binding member
  obtain ⟨allocation, present, _⟩ := registry.2 binding member
  exact (formed.1 _ _ present).1
#print axioms StaticRegistryValid.bounded

/-- Related activation homes allocate corresponding fresh storage and writable views. -/
theorem Memory.Renamed.allocateHome {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (sourceActivation targetActivation width alignment : Nat)
    (scope : scopes sourceActivation targetActivation)
    (bounded : width < nativeLimit) (positive : 0 < alignment) :
    ∃ sourceAfter targetAfter,
      allocateHome source sourceActivation width alignment =
        .ok (⟨source.nextIdentity, 0⟩, sourceAfter) ∧
      allocateHome target targetActivation width alignment =
        .ok (⟨target.nextIdentity, 0⟩, targetAfter) ∧
      Memory.Renamed mapping.allocate scopes sourceAfter targetAfter := by
  have descriptors : Allocation.Related scopes
      ⟨.frame sourceActivation, ⟨width, alignment, []⟩, true, [width]⟩
      ⟨.frame targetActivation, ⟨width, alignment, []⟩, true, [width]⟩ :=
    ⟨.frame scope, rfl, rfl, rfl⟩
  have valid : (Allocation.mk (.frame sourceActivation)
      ⟨width, alignment, []⟩ true [width]).valid = true := by
    simp [Allocation.valid, bounded, positive]
  obtain ⟨sourceAllocated, targetAllocated, sourceMade, targetMade, allocated⟩ :=
    related.allocate sourceFormed targetFormed staticBounds _ _ descriptors valid
  have freshBound : source.nextIdentity < mapping.allocate.sourceLimit := by
    change source.nextIdentity < mapping.sourceLimit + 1
    rw [related.sourceLimit]
    exact Nat.lt_succ_self _
  have freshImage : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
    rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
  refine ⟨{ sourceAllocated with
      views := ⟨source.nextIdentity, 0, width, true, true⟩ :: sourceAllocated.views },
    { targetAllocated with
      views := ⟨target.nextIdentity, 0, width, true, true⟩ :: targetAllocated.views }, ?_, ?_, ?_⟩
  · simp only [CIL.Safety.allocateHome, sourceMade, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp only [CIL.Safety.allocateHome, targetMade, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  simpa only [AllocationRenaming.view, freshImage] using
    allocated.prependView ⟨source.nextIdentity, 0, width, true, true⟩ freshBound
#print axioms Memory.Renamed.allocateHome

/-- A deleted target home gains only private writable authority outside the source image. -/
theorem Memory.Renamed.skipHome {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (formed : target.WellFormed)
    (activation width alignment : Nat) (bounded : width < nativeLimit)
    (positive : 0 < alignment) :
    ∃ targetAfter, CIL.Safety.allocateHome target activation width alignment =
      .ok (⟨target.nextIdentity, 0⟩, targetAfter) ∧
      Memory.Renamed mapping.skipTarget scopes source targetAfter := by
  have valid : (Allocation.mk (.frame activation)
      ⟨width, alignment, []⟩ true [width]).valid = true := by
    simp [Allocation.valid, bounded, positive]
  obtain ⟨allocated, made, remains⟩ := related.skipTarget formed _ valid
  refine ⟨{ allocated with
    views := ⟨target.nextIdentity, 0, width, true, true⟩ :: allocated.views }, ?_, ?_⟩
  · simp only [CIL.Safety.allocateHome, made, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply remains.prependPrivateView ⟨target.nextIdentity, 0, width, true, true⟩
  intro identity bound
  change target.nextIdentity ≠ mapping.image identity
  rw [← related.targetLimit]
  exact (Nat.ne_of_lt (mapping.bounded identity bound)).symm
#print axioms Memory.Renamed.skipHome

end CIL.Safety
