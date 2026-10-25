import CIL.Safety.LocalSlotRenaming
import CIL.Safety.MemoryRenamingOperations

/-!
# Activation exit under allocation renaming

An activation owns corresponding retained homes interleaved with target-only dead homes.
Returning expires both lists. Private homes remain outside the source image even after
nested calls extend the allocation map.
-/

namespace CIL.Safety

/-- Corresponding owned allocations, with private target homes allowed at any position. -/
inductive OwnedAllocations (mapping : AllocationRenaming) :
    List AllocationId → List AllocationId → Prop
  | nil : OwnedAllocations mapping [] []
  | keep {source target} (identity : AllocationId) (bound : identity < mapping.sourceLimit)
      (rest : OwnedAllocations mapping source target) :
      OwnedAllocations mapping (identity :: source) (mapping.image identity :: target)
  | privateHome {source target} (identity : AllocationId)
      (bound : identity < mapping.targetLimit)
      (privateIdentity : ∀ sourceIdentity, sourceIdentity < mapping.sourceLimit →
        mapping.image sourceIdentity ≠ identity)
      (rest : OwnedAllocations mapping source target) :
      OwnedAllocations mapping source (identity :: target)

/-- Suspended frame ownership remains valid when nested calls allocate more storage. -/
theorem OwnedAllocations.extend {earlier later : AllocationRenaming}
    (extension : earlier.Extends later) {source target : List AllocationId}
    (owned : OwnedAllocations earlier source target) : OwnedAllocations later source target := by
  induction owned with
  | nil => exact .nil
  | keep identity bound rest induction =>
    rw [← extension.image identity bound]
    exact .keep identity (Nat.lt_of_lt_of_le bound extension.source) induction
  | privateHome identity bound privateIdentity rest induction =>
    exact .privateHome identity (Nat.lt_of_lt_of_le bound extension.target)
      (extension.private identity bound privateIdentity) induction
#print axioms OwnedAllocations.extend

/-- Exact mapped ownership lists have no private target entries. -/
theorem OwnedAllocations.mapped (mapping : AllocationRenaming) (owned : List AllocationId)
    (bounds : ∀ identity ∈ owned, identity < mapping.sourceLimit) :
    OwnedAllocations mapping owned (owned.map mapping.image) := by
  induction owned with
  | nil => exact .nil
  | cons identity rest induction =>
    exact .keep identity (bounds identity List.mem_cons_self)
      (induction fun other member => bounds other (List.mem_cons_of_mem _ member))
#print axioms OwnedAllocations.mapped

/-- Private target ownership lists contain no mapped source allocation. -/
theorem OwnedAllocations.privateList (mapping : AllocationRenaming) (owned : List AllocationId)
    (privateOwned : ∀ identity ∈ owned, identity < mapping.targetLimit ∧
      ∀ sourceIdentity, sourceIdentity < mapping.sourceLimit →
        mapping.image sourceIdentity ≠ identity) : OwnedAllocations mapping [] owned := by
  induction owned with
  | nil => exact .nil
  | cons identity rest induction =>
    obtain ⟨bound, privateIdentity⟩ := privateOwned identity List.mem_cons_self
    exact .privateHome identity bound privateIdentity
      (induction fun other member => privateOwned other (List.mem_cons_of_mem _ member))
#print axioms OwnedAllocations.privateList

/-- Sequential frame builders concatenate corresponding ownership lists. -/
theorem OwnedAllocations.append {mapping : AllocationRenaming}
    {sourceFirst targetFirst sourceRest targetRest : List AllocationId}
    (first : OwnedAllocations mapping sourceFirst targetFirst)
    (rest : OwnedAllocations mapping sourceRest targetRest) :
    OwnedAllocations mapping (sourceFirst ++ sourceRest) (targetFirst ++ targetRest) := by
  induction first with
  | nil => exact rest
  | keep identity bound tail induction => exact .keep identity bound induction
  | privateHome identity bound privateIdentity tail induction =>
    exact .privateHome identity bound privateIdentity induction
#print axioms OwnedAllocations.append

/-- Expiring corresponding owned lists also expires all private dead homes safely. -/
theorem Memory.Renamed.expireOwned {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    {sourceOwned targetOwned : List AllocationId}
    (owned : OwnedAllocations mapping sourceOwned targetOwned) :
    Memory.Renamed mapping scopes (sourceOwned.foldl CIL.Safety.expire source)
      (targetOwned.foldl CIL.Safety.expire target) := by
  induction owned generalizing source target with
  | nil => exact related
  | keep identity bound rest induction =>
    exact induction (related.expire identity bound)
  | privateHome identity bound privateIdentity rest induction =>
    exact induction (related.expirePrivate identity privateIdentity)
#print axioms Memory.Renamed.expireOwned

/-- Returning from related activations preserves the memory relation after both frame exits. -/
theorem Memory.Renamed.leaveFrame {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (sourceFrame targetFrame : Frame)
    (owned : OwnedAllocations mapping sourceFrame.owned targetFrame.owned) :
    Memory.Renamed mapping scopes (leaveFrame sourceFrame source)
      (leaveFrame targetFrame target) := related.expireOwned owned
#print axioms Memory.Renamed.leaveFrame

end CIL.Safety
