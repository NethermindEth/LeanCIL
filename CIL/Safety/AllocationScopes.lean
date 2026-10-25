import CIL.Safety.AllocationRenaming

/-!
# Allocation descriptors under frame-scope correspondence

Allocation identities and activation labels have different lifetimes. A scope relation
records corresponding activations without requiring a global function: an empty source
frame and its child can share an activation label while their padded targets do not.
-/

namespace CIL.Safety

/-- Storage classes agree, with frame labels justified by the current scope correspondence. -/
inductive StorageKind.Related (scopes : Nat → Nat → Prop) : StorageKind → StorageKind → Prop where
  | same (kind : StorageKind) : Related scopes kind kind
  | frame {source target : Nat} (scope : scopes source target) :
      Related scopes (.frame source) (.frame target)

/-- Corresponding storage classes give the same immutable-storage check. -/
theorem StorageKind.Related.immutable {scopes : Nat → Nat → Prop} {source target : StorageKind}
    (related : StorageKind.Related scopes source target) :
    (source == .immutableStatic) = (target == .immutableStatic) := by
  cases related <;> rfl
#print axioms StorageKind.Related.immutable

/-- Extending the active scope relation preserves earlier storage correspondences. -/
theorem StorageKind.Related.extend {before after : Nat → Nat → Prop}
    (extension : ∀ source target, before source target → after source target)
    {source target : StorageKind} (related : StorageKind.Related before source target) :
    StorageKind.Related after source target := by
  cases related with
  | same => exact .same _
  | frame scope => exact .frame (extension _ _ scope)
#print axioms StorageKind.Related.extend

/-- Related allocation descriptors retain all observable geometry and lifetime information. -/
structure Allocation.Related (scopes : Nat → Nat → Prop) (source target : Allocation) : Prop where
  kind : StorageKind.Related scopes source.kind target.kind
  layout : source.layout = target.layout
  live : source.live = target.live
  sentinels : source.sentinels = target.sentinels

/-- Identical allocation descriptors are related for any scope relation. -/
theorem Allocation.Related.refl (scopes : Nat → Nat → Prop) (allocation : Allocation) :
    Allocation.Related scopes allocation allocation := ⟨.same _, rfl, rfl, rfl⟩
#print axioms Allocation.Related.refl

/-- The allocation validity check is independent of related frame activation labels. -/
theorem Allocation.Related.valid {scopes : Nat → Nat → Prop} {source target : Allocation}
    (related : Allocation.Related scopes source target) : source.valid = target.valid := by
  simp only [Allocation.valid, related.layout, related.sentinels]
#print axioms Allocation.Related.valid

/-- Related allocation descriptors admit exactly the same offsets and sentinels. -/
theorem Allocation.Related.validPosition {scopes : Nat → Nat → Prop}
    {source target : Allocation} (related : Allocation.Related scopes source target)
    (offset : Nat) :
    validPosition source offset = validPosition target offset := by
  simp only [CIL.Safety.validPosition, related.layout, related.sentinels]
#print axioms Allocation.Related.validPosition

/-- Expiration changes the lifetime flag on both related allocation descriptors. -/
theorem Allocation.Related.expire {scopes : Nat → Nat → Prop} {source target : Allocation}
    (related : Allocation.Related scopes source target) :
    Allocation.Related scopes { source with live := false } { target with live := false } :=
  ⟨related.kind, related.layout, rfl, related.sentinels⟩
#print axioms Allocation.Related.expire

/-- Adding an activation pair preserves the allocation correspondences of suspended callers. -/
theorem Allocation.Related.extend {before after : Nat → Nat → Prop}
    (extension : ∀ source target, before source target → after source target)
    {source target : Allocation} (related : Allocation.Related before source target) :
    Allocation.Related after source target :=
  ⟨related.kind.extend extension, related.layout, related.live, related.sentinels⟩
#print axioms Allocation.Related.extend

end CIL.Safety
