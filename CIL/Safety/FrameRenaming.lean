import CIL.Safety.LocalListRenaming

/-!
# Active frames under allocation renaming

Local operand relocation is separate from allocation and activation identities.
Suspended frames retain their correspondence when nested calls add mappings and scopes.
-/

namespace CIL.Safety

/-- A retained activation, including private dead homes. -/
structure Frame.Renamed (indices : LocalIndexMap) (mapping : AllocationRenaming)
    (scopes : Nat → Nat → Prop) (source target : Frame) : Prop where
  activation : scopes source.activation target.activation
  locals : indices.Selects (LocalSlot.Renamed mapping) source.locals target.locals
  owned : OwnedAllocations mapping source.owned target.owned
  stackBytes : target.stackBytes = source.stackBytes

/-- Nested calls can extend identity and scope correspondence without rewriting suspended frames. -/
theorem Frame.Renamed.extend {indices : LocalIndexMap} {earlier later : AllocationRenaming}
    {before after : Nat → Nat → Prop} {source target : Frame}
    (related : Frame.Renamed indices earlier before source target)
    (extension : earlier.Extends later)
    (scopeExtension : ∀ left right, before left right → after left right) :
    Frame.Renamed indices later after source target := by
  exact ⟨scopeExtension _ _ related.activation,
    related.locals.imp (fun _ _ slots => slots.extend extension),
    related.owned.extend extension, related.stackBytes⟩
#print axioms Frame.Renamed.extend

/-- Assignment to a retained local updates its relocated target operand. -/
theorem Frame.Renamed.setLocal {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Frame}
    (related : Frame.Renamed indices mapping scopes source target)
    (position : Nat) (bound : position < indices.sourceLength)
    (slot : LocalSlot) (slotBound : slot.Below mapping.sourceLimit) :
    Frame.Renamed indices mapping scopes
      { source with locals := source.locals.set position slot }
      { target with
        locals := target.locals.set (indices.index position) (mapping.localSlot slot) } :=
  ⟨related.activation, related.locals.set position bound slot _ ⟨slotBound, rfl⟩,
    related.owned, related.stackBytes⟩
#print axioms Frame.Renamed.setLocal

/-- A paired dynamic allocation adds corresponding ownership and the same quota charge. -/
theorem Frame.Renamed.addOwned {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Frame}
    (related : Frame.Renamed indices mapping scopes source target)
    (identity : AllocationId) (bound : identity < mapping.sourceLimit) (reserved : Nat) :
    Frame.Renamed indices mapping scopes
      { source with
        owned := identity :: source.owned
        stackBytes := source.stackBytes + reserved }
      { target with
        owned := mapping.image identity :: target.owned
        stackBytes := target.stackBytes + reserved } :=
  ⟨related.activation, related.locals, .keep identity bound related.owned,
    congrArg (· + reserved) related.stackBytes⟩
#print axioms Frame.Renamed.addOwned

end CIL.Safety
