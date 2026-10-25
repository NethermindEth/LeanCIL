import CIL.Safety.AllocationScopes

/-!
# Memory observations under allocation renaming

The relation matches allocated source identities with target identities while allowing
additional target allocations. Cells, permissions, geometry and lifetime checks agree
on the image; frame labels retain an explicit scope correspondence.
-/

namespace CIL.Safety

/-- Memory observations agree on the image of an allocation map. -/
structure Memory.Renamed (mapping : AllocationRenaming) (scopes : Nat → Nat → Prop)
    (source target : Memory) : Prop where
  sourceLimit : mapping.sourceLimit = source.nextIdentity
  targetLimit : mapping.targetLimit = target.nextIdentity
  allocations : ∀ identity, identity < mapping.sourceLimit →
    Option.Rel (Allocation.Related scopes) (source.allocations identity)
      (target.allocations (mapping.image identity))
  cells : ∀ identity, identity < mapping.sourceLimit → ∀ offset,
    target.cells (mapping.image identity) offset = source.cells identity offset
  permissions : ∀ reference, reference.allocation < mapping.sourceLimit → ∀ writing,
    permitted target writing (mapping.reference reference) = permitted source writing reference
  staticBindings : target.staticBindings = source.staticBindings.map
    (fun binding => (binding.1, mapping.reference binding.2))
  stackLimit : target.stackLimit = source.stackLimit

/-- Identical caller memory is related by the initial identity map. -/
theorem Memory.Renamed.refl (memory : Memory) (scopes : Nat → Nat → Prop) :
    Memory.Renamed (.identity memory.nextIdentity) scopes memory memory := by
  refine ⟨rfl, rfl, ?_, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, rfl⟩
  · intro identity _
    change Option.Rel (Allocation.Related scopes) (memory.allocations identity)
      (memory.allocations identity)
    cases memory.allocations identity with
    | none => exact .none
    | some allocation => exact .some (Allocation.Related.refl scopes allocation)
  · simp [AllocationRenaming.reference, AllocationRenaming.identity]
#print axioms Memory.Renamed.refl

/-- Reference formation preserves its result after mapping an allocated identity. -/
theorem Memory.Renamed.form {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (reference : Reference) (bound : reference.allocation < mapping.sourceLimit) :
    form target (mapping.reference reference) = (form source reference).map mapping.reference := by
  have allocations := related.allocations reference.allocation bound
  unfold CIL.Safety.form liveAllocation
  simp only [AllocationRenaming.reference]
  generalize sourceFound : source.allocations reference.allocation = sourceAllocation
    at allocations ⊢
  generalize targetFound : target.allocations (mapping.image reference.allocation) =
    targetAllocation at allocations ⊢
  cases allocations with
  | none => rfl
  | some descriptor =>
    dsimp only
    rw [← descriptor.live]
    split <;> simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
    simp only [← descriptor.validPosition reference.offset]
    split <;> rfl
#print axioms Memory.Renamed.form

/-- Access checks agree for corresponding references, including writable static restrictions. -/
theorem Memory.Renamed.access {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (reference : Reference) (bound : reference.allocation < mapping.sourceLimit)
    (width alignment : Nat) (writing : Bool) :
    access target (mapping.reference reference) width alignment writing =
      access source reference width alignment writing := by
  unfold CIL.Safety.access
  rw [related.form reference bound]
  cases formed : CIL.Safety.form source reference with
  | error fault => simp only [Except.map, Bind.bind, Except.bind]
  | ok value =>
    simp only [Except.map, Bind.bind, Except.bind]
    have allocations := related.allocations reference.allocation bound
    have permissions : ∀ offset,
        permitted target writing ⟨mapping.image reference.allocation, offset⟩ =
          permitted source writing ⟨reference.allocation, offset⟩ :=
      fun offset => related.permissions ⟨reference.allocation, offset⟩ bound writing
    unfold liveAllocation
    simp only [AllocationRenaming.reference]
    generalize sourceFound : source.allocations reference.allocation = sourceAllocation
      at allocations ⊢
    generalize targetFound : target.allocations (mapping.image reference.allocation) =
      targetAllocation at allocations ⊢
    cases allocations with
    | none => rfl
    | @some sourceDescriptor targetDescriptor descriptor =>
      have immutable : targetDescriptor.kind = .immutableStatic ↔
          sourceDescriptor.kind = .immutableStatic := by
        have equal : (targetDescriptor.kind == .immutableStatic) = true ↔
            (sourceDescriptor.kind == .immutableStatic) = true := by
          rw [descriptor.kind.immutable]
        simpa only [beq_iff_eq] using equal
      dsimp only
      simp only [← descriptor.live]
      cases live : sourceDescriptor.live <;>
        simp [Pure.pure, Except.pure, ← descriptor.layout, immutable, permissions]
      all_goals simp only [← descriptor.layout]
      all_goals rfl
#print axioms Memory.Renamed.access

/-- Reading corresponding storage returns exactly the same bytes. -/
theorem Memory.Renamed.read {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (reference : Reference) (bound : reference.allocation < mapping.sourceLimit)
    (width alignment : Nat) :
    read target (mapping.reference reference) width alignment =
      read source reference width alignment := by
  unfold CIL.Safety.read
  rw [related.access reference bound width alignment false]
  simp only [AllocationRenaming.reference, related.cells reference.allocation bound]
#print axioms Memory.Renamed.read
/-- Adding activation correspondences retains the observations of suspended frames. -/
theorem Memory.Renamed.extendScopes {mapping : AllocationRenaming}
    {before after : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping before source target)
    (extension : ∀ left right, before left right → after left right) :
    Memory.Renamed mapping after source target := by
  refine ⟨related.sourceLimit, related.targetLimit, ?_, related.cells, related.permissions,
    related.staticBindings, related.stackLimit⟩
  intro identity bound
  have lift : ∀ left right, Option.Rel (Allocation.Related before) left right →
      Option.Rel (Allocation.Related after) left right := by
    intro left right allocations
    cases allocations with
    | none => exact .none
    | some descriptor => exact .some (descriptor.extend extension)
  exact lift _ _ (related.allocations identity bound)
#print axioms Memory.Renamed.extendScopes
end CIL.Safety
