import CIL.Safety.MemoryRenaming
import CIL.Safety.ValueRenaming

/-!
# Typed view observations under renaming

Span and array checks preserve exact lengths, element types, offsets and lifetime
checks. Only the backing allocation identity changes.
-/

namespace CIL.Safety

/-- Span formation checks the same complete extent in corresponding allocations. -/
theorem Memory.Renamed.spanValidate {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : SpanView)
    (bound : view.reference.Below mapping.sourceLimit) :
    (mapping.spanView view).validate target = view.validate source := by
  obtain ⟨reference, length, width, writable⟩ := view
  cases reference with
  | null => rfl
  | address reference =>
    have allocations := related.allocations reference.allocation bound
    dsimp only [AllocationRenaming.spanView, AllocationRenaming.managedReference,
      AllocationRenaming.reference]
    unfold SpanView.validate liveAllocation
    dsimp only
    generalize sourceFound : source.allocations reference.allocation = sourceAllocation
      at allocations ⊢
    generalize targetFound : target.allocations (mapping.image reference.allocation) =
      targetAllocation at allocations ⊢
    cases allocations with
    | none => rfl
    | @some sourceDescriptor targetDescriptor descriptor =>
      dsimp only
      rw [← descriptor.live]
      cases sourceDescriptor.live <;>
        simp only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
          Bind.bind, Except.bind, Pure.pure, Except.pure, ← descriptor.layout]
#print axioms Memory.Renamed.spanValidate

/-- Array validation preserves nullness, element type and extent under renaming. -/
theorem Memory.Renamed.arrayValidate {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : ArrayView)
    (bound : view.reference.Below mapping.sourceLimit) :
    (mapping.arrayView view).validate target = view.validate source :=
  related.spanValidate view.storage bound
#print axioms Memory.Renamed.arrayValidate

/-- Snapshots retain both byte values and initialization flags across allocation renaming. -/
theorem Memory.Renamed.readSnapshot {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (reference : Reference)
    (bound : reference.allocation < mapping.sourceLimit) (width alignment : Nat) :
    readSnapshot target (mapping.reference reference) width alignment =
      readSnapshot source reference width alignment := by
  unfold CIL.Safety.readSnapshot
  rw [related.access reference bound]
  simp only [AllocationRenaming.reference, related.cells reference.allocation bound]
#print axioms Memory.Renamed.readSnapshot

end CIL.Safety
