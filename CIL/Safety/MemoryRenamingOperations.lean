import CIL.Safety.MemoryRenaming
import CIL.Safety.MemoryEquivalence

/-!
# Permission and lifetime operations under allocation renaming

Matched view grants preserve byte authority. Target-only private homes can acquire
views or expire without changing any observation on the mapped source allocations.
-/

namespace CIL.Safety

/-- Granting corresponding views preserves the memory relation. -/
theorem Memory.Renamed.prependView {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (view : View) (bound : view.allocation < mapping.sourceLimit) :
    Memory.Renamed mapping scopes { source with views := view :: source.views }
      { target with views := mapping.view view :: target.views } := by
  refine ⟨related.sourceLimit, related.targetLimit, related.allocations, related.cells, ?_,
    related.staticBindings, related.stackLimit⟩
  intro reference referenceBound writing
  change (viewContains (mapping.view view) (mapping.reference reference) &&
      (if writing then view.writable else view.readable) ||
      permitted target writing (mapping.reference reference)) =
    (viewContains view reference && (if writing then view.writable else view.readable) ||
      permitted source writing reference)
  rw [mapping.viewContains view reference bound referenceBound,
    related.permissions reference referenceBound writing]
#print axioms Memory.Renamed.prependView

/-- A view of a private target-only allocation grants no authority on the source image. -/
theorem Memory.Renamed.prependPrivateView {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target) (view : View)
    (privateView : ∀ identity, identity < mapping.sourceLimit →
      view.allocation ≠ mapping.image identity) :
    Memory.Renamed mapping scopes source { target with views := view :: target.views } := by
  refine ⟨related.sourceLimit, related.targetLimit, related.allocations, related.cells, ?_,
    related.staticBindings, related.stackLimit⟩
  intro reference bound writing
  have excluded : viewContains view (mapping.reference reference) = false := by
    simp [viewContains, AllocationRenaming.reference, privateView reference.allocation bound]
  change (viewContains view (mapping.reference reference) &&
      (if writing then view.writable else view.readable) ||
      permitted target writing (mapping.reference reference)) = permitted source writing reference
  simp only [excluded, Bool.false_and, Bool.false_or, related.permissions reference bound writing]
#print axioms Memory.Renamed.prependPrivateView

/-- Expiring corresponding owned allocations preserves lifetime observations on the image. -/
theorem Memory.Renamed.expire {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (identity : AllocationId) (bound : identity < mapping.sourceLimit) :
    Memory.Renamed mapping scopes (expire source identity)
      (expire target (mapping.image identity)) := by
  refine ⟨related.sourceLimit, related.targetLimit, ?_, related.cells, related.permissions,
    related.staticBindings, related.stackLimit⟩
  intro other otherBound
  have allocations := related.allocations other otherBound
  have identities : mapping.image other = mapping.image identity ↔ other = identity :=
    ⟨mapping.injective _ _ otherBound bound, congrArg mapping.image⟩
  simp only [CIL.Safety.expire, identities]
  by_cases same : other = identity
  · simp only [same, ite_true]
    subst other
    generalize sourceFound : source.allocations identity = sourceAllocation at allocations ⊢
    generalize targetFound : target.allocations (mapping.image identity) = targetAllocation
      at allocations ⊢
    cases allocations with
    | none => exact .none
    | some descriptor => exact .some descriptor.expire
  · simpa only [same, ite_false] using allocations
#print axioms Memory.Renamed.expire

/-- Expiring a private target-owned home cannot expire a corresponding source allocation. -/
theorem Memory.Renamed.expirePrivate {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (identity : AllocationId) (privateHome : ∀ other, other < mapping.sourceLimit →
      mapping.image other ≠ identity) :
    Memory.Renamed mapping scopes source (CIL.Safety.expire target identity) := by
  refine ⟨related.sourceLimit, related.targetLimit, ?_, related.cells, related.permissions,
    related.staticBindings, related.stackLimit⟩
  intro other bound
  simpa only [CIL.Safety.expire, privateHome other bound, ite_false]
    using related.allocations other bound
#print axioms Memory.Renamed.expirePrivate

/-- Checked writes to corresponding references preserve the memory relation. -/
theorem Memory.Renamed.write {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target : Memory} (related : Memory.Renamed mapping scopes source target)
    (reference : Reference) (bound : reference.allocation < mapping.sourceLimit)
    (bytes : List (BitVec 8)) (alignment : Nat) :
    ResultEquivalent (Memory.Renamed mapping scopes)
      (write source reference bytes alignment)
      (write target (mapping.reference reference) bytes alignment) := by
  unfold CIL.Safety.write
  rw [related.access reference bound]
  cases checked : CIL.Safety.access source reference bytes.length alignment true with
  | error fault => exact .error fault
  | ok value =>
    cases value
    apply ResultEquivalent.ok
    refine ⟨related.sourceLimit, related.targetLimit, related.allocations, ?_, ?_,
      related.staticBindings, related.stackLimit⟩
    · intro identity identityBound offset
      have identities : mapping.image identity = mapping.image reference.allocation ↔
          identity = reference.allocation :=
        ⟨mapping.injective _ _ identityBound bound, congrArg mapping.image⟩
      simp only [AllocationRenaming.reference, identities, related.cells identity identityBound]
    · intro queried queryBound writing
      change permitted { target with views := (writeViews target
          (mapping.reference reference) bytes.length) } writing (mapping.reference queried) =
        permitted { source with views := writeViews source reference bytes.length } writing queried
      rw [writeViews_permitted, writeViews_permitted]
      exact (related.prependView
        ⟨reference.allocation, reference.offset, bytes.length, true, false⟩ bound).permissions
          queried queryBound writing
#print axioms Memory.Renamed.write

/-- Initializing a target-only private home changes no mapped source byte or permission. -/
theorem Memory.Renamed.writePrivate {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
    {source target after : Memory} (related : Memory.Renamed mapping scopes source target)
    (reference : Reference) (privateHome : ∀ identity, identity < mapping.sourceLimit →
      mapping.image identity ≠ reference.allocation)
    (bytes : List (BitVec 8)) (alignment : Nat)
    (written : CIL.Safety.write target reference bytes alignment = .ok after) :
    Memory.Renamed mapping scopes source after := by
  unfold CIL.Safety.write at written
  cases checked : CIL.Safety.access target reference bytes.length alignment true with
  | error fault => simp only [checked, Bind.bind, Except.bind] at written; cases written
  | ok value =>
    cases value
    simp only [checked, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at written
    subst after
    refine ⟨related.sourceLimit, related.targetLimit, related.allocations, ?_, ?_,
      related.staticBindings, related.stackLimit⟩
    · intro identity bound offset
      simp only [privateHome identity bound, false_and, ite_false]
      exact related.cells identity bound offset
    · intro queried queryBound writing
      change permitted { target with views := writeViews target reference bytes.length }
          writing (mapping.reference queried) = permitted source writing queried
      rw [writeViews_permitted]
      exact (related.prependPrivateView
        ⟨reference.allocation, reference.offset, bytes.length, true, false⟩
        (fun identity bound => (privateHome identity bound).symm)).permissions
          queried queryBound writing
#print axioms Memory.Renamed.writePrivate
end CIL.Safety
