import CIL.Safety.SpanViews
import CIL.Safety.AllocationExtension

/-! # Checked span fills and preservation of extents under allocation extension -/

namespace CIL.Safety

/-- A nonempty fill performs one checked write of exactly the repeated element encoding. -/
theorem SpanView.fill_written (view : SpanView) (before after : Memory)
    (base : Reference) (element : List (BitVec 8))
    (address : view.reference = .address base) (nonempty : view.length ≠ 0)
    (filled : view.fill before element = .ok after) :
    Safety.write before base (List.replicate view.length element).flatten 1 = .ok after := by
  unfold SpanView.fill SpanView.fillWith at filled
  simp only [address, nonempty, beq_iff_eq, ite_false] at filled
  repeat' first
    | exact filled
    | cases filled
    | split at filled
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at filled
#print axioms SpanView.fill_written

/-- Span formation depends on allocation metadata, not cells or permissions. -/
theorem SpanView.validate_congr (view : SpanView) (before after : Memory)
    (same : before.allocations = after.allocations) :
    view.validate before = view.validate after := by
  simp only [SpanView.validate, liveAllocation, same]

/-- A valid span remains valid when existing allocation descriptors are unchanged. -/
theorem SpanView.validate_preserved (view : SpanView) {before after : Memory}
    (formed : view.validate before = .ok ()) (wellFormed : before.WellFormed)
    (extension : AllocationExtension before after) : view.validate after = .ok () := by
  cases reference : view.reference with
  | null => simpa only [SpanView.validate, reference] using formed
  | address address =>
    cases present : before.allocations address.allocation with
    | none =>
      simp only [SpanView.validate, reference, liveAllocation, present] at formed
      repeat' first
        | contradiction
        | split at formed
        | simp_all [Bind.bind, Except.bind, Pure.pure, Except.pure]
    | some allocation =>
      have same := extension.lookup address.allocation (wellFormed.1 _ _ present).1
      simpa only [SpanView.validate, reference, liveAllocation, same] using formed

#print axioms SpanView.validate_congr
#print axioms SpanView.validate_preserved

/-- Successful slicing retains a complete checked extent. -/
theorem SpanView.slice_valid (view result : SpanView) (memory : Memory) (start length : Nat)
    (sliced : view.slice memory start length = .ok result) : result.validate memory = .ok () := by
  unfold SpanView.slice at sliced
  repeat' first
    | assumption
    | cases sliced
    | split at sliced
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at sliced

/-- A successful element lookup yields a reference that forms in the same memory. -/
theorem SpanView.element_formed (view : SpanView) (memory : Memory) (index : Nat)
    (reference : Reference) (found : view.element memory index = .ok reference) :
    form memory reference = .ok reference := by
  unfold SpanView.element at found
  repeat' first
    | solve |
        have same := form_preserves_provenance _ _ _ found
        subst reference
        exact found
    | cases found
    | split at found
    | simp only [Bind.bind, Except.bind] at found

#print axioms SpanView.slice_valid
#print axioms SpanView.element_formed

end CIL.Safety
