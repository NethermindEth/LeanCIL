import CIL.Safety.ArrayViews
import CIL.Safety.SpanViewLemmas

/-! # Preservation of supplied array extents -/

namespace CIL.Safety

/-- A typed null array has no extent and needs no backing allocation. -/
theorem ArrayView.null_valid (element : CIL.ArrayElement) (memory : Memory)
    (width : 0 < element.width ∧ element.width < 2^64) :
    (ArrayView.mk .null 0 element).validate memory = .ok () := by
  simp [ArrayView.validate, ArrayView.storage, SpanView.validate, width, Pure.pure, Except.pure]

#print axioms ArrayView.null_valid

/-- Array formation observes allocation metadata, independently of contents and authority. -/
theorem ArrayView.validate_congr (view : ArrayView) (before after : Memory)
    (same : before.allocations = after.allocations) :
    view.validate before = view.validate after :=
  view.storage.validate_congr before after same

/-- Adding allocations preserves every already valid array extent. -/
theorem ArrayView.validate_preserved (view : ArrayView) {before after : Memory}
    (formed : view.validate before = .ok ()) (wellFormed : before.WellFormed)
    (extension : AllocationExtension before after) : view.validate after = .ok () :=
  view.storage.validate_preserved formed wellFormed extension

#print axioms ArrayView.validate_congr
#print axioms ArrayView.validate_preserved

/-- Successful element lookup returns a reference that forms in the same memory. -/
theorem ArrayView.element_formed (view : ArrayView) (memory : Memory) (index : Nat)
    (reference : Reference) (found : view.element memory index = .ok reference) :
    form memory reference = .ok reference := by
  unfold ArrayView.element at found
  repeat' first
    | exact view.storage.element_formed memory index reference found
    | cases found
    | split at found
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at found

#print axioms ArrayView.element_formed

end CIL.Safety
