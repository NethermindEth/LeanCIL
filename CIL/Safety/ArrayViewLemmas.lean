import CIL.Safety.ArrayViews
import CIL.Safety.SpanViewLemmas

/-! # Preservation of supplied array extents -/

namespace CIL.Safety

/-- A typed null array has no extent and needs no backing allocation. -/
theorem ArrayView.null_valid (element : CIL.ArrayElement) (memory : Memory) :
    (ArrayView.mk .null 0 element).validate memory = .ok () := by
  cases element <;> rfl

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

end CIL.Safety
