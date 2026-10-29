import CIL.Safety.SpanViews

/-! # Primitive span bounds, authority and aliasing regressions -/

namespace Tests.SpanViews
open CIL.Safety

private def memory : Memory := {
  allocations := fun identity => if identity == 0 then
    some ⟨.callerStack, ⟨16, 1, []⟩, true, []⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 1 }

private def view : SpanView := ⟨.address ⟨0, 0⟩, 4, 4, true⟩

theorem empty_at_end : (view.slice memory 4 0).map (fun slice => slice.reference) =
    .ok (.address ⟨0, 16⟩) := rfl
#print axioms empty_at_end

theorem invalid_ranges : view.slice memory 5 0 = .error .outsideAllocation ∧
    view.slice memory 3 2 = .error .outsideAllocation ∧
    view.element memory 4 = .error .outsideAllocation := ⟨rfl, rfl, rfl⟩
#print axioms invalid_ranges

theorem readonly_observes_alias :
    (do let updated ← view.write memory 1 [1, 2, 3, 4]
        view.asReadOnly.read updated 1) = .ok [1, 2, 3, 4] := rfl
#print axioms readonly_observes_alias

theorem readonly_rejects_write :
    view.asReadOnly.write memory 0 [0, 0, 0, 0] = .error .unwritable := rfl
#print axioms readonly_rejects_write

theorem writable_view_grants_no_authority :
    view.write { memory with views := [⟨0, 0, 16, true, false⟩] } 0 [0, 0, 0, 0] =
      .error .unwritable := rfl
#print axioms writable_view_grants_no_authority

theorem unwritten_contents_not_readable :
    view.read { memory with cells := fun _ _ => ⟨0, false⟩ } 0 = .error .uninitialized := rfl
#print axioms unwritten_contents_not_readable

theorem expired_span_rejected :
    view.validate (expire memory 0) = .error .expiredLifetime := rfl
#print axioms expired_span_rejected

/-- Whole-view fills initialize unreadable bytes and leave adjacent storage unchanged. -/
theorem fill_initializes_slice :
    (do let slice ← view.slice memory 1 2
        let filled ← slice.fill { memory with
          cells := fun _ _ => ⟨99, false⟩
          views := [⟨0, 0, 16, false, true⟩] } [1, 2, 3, 4]
        let first ← slice.read filled 0
        let last ← slice.read filled 1
        pure (first, last, filled.cells 0 3, filled.cells 0 12)) =
      .ok ([1, 2, 3, 4], [1, 2, 3, 4], ⟨99, false⟩, ⟨99, false⟩) := rfl
#print axioms fill_initializes_slice

/-- Empty null and end-position views do not demand byte access authority. -/
theorem fill_empty_views :
    (SpanView.mk .null 0 4 true).fill { memory with views := [] } [0, 0, 0, 0] =
      .ok { memory with views := [] } ∧
    (SpanView.mk (.address ⟨0, 16⟩) 0 4 true).fill { memory with views := [] } [0, 0, 0, 0] =
      .ok { memory with views := [] } := ⟨rfl, rfl⟩
#print axioms fill_empty_views

/-- Filling never bypasses view mutability, byte authority, lifetime or extent validation. -/
theorem fill_rejects_invalid_access :
    view.asReadOnly.fill memory [0, 0, 0, 0] = .error .unwritable ∧
    view.fill { memory with views := [] } [0, 0, 0, 0] = .error .unwritable ∧
    view.fill (expire memory 0) [0, 0, 0, 0] = .error .expiredLifetime ∧
    { view with length := 5 }.fill memory [0, 0, 0, 0] = .error .outsideAllocation ∧
    view.fill memory [0] = .error .unsupportedLayout := ⟨rfl, rfl, rfl, rfl, rfl⟩
#print axioms fill_rejects_invalid_access

end Tests.SpanViews
