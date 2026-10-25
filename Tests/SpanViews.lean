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

end Tests.SpanViews
