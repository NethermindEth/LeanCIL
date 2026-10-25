import CIL.Safety.Execution
import CIL.Extraction.Scalars

/-! # Reference observations without byte access authority -/

namespace Tests.ReferenceTests
open CIL.Safety

private def memory : Memory := {
  allocations := fun identity => if identity < 2 then
    some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, false⟩
  views := []
  nextIdentity := 2 }

/-- Null is false in a reference truth test. -/
theorem null_is_false : referenceNonNull memory .null = .ok false := rfl
#print axioms null_is_false

/-- An interior reference can be observed even without read authority or initialized bytes. -/
theorem interior_is_true : referenceNonNull memory (.address ⟨0, 3⟩) = .ok true := rfl
#print axioms interior_is_true

/-- Equality uses the offset within a live allocation. -/
theorem same_position_equal :
    referenceEqual memory (.address ⟨0, 3⟩) (.address ⟨0, 3⟩) = .ok true := rfl
#print axioms same_position_equal

/-- Distinct positions within one allocation are unequal. -/
theorem different_positions_unequal :
    referenceEqual memory (.address ⟨0, 3⟩) (.address ⟨0, 4⟩) = .ok false := rfl
#print axioms different_positions_unequal

/-- Interiors of distinct admitted allocations cannot alias. -/
theorem different_interiors_unequal :
    referenceEqual memory (.address ⟨0, 3⟩) (.address ⟨1, 3⟩) = .ok false := rfl
#print axioms different_interiors_unequal

/-- A valid end sentinel remains comparable within its own allocation. -/
theorem same_end_equal :
    referenceEqual memory (.address ⟨0, 8⟩) (.address ⟨0, 8⟩) = .ok true := rfl
#print axioms same_end_equal

/-- End and start addresses across allocations are not assumed unequal. -/
theorem cross_allocation_end_rejected :
    referenceEqual memory (.address ⟨0, 8⟩) (.address ⟨1, 0⟩) =
      .error (.unsupported "Cross-allocation end-pointer comparison") := rfl
#print axioms cross_allocation_end_rejected

/-- Null tests do not revive expired storage. -/
theorem expired_reference_rejected :
    referenceNonNull { memory with
      allocations := fun _ => some ⟨.callerStack, ⟨8, 1, []⟩, false, []⟩ }
      (.address ⟨0, 0⟩) =
      .error (.memory .expiredLifetime (.address ⟨0, 0⟩) 0) := rfl
#print axioms expired_reference_rejected

/-- Equality validates addresses even when their representations are identical. -/
theorem invalid_self_comparison_rejected :
    referenceEqual memory (.address ⟨0, 9⟩) (.address ⟨0, 9⟩) =
      .error (.memory .invalidReference (.address ⟨0, 9⟩) 0) := rfl
#print axioms invalid_self_comparison_rejected

/-- Observing a readonly reference does not turn its stored value into a writable reference. -/
theorem readonly_reference_observed :
    Value.referenceValue (.readOnlyReference (.address ⟨0, 0⟩)) = some (.address ⟨0, 0⟩) := rfl
#print axioms readonly_reference_observed

private def compare : CIL.Method := {
  code := [.arg 0, .arg 1, .eq, .ret], locals := [], returnsValue := true }

/-- Compiled equality observes readonly and writable views without changing memory. -/
theorem mixed_capability_equality :
    invoke [compare] 8 0 [.readOnlyReference (.address ⟨0, 3⟩),
      .reference (.address ⟨0, 3⟩)] memory = .ok (memory, [.scalar (.i32 1)]) := rfl
#print axioms mixed_capability_equality

private def branch (operation : CIL.Op) : CIL.Method := {
  code := [.arg 0, operation, .const32 0, .ret, .const32 1, .ret]
  locals := [], returnsValue := true }

/-- Null reference branches select the zero arm. -/
theorem null_branch :
    invoke [branch (.brzero 4)] 8 0 [.reference .null] memory =
      .ok (memory, [.scalar (.i32 1)]) := rfl
#print axioms null_branch

/-- Non-null readonly references select the nonzero arm without byte access authority. -/
theorem readonly_branch :
    invoke [branch (.brnonzero 4)] 8 0 [.readOnlyReference (.address ⟨0, 3⟩)] memory =
      .ok (memory, [.scalar (.i32 1)]) := rfl
#print axioms readonly_branch

private def compareBranch (operation : CIL.Op) : CIL.Method := {
  code := [.arg 0, .arg 1, operation, .const32 0, .ret, .const32 1, .ret]
  locals := [], returnsValue := true }

/-- Equality branches use the same checked comparison as ceq. -/
theorem reference_beq :
    invoke [compareBranch (.beq 5)] 9 0
      [.reference (.address ⟨0, 3⟩), .readOnlyReference (.address ⟨0, 3⟩)] memory =
      .ok (memory, [.scalar (.i32 1)]) := rfl
#print axioms reference_beq

/-- Inequality branches distinguish two positions within the same allocation. -/
theorem reference_bne :
    invoke [compareBranch (.bne 5)] 9 0
      [.reference (.address ⟨0, 3⟩), .reference (.address ⟨0, 4⟩)] memory =
      .ok (memory, [.scalar (.i32 1)]) := rfl
#print axioms reference_bne

/-- Existing numeric equality still follows scalar semantics. -/
theorem scalar_equality_unchanged :
    invoke [compare] 8 0 [.scalar (.i32 3), .scalar (.i32 4)] memory =
      .ok (memory, [.scalar (.i32 0)]) := rfl
#print axioms scalar_equality_unchanged

/-- An object null cannot serve as a metadata-proven managed reference in a comparison. -/
theorem object_null_pointer_mix_rejected :
    CIL.Extraction.scalarOpMatches ⟨0, 65025, .none⟩ [.reference, .nullObject] .eq = false :=
  by decide +kernel
#print axioms object_null_pointer_mix_rejected

/-- The equality certificate checks the operation, not just its stack effect. -/
theorem changed_reference_comparison_rejected :
    CIL.Extraction.scalarOpMatches ⟨0, 65025, .none⟩ [.reference, .reference] .lt = false :=
  by decide +kernel
#print axioms changed_reference_comparison_rejected

/-- The null literal cannot be replaced by a numeric zero with the same stack effect. -/
theorem numeric_null_forgery_rejected :
    CIL.Extraction.scalarOpMatches ⟨0, 20, .none⟩ [] (.const32 0) = false := by decide +kernel
#print axioms numeric_null_forgery_rejected

/-- The truth-branch certificate binds the original target. -/
theorem changed_reference_branch_rejected :
    CIL.Extraction.scalarOpMatches ⟨0, 45, .target 4⟩ [.reference] (.brnonzero 3) = false :=
  by decide +kernel
#print axioms changed_reference_branch_rejected

end Tests.ReferenceTests
