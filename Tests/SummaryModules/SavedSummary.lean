import Reference
import CIL.Safety.ProfileContract

/-! A decoded summary for the compiled unsigned word addition. -/
namespace SavedSummary
open CIL CIL.Safety

/-- Addition returns the wrapping sum and preserves the caller's memory. -/
def contract : MethodContract (W64 × W64) W64 where
  args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
  results value := [.scalar (.i64 value)]
  pre _ _ := True
  footprint _ := []
  post input before after value := after = before ∧ value = input.1 + input.2

/-- The saved proof binds the addition contract to its definition and body in the scalar image. -/
theorem checked :
    DecodedSummary Reference.program Reference.methodEvidence Reference.profile Reference.environment
      0 Reference.assembly0 Reference.method0Original.token [] contract := by
  apply DecodedSummary.of_translation Reference.translation_valid ⟨0, by decide⟩ Reference.program_method0
  rintro ⟨left, right⟩ memory -
  apply MethodContract.Holds.intro (c := contract) (input := (left, right)) memory
    (left + right) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
  exact ⟨8, rfl⟩
#print axioms checked
end SavedSummary
