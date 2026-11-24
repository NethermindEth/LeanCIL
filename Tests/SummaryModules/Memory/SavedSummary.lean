import Reference
import CIL.Safety.ProfileContract
import CIL

/-! Mutate increases the referenced word by two and confines its write to that word. -/
namespace SavedSummary
open CIL CIL.Safety

/-- Mutate increases the referenced word by two and confines its write to that word. -/
def contract : MethodContract (Reference × W64) Unit where
  args := fun (place, _) => [.reference (.address place)]
  results _ := []
  pre := fun (place, old) memory => access memory place 8 1 true = .ok () ∧
    read memory place 8 1 = .ok (numberBytes old.toNat 8)
  footprint := fun (place, _) => [(place, 8)]
  post := fun (place, old) _ final _ =>
    read final place 8 1 = .ok (numberBytes (old + 2).toNat 8)

/-- The entry calls no runtime-modelled method, so its summary relies on no runtime model. -/
def models : List ModelledCall := []

/-- The compiled scalar entry satisfies the contract. -/
theorem checked :
    DecodedSummary Reference.program Reference.methodEvidence Reference.profile Reference.environment
      0 Reference.assembly0 Reference.method0Original.token [] models contract := by
  apply DecodedSummary.of_translation Reference.translation_valid ⟨0, by decide⟩
    Reference.program_method0 (listed := .of_sites [0] (by decide) (by decide) rfl)
  rintro ⟨place, old⟩ memory ⟨ready, loaded⟩
  obtain ⟨final, written, stored, readback⟩ := store_word64 (old + 2) ready
  refine MethodContract.Holds.intro final () ?_
    (Confined.write written (by simp [contract])) readback
  cil_checked_steps [loaded, stored, access_reference_valid _ _ _ _ _ ready,
    checkedValue_address _ _ (access_reference_valid _ _ _ _ _ ready)]
#print axioms checked
end SavedSummary
