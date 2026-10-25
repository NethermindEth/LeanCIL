import Reference
import FamilyContract
import CIL.Safety.ProfileContract
import CIL.Safety.SymbolicExecution

/-! One compiled reference extraction and one family proof serve every agreeing export profile. -/
namespace FamilyProof
open CIL CIL.Safety

/-- The reference extraction's methods all use the selected SSE2 profile. -/
theorem uniform : ∀ body ∈ Reference.program, body.profile = Reference.profile := by decide
#print axioms uniform

/-- The only proof that executes the extracted body. -/
theorem reference_holds : FamilyContract.supported.Holds Reference.program 0 := by
  rintro _ memory _
  refine ⟨10, memory, [.scalar (.i32 1)], ?_, Confined.refl _ memory, _, rfl, rfl⟩
  cil_checked_steps [Reference.program, Reference.profile]
  all_goals rfl
#print axioms reference_holds

/-- The one export theorem covers any agreeing profile, including all three selected profiles. -/
theorem family (profile : FeatureProfile)
    (agreement : ∀ feature ∈ Reference.program.profileReads,
      Reference.profile.evaluate feature = profile.evaluate feature) :
    FamilyContract.supported.Holds (reprofile Reference.program profile) 0 :=
  reference_holds.reprofile Reference.profile uniform
    (Program.ProfileAgreement.of_flags _ _ _ agreement)
#print axioms family

/-- Outcome families use the same checked profile binding. -/
theorem outcomeFamily (profile : FeatureProfile)
    (agreement : ∀ feature ∈ Reference.program.profileReads,
      Reference.profile.evaluate feature = profile.evaluate feature) :
    FamilyContract.outcome.Holds (reprofile Reference.program profile) 0 :=
  (family profile agreement).outcomes
#print axioms outcomeFamily

end FamilyProof
