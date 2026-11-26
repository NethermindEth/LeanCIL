import Reference
import CIL.Safety.ProfileContract
import CIL

/-! The low lane of CreateScalarUnsafe contains its argument. -/
namespace SavedSummary
open CIL CIL.Safety

/-- The low lane of CreateScalarUnsafe contains its argument. -/
def contract : MethodContract W64 W64 where
  args x := [.scalar (.i64 x)]
  results value := [.scalar (.i64 value)]
  pre _ _ := True
  footprint _ := []
  post x initial final value := value = x ∧ final = initial

/-- The vector calls of the entry and the intrinsics the runtime table runs for them. -/
def models : List ModelledCall :=
  [⟨.call, Extraction.createScalarUnsafeMethod, .intrinsic (.vector .createScalarUnsafe64) 1⟩,
    ⟨.call, Extraction.getElement128Method, .intrinsic (.vector (.extract64 128)) 2⟩]

/-- The compiled scalar entry satisfies the contract. -/
theorem checked :
    DecodedSummary Reference.program Reference.methodEvidence Reference.profile Reference.environment
      0 Reference.assembly0 Reference.method0Original.token [] models contract := by
  apply DecodedSummary.of_translation Reference.translation_valid ⟨0, by decide⟩
    Reference.program_method0 (listed := .of_sites [0] (by decide) (by decide) rfl)
  rintro x memory -
  refine MethodContract.Holds.intro memory x ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
  cil_checked_steps
#print axioms checked
end SavedSummary
