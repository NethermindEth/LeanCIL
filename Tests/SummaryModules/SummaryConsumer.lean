import Extracted
import SavedSummary

/-! The independently extracted entry reuses the cached decoded summary under this profile. -/
namespace SummaryConsumer
open CIL CIL.Safety CIL.Extraction

/-- The destination contains the reprofiled instructions and the same defining record. -/
theorem checked :
    DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile Extracted.environment
      0 Extracted.assembly0 Extracted.method0Original.token [] SavedSummary.addition := by
  have decoded : decodedProgram? Extracted.profile Extracted.environment Extracted.methodEvidence =
      some Extracted.program :=
    decodedProgram?_eq_some Extracted.translation_valid.programBindingsValid
      (.cons ((Method.ofBody?_of_decodes Extracted.method0_body_validated).trans
        Extracted.method0_decoded) .nil)
  have token : Extracted.method0Original.token = Reference.method0Original.token := by cil_kernel_rfl
  have program : Extracted.program = reprofile Reference.program Extracted.profile := by cil_kernel_rfl
  have record : Extracted.methodEvidence = Reference.methodEvidence := by cil_kernel_rfl
  rw [program, record] at decoded ⊢
  rw [token]
  exact SavedSummary.checked.reprofile (target := Extracted.profile) (by decide +kernel)
    (Program.ProfileAgreement.of_flags _ _ _ (by decide +kernel)) decoded
#print axioms checked
end SummaryConsumer
