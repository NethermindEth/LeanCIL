import Extracted
import CIL.Safety.DecodedSummary

/-! A direct call through a local struct into a second pinned assembly. -/

open CIL CIL.Safety CIL.Extraction
namespace MultiAssemblyProof

/-- Calling the library through the local struct returns three times five plus one. -/
theorem correctness :
    (invoke Extracted.program 64 0 [.scalar (.i64 5)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 16)] := by rfl

#print axioms correctness

/-- The struct's declaring type binds its method to the application assembly and definition token. -/
theorem counter_callee {pin : AssemblyPin} {token : Nat} {arguments : List TypeExpr}
    (bound : DecodedAt Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment 1 pin token arguments) :
    pin.identity = Extracted.assembly0.identity ∧ token = Extracted.method1Original.token ∧
      arguments = [] :=
  bound.direct_site Extracted.attribution_validated Extracted.method0_calls_validated
    (pc := 1) rfl rfl rfl rfl rfl rfl rfl (by decide +kernel)

#print axioms counter_callee

/-- The referenced library cannot supply the application's struct method. -/
theorem foreign_pin_refused {token : Nat} {arguments : List TypeExpr} :
    ¬ DecodedAt Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment 1 Extracted.assembly1 token arguments := by
  intro bound
  exact (by decide : Extracted.assembly1.identity ≠ Extracted.assembly0.identity)
    (counter_callee bound).1

#print axioms foreign_pin_refused
end MultiAssemblyProof
