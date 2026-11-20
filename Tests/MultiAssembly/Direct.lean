import Extracted
import CIL.Safety.DecodedSummary
import CIL.Safety.SymbolicExecution

/-! Direct call from the selected assembly into a pinned referenced assembly's static method. -/

open CIL
namespace MultiAssemblyProof

/-- `Direct x` returns `Step x + 1` for every input, with `Step` extracted from the reference. -/
theorem correctness (x : W64) :
    (CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i64 x)] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i64 (x * 3 + 1 + 1))] := by
  rfl

#print axioms correctness
open Safety Extraction

/-- The library method returns three times its input plus one and preserves caller memory. -/
def stepContract : MethodContract W64 W64 where
  args x := [.scalar (.i64 x)]
  results value := [.scalar (.i64 value)]
  pre _ _ := True
  footprint _ := []
  post x initial final value := value = x * 3 + 1 ∧ final = initial

/-- The compiled definition of Step is the second method, from the pinned reference. -/
theorem step_summary :
    DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment 1 Extracted.assembly1 Extracted.method1Original.token []
      stepContract := by
  apply DecodedSummary.of_translation Extracted.translation_valid ⟨1, by decide⟩
    Extracted.program_method1
  intro x memory _
  exact MethodContract.Holds.intro memory (x * 3 + 1) ⟨8, rfl⟩ (Confined.refl _ _) ⟨rfl, rfl⟩

#print axioms step_summary

/-- The caller's MemberRef resolves to Step's MethodDef in the referenced library's slice. -/
theorem direct_member_resolution :
    ∃ env site position,
      Extracted.method0Body.metadata.environmentWith Extracted.method0Body.identities
        Extracted.method0Body.tables Extracted.method0Body.pinned = .ok env ∧
      env.methodSite Extracted.method0Body.tokens.operands[0].1 = .ok site ∧
      site.definition = some (position, Extracted.method1Original.token) ∧
      Extracted.method0Body.identities[position]? =
        some (bytesOf Extracted.assembly1.identity) := by
  obtain ⟨token, env, frame, site, position, listed, built, _, resolved, _, definition⟩ :=
    Extracted.method0_body_validated.callManagedTarget (pc := 1)
      (target := Extracted.method1Original.token) rfl rfl rfl
  have singleton : Extracted.method0Body.tokens.operands =
      [Extracted.method0Body.tokens.operands[0]] := rfl
  rw [singleton, List.mem_singleton] at listed
  have same := congrArg Prod.fst listed
  change token = _ at same
  subst token
  refine ⟨env, site, position, built, resolved, definition, ?_⟩
  cases built
  cases resolved
  cases definition
  rfl

#print axioms direct_member_resolution

/-- At App.Direct's call, the bound callee must belong to Lib. Both assemblies use the same
    MethodDef token for their respective methods. -/
theorem direct_callee_identity {pin : AssemblyPin} {token : Nat} {arguments : List TypeExpr}
    (bound : DecodedAt Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment 1 pin token arguments) :
    pin.identity = Extracted.assembly1.identity ∧ token = Extracted.method0Original.token ∧
      arguments = [] :=
  bound.direct_site Extracted.attribution_validated Extracted.method0_calls_validated
    (pc := 1) rfl rfl rfl rfl rfl rfl rfl (by decide +kernel)

#print axioms direct_callee_identity

/-- The identical token in the calling assembly cannot certify the summary of the library call. -/
theorem app_pin_refused :
    ¬ DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment 1 Extracted.assembly0 Extracted.method0Original.token []
      stepContract := by
  intro summary
  exact (by decide : Extracted.assembly0.identity ≠ Extracted.assembly1.identity)
    (direct_callee_identity summary.bound).1

#print axioms app_pin_refused

/-- The caller uses the library summary and returns the incremented result in unchanged memory. -/
theorem direct_uses_summary (x : W64) (memory : Safety.Memory) :
    WP (Execution (fun fuel => invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory))
      (fun (final, values) => final = memory ∧ values = [.scalar (.i64 (x * 3 + 1 + 1))]) := by
  cil_contract_steps [step_summary.holds, stepContract] with after value result
  obtain ⟨rfl, rfl⟩ := result.post
  exact ⟨rfl, rfl⟩

#print axioms direct_uses_summary
end MultiAssemblyProof
