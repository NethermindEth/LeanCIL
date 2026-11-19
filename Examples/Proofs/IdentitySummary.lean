import Extracted
import CIL
import CIL.MethodIdentity

/-!
# Identity through a decoded summary

`Examples.GenericMethods::Identity64` calls `Identity<ulong>` once. `correctness_stepped` steps
the caller and the specialization instruction by instruction. `correctness` proves the same
statement from a `DecodedSummary` of the specialization: its contract, bound to the record whose
pinned bytes decode to it, applied at the call without stepping its body.
-/

namespace ExampleProof
open CIL CIL.Safety CIL.Extraction

bind_method identity identityBody :=
  "System.UInt64 Examples.GenericMethods::Identity<System.UInt64>(System.UInt64)"

/-- The identity specialization returns its argument and changes no memory. -/
def identityContract : MethodContract W64 W64 where
  args x := [.scalar (.i64 x)]
  results value := [.scalar (.i64 value)]
  pre _ _ := True
  footprint _ := []
  post x initial final value := value = x ∧ final = initial

/-- The caller returns its argument and keeps the caller memory, stepping the specialization. -/
theorem correctness_stepped (memory : Safety.Memory) (x : W64) :
    ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (memory, [.scalar (.i64 x)]) := by
  cil_checked_steps
#print axioms correctness_stepped

/-- The specialization meets its contract. -/
theorem identity_holds : identityContract.Holds Extracted.program identity := by
  rintro x memory -
  refine MethodContract.Holds.intro memory x ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
  cil_checked_steps
#print axioms identity_holds

/-- Every record's pinned bytes decode to the method at its index of the extraction. -/
theorem bodies_decode :
    decodedProgram? Extracted.profile Extracted.environment Extracted.methodEvidence =
      some Extracted.program :=
  decodedProgram?_eq_some Extracted.translation_valid.programMasksValid
    (.cons ((Method.ofBody?_of_decodes Extracted.method0_body_validated).trans
        Extracted.method0_decoded)
      (.cons ((Method.ofBody?_of_decodes Extracted.method1_body_validated).trans
          Extracted.method1_decoded) .nil))
#print axioms bodies_decode

/-- The contract, bound to the record of the specialization and the bytes it decodes from. -/
theorem identity_summary : ∃ record, Extracted.methodEvidence[identity]? = some record ∧
    DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment identity record.assembly record.original.token record.arguments
      identityContract :=
  ⟨_, rfl, .of_decoded bodies_decode rfl Extracted.method1_specialization_validated.1
    identity_holds⟩
#print axioms identity_summary

/-- The call of the caller names the metadata token and type arguments of any summary of the
    index its link enters. -/
theorem calls_name_summary {pin : AssemblyPin} {token : Nat} {arguments : List TypeExpr}
    (summary : DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment identity pin token arguments identityContract) :
    ∃ site,
      (lowerConstrainedRaw Extracted.method0DispatchTypes Extracted.method0Closed).code[1]?.map
        RawInstruction.operand = some (.call site) ∧
      site.target = .managed token ∧ site.typeArguments = arguments := by
  obtain ⟨sameToken, sameArguments⟩ :=
    summary.site Extracted.method0_calls_validated (pc := 1) rfl rfl rfl rfl rfl rfl
  exact ⟨_, rfl, by rw [sameToken], sameArguments.symm⟩
#print axioms calls_name_summary

/-- The caller returns its argument and keeps the caller memory, applying the summary at
    the call. -/
theorem correctness (memory : Safety.Memory) (x : W64) :
    ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (memory, [.scalar (.i64 x)]) := by
  obtain ⟨record, -, summary⟩ := identity_summary
  refine (WP.exact_iff (execution := Execution fun fuel =>
    invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory)).mp ?_
  cil_contract_steps [summary.holds, identityContract] with middle value firstCall
  obtain ⟨rfl, rfl⟩ := firstCall.post
  rfl
#print axioms correctness

end ExampleProof
