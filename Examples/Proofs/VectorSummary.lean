import Extracted
import CIL
import CIL.MethodIdentity

/-!
# A vector callee through a decoded summary

`Examples.DivisionIntrinsics::UnsafeLowNext` returns `UnsafeLow` of its argument plus one.
`UnsafeLow` puts its argument in the low lane of a `Vector128` with `CreateScalarUnsafe` and
reads that lane back with `GetElement`, two calls the extraction runs through their runtime
models. `correctness_stepped` steps the caller and `UnsafeLow` instruction by instruction.
`correctness` proves the same statement from a `DecodedSummary` of `UnsafeLow`: its contract,
bound to the record whose pinned bytes decode to it, applied at the call without stepping its body.
-/

namespace ExampleProof
open CIL CIL.Safety CIL.Extraction

bind_method low lowBody := "System.UInt64 Examples.DivisionIntrinsics::UnsafeLow(System.UInt64)"

/-- The caller returns its argument plus one and keeps the caller memory, stepping `UnsafeLow`. -/
theorem correctness_stepped (memory : Safety.Memory) (x : W64) :
    ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (memory, [.scalar (.i64 (x + 1))]) := by
  cil_checked_steps
#print axioms correctness_stepped

/-- `UnsafeLow` returns its argument and changes no memory. -/
def lowContract : MethodContract W64 W64 where
  args x := [.scalar (.i64 x)]
  results value := [.scalar (.i64 value)]
  pre _ _ := True
  footprint _ := []
  post x initial final value := value = x ∧ final = initial

/-- `UnsafeLow` meets its contract. -/
theorem low_holds : lowContract.Holds Extracted.program low := by
  rintro x memory -
  refine MethodContract.Holds.intro memory x ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
  cil_checked_steps
#print axioms low_holds

/-- Every record's pinned bytes decode to the method at its index of the extraction. -/
theorem bodies_decode :
    decodedProgram? Extracted.profile Extracted.environment Extracted.methodEvidence =
      some Extracted.program :=
  decodedProgram?_eq_some Extracted.translation_valid.programBindingsValid
    (.cons ((Method.ofBody?_of_decodes Extracted.method0_body_validated).trans
        Extracted.method0_decoded)
      (.cons ((Method.ofBody?_of_decodes Extracted.method1_body_validated).trans
          Extracted.method1_decoded) .nil))
#print axioms bodies_decode

/-- The contract, bound to the record of `UnsafeLow` and the bytes it decodes from. -/
theorem low_summary : ∃ record, Extracted.methodEvidence[low]? = some record ∧
    DecodedSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment low record.assembly record.original.token record.arguments
      lowContract :=
  ⟨_, rfl, .of_translation Extracted.translation_valid ⟨low, by decide⟩
    (method := Extracted.method1) rfl low_holds⟩
#print axioms low_summary

/-- The caller returns its argument plus one and keeps the caller memory, applying the summary
    at the call. -/
theorem correctness (memory : Safety.Memory) (x : W64) :
    ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (memory, [.scalar (.i64 (x + 1))]) := by
  obtain ⟨record, -, summary⟩ := low_summary
  refine (WP.exact_iff (execution := Execution fun fuel =>
    invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory)).mp ?_
  cil_contract_steps [summary.holds, lowContract] with middle value lowered
  obtain ⟨rfl, rfl⟩ := lowered.post
  rfl
#print axioms correctness

end ExampleProof
