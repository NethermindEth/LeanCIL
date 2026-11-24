import CIL.Safety.DecodedSummary
import CIL.Safety.SymbolicExecution
import Tests.DecodedMethod
import Tests.ProfileContract

/-!
# Decoded summary tests

A contract proved for the world's adder, at index 1 of a program whose caller at index 0 calls
it, is a `DecodedSummary` bound to the adder's pinned bytes, metadata token and type
arguments. The bodies of a one-record program decode to that program through
`decodedProgram?_eq_some`, and `DecodedSummary.of_decoded` builds a summary from the decoded
program. At the caller's call site, `DecodedSummary.site` shows the summary is for the method
the site's token names, and the caller's proof composes the call through the summary alone.
-/

namespace Tests.DecodedSummary

open CIL CIL.Extraction CIL.Safety Tests.BodyEncoding Tests.BodyDecoding Tests.MetadataWorld
open Tests.DecodedMethod

/-- The adder's pinned bytes, `12 02 03 58 2A` against its metadata. -/
def addBody : BodyEvidence := (encodeBody pin addArgumentsRaw).get (by decide +kernel)

cil_decoded_method addMethod :=
  Method.ofRaw? testProfile testEnvironment [] (allLive addArgumentsRaw) addArgumentsRaw []
cil_instruction_equations addMethod
cil_resolution_facts addMethod

/-- The call site of the adder, the world's `Program.Main` given two `uint64` parameters. -/
def addSite : CallSite := {
  declared := { convention := 0, returnType := uint64, parameters := [uint64, uint64] },
  method := {
    owner := .object ownIdentity "Program", name := name!"Main", hasThis := false,
    genericArity := 0, returnType := uint64, parameters := [uint64, uint64] },
  name := "Main", target := .managed tokens.main, typeArguments := [], parameterCount := 2,
  returnsValue := true }

/-- `ldarg.0; ldarg.1; call Main(uint64, uint64); ret`, a method with the next token. -/
def callerRaw : RawMethod :=
  { method 8 false [] [instr 0 2, instr 1 3, instr 2 0x28 (.call addSite), instr 7 0x2A] with
    token := tokens.main + 1, parameters := [uint64, uint64], returnType := uint64 }

cil_decoded_method callerMethod :=
  Method.ofRaw? testProfile testEnvironment [(2, .direct 1)] (allLive callerRaw) callerRaw []
cil_instruction_equations callerMethod
cil_resolution_facts callerMethod

/-- The caller at 0 and the adder at 1. -/
def program : CIL.Program := [callerMethod, addMethod]

/-- The adder's record, with its bytes. -/
def addItem : MethodEvidence := { item addArgumentsRaw addBody with
  assembly := pin, featureStates := addFeatureStates,
  signature := (spelled? addBody.names.signature).getD "" }

/-- The adder's row and body bind the selector and assembly of its summary. -/
theorem add_body_bound : addItem.BodyBound := ⟨[], by decide +kernel⟩
#print axioms add_body_bound

/-- A different assembly label cannot reuse the adder's unchanged bytes and metadata. -/
theorem rejects_substituted_assembly :
    ¬ DecodedAt [addMethod] [{ addItem with assembly := ⟨"Elsewhere"⟩ }]
      testProfile testEnvironment 0 ⟨"Elsewhere"⟩ tokens.main [] := by
  rintro ⟨record, found, _, _, _, _, ⟨_, body⟩, _⟩
  cases found
  exact (by decide : addBody.metadata.own.assembly.identity ≠ "Elsewhere") body.2.2.1
#print axioms rejects_substituted_assembly

/-- The records of `program`; the caller's carries the adder's bytes, so only the adder's record
    decodes to its method. -/
def evidence : List MethodEvidence :=
  [{ item callerRaw addBody with links := [(2, .direct 1)] }, addItem]

/-- The adder's bytes decode to the adder. -/
theorem add_body_decodes :
    Method.ofBody? testProfile testEnvironment [] (allLive addArgumentsRaw)
      addBody addArgumentsRaw [] = some addMethod := by
  cil_kernel_rfl
#print axioms add_body_decodes

/-- An evidence-only change of a calli catalog from method 1 to 0 fails translation. -/
theorem changed_indirect_index_refused {rawLayouts layouts pins platform all imports}
    (record : MethodEvidence) (emitted : Method) (handler : ManagedIdentity)
    (recorded : linkLookup record.links 18 = some (.indirect [⟨handler, 0⟩]))
    (checked : emitted.linkAt 18 = some (.indirect [⟨handler, 1⟩])) :
    ¬ MethodEvidenceValid rawLayouts layouts pins platform all imports record emitted := by
  intro valid
  rw [valid.links_eq] at recorded
  change linkLookup emitted.links 18 = _ at checked
  rw [checked] at recorded
  cases recorded
#print axioms changed_indirect_index_refused

/-- A one-record program decodes record by record, so `decodedProgram?` gives it. -/
theorem adder_program_decodes :
    decodedProgram? testProfile testEnvironment [addItem] = some [addMethod] :=
  decodedProgram?_eq_some (by decide +kernel) (.cons add_body_decodes .nil)
#print axioms adder_program_decodes

/-- The original certificate marks the add live, while the supplied mask hides it. -/
private def hiddenAdd := { addItem with reachable := [true, true, false, true] }

/-- The byte decoder under the forged mask replaces the live add with its raw opcode. -/
private def hiddenMethod := { addMethod with code := [.ldarg 0, .ldarg 1, .unadmitted 88, .ret] }

/-- Neither the decoded program nor a summary with the original identity accepts the hidden add. -/
theorem hidden_add_rejected :
    Method.ofBody? testProfile testEnvironment [] hiddenAdd.reachable addBody addArgumentsRaw [] =
      some hiddenMethod ∧
    decodedProgram? testProfile testEnvironment [hiddenAdd] = none ∧
    ¬ DecodedAt [hiddenMethod] [hiddenAdd] testProfile testEnvironment 0 pin tokens.main [] := by
  refine ⟨by cil_kernel_rfl, by decide +kernel, ?_⟩
  rintro ⟨record, found, _, _, _, _, _, method, present, _, valid⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq] at found
  subst record
  cases present
  exact (by decide +kernel : ¬ hiddenAdd.MaskValid [hiddenAdd] hiddenMethod) valid
#print axioms hidden_add_rejected

/-- An empty body fails to decode even though the adder's definition still instantiates. -/
private def emptyBody := { addItem with body.bytes := [] }

/-- A failed body decode and an absent program entry cannot bind the adder's record. -/
theorem missing_method_rejected :
    instantiateMethod testEnvironment.rawLayouts emptyBody.original [] = some emptyBody.closed ∧
    Method.ofBody? testProfile testEnvironment emptyBody.links emptyBody.reachable emptyBody.body
      emptyBody.original emptyBody.arguments = none ∧
    ¬ DecodedAt [] [emptyBody] testProfile testEnvironment 0 pin tokens.main [] := by
  refine ⟨by cil_kernel_rfl, by cil_kernel_rfl, ?_⟩
  rintro ⟨_, _, _, _, _, _, _, _, present, _⟩
  cases present
#print axioms missing_method_rejected

/-- `(left, right)` returns `left + right` and changes no memory. -/
def addContract : MethodContract (W64 × W64) W64 where
  args := fun (left, right) => [.scalar (.i64 left), .scalar (.i64 right)]
  results sum := [.scalar (.i64 sum)]
  pre _ _ := True
  footprint _ := []
  post := fun (left, right) initial final sum => sum = left + right ∧ final = initial

/-- The adder meets its contract at index 1 of `program`. -/
theorem add_holds : addContract.Holds program 1 := by
  rintro ⟨left, right⟩ memory -
  refine MethodContract.Holds.intro memory (left + right) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
  cil_checked_steps
#print axioms add_holds

/-- The adder meets its contract as the only method of a program. -/
theorem add_holds_alone : addContract.Holds [addMethod] 0 := by
  rintro ⟨left, right⟩ memory -
  refine MethodContract.Holds.intro memory (left + right) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
  cil_checked_steps
#print axioms add_holds_alone

/-- The adder's contract, bound to its record at index 1. -/
theorem addSummary : DecodedSummary program evidence testProfile testEnvironment 1 pin
    tokens.main [] [] addContract :=
  ⟨fun _ => add_holds, ⟨addItem, rfl, rfl, rfl, rfl, by cil_kernel_rfl, add_body_bound, addMethod,
    rfl, add_body_decodes, by decide +kernel⟩, .of_sites [1] (by decide) (by decide) rfl⟩
#print axioms addSummary

/-- A summary of the decoded one-record program is bound to the adder's identity. -/
theorem decoded_summary : DecodedSummary [addMethod] [addItem] testProfile testEnvironment 0 pin
    tokens.main [] [] addContract :=
  .of_decoded (index := 0) adder_program_decodes rfl add_body_bound (by cil_kernel_rfl)
    add_holds_alone (.of_sites [0] (by decide) (by decide) rfl)
#print axioms decoded_summary

/-- The scalar adder's summary also certifies the same body and contract under x86-64-v3. -/
theorem add_summary_x64 :
    DecodedSummary (reprofile [addMethod] Tests.ProfileContract.avx2Profile) [addItem]
      Tests.ProfileContract.avx2Profile testEnvironment 0 pin tokens.main [] [] addContract :=
  decoded_summary.reprofile (by decide +kernel)
    (Program.ProfileAgreement.of_flags _ _ _ (by decide +kernel))
    (imports := []) (by cil_kernel_rfl)
#print axioms add_summary_x64

/-- Reusing the scalar outcome proof under x86-64-v3 retains the adder's pinned body. -/
theorem add_outcome_x64 :
    DecodedOutcomeSummary (reprofile [addMethod] Tests.ProfileContract.avx2Profile) [addItem]
      Tests.ProfileContract.avx2Profile testEnvironment 0 pin tokens.main [] []
      { addContract with raises := fun _ _ => none } := by
  let outcome : OutcomeContract (W64 × W64) W64 :=
    { addContract with raises := fun _ _ => none }
  have source : DecodedOutcomeSummary [addMethod] [addItem] testProfile testEnvironment 0
      pin tokens.main [] [] outcome :=
    ⟨fun _ => add_holds_alone.outcomes, decoded_summary.bound, decoded_summary.listed⟩
  exact source.reprofile (by decide +kernel)
    (Program.ProfileAgreement.of_flags _ _ _ (by decide +kernel))
    (imports := []) (by cil_kernel_rfl)
#print axioms add_outcome_x64

/-- The caller's call check, against the records' method table. -/
theorem caller_calls_valid :
    ManagedCallsValid (specializationTable evidence) [] (callModelled callerMethod) callerRaw
      [true, true, true, true] callerMethod := by
  decide +kernel
#print axioms caller_calls_valid

/-- Every summary of the index the caller's call enters is for the method its site names. -/
theorem summary_names_site {token : Nat} {arguments : List TypeExpr} {models : List ModelledCall}
    (summary : DecodedSummary program evidence testProfile testEnvironment 1 pin token arguments
      models addContract) : token = tokens.main ∧ arguments = [] :=
  summary.site caller_calls_valid (pc := 2) rfl rfl rfl rfl rfl rfl
#print axioms summary_names_site

/-- A summary of the index the caller's call enters, bound to another token, is refuted at that
    call. -/
theorem other_token_refused {models : List ModelledCall}
    (summary : DecodedSummary program evidence testProfile testEnvironment 1 pin
      (tokens.main + 1) [] models addContract) : False := by
  have named := (summary_names_site summary).1
  omega
#print axioms other_token_refused

/-- The caller returns the sum, proved from the adder's summary without stepping the adder. -/
theorem caller_returns (memory : Safety.Memory) (left right : W64) :
    WP (Execution (fun fuel => invoke program fuel 0
        [.scalar (.i64 left), .scalar (.i64 right)] memory))
      (fun (final, values) => final = memory ∧ values = [.scalar (.i64 (left + right))]) := by
  cil_contract_steps [addSummary.holds (.nil _), addContract] with after sum added
  obtain ⟨rfl, rfl⟩ := added.post
  exact ⟨rfl, rfl⟩
#print axioms caller_returns

/-- `UnsafeLow`'s body: its two vector calls have no link and run their runtime models. -/
def lowMethod : Method :=
  { addMethod with links := [], code := [.ldarg 0, .call createScalarUnsafeMethod {},
    .ldc_i4 0, .call getElement128Method {}, .ret] }

/-- The vector calls of `lowMethod` and the intrinsics the runtime table runs for them. -/
def lowModels : List ModelledCall :=
  [⟨.call, createScalarUnsafeMethod, .intrinsic (.vector .createScalarUnsafe64) 1⟩,
    ⟨.call, getElement128Method, .intrinsic (.vector (.extract64 128)) 2⟩]

/-- The listing names both vector calls, and the runtime table gives each its listed model. -/
theorem low_models : ModelsListed [lowMethod] 0 lowModels ∧
    ModelsResolve lowMethod.environment lowModels :=
  ⟨.of_sites [0] (by decide) (by decide) rfl, by decide +kernel⟩
#print axioms low_models

/-- No summary of `lowMethod` can leave out its `CreateScalarUnsafe` call, so its statement
    cannot hide the runtime behaviour its contract relies on. -/
theorem low_unlisted_refused {Input Output : Type} {evidence : List MethodEvidence}
    {profile : FeatureProfile} {environment : LayoutEnvironment} {pin : AssemblyPin}
    {token : Nat} {arguments : List TypeExpr} {contract : MethodContract Input Output}
    (models : List ModelledCall)
    (omitted : ∀ call ∈ models, call.method ≠ createScalarUnsafeMethod) :
    ¬ DecodedSummary [lowMethod] evidence profile environment 0 pin token arguments models
      contract := by
  intro summary
  obtain ⟨call, member, -, named⟩ := summary.listed 0 lowMethod .refl rfl
    (.call, createScalarUnsafeMethod) (Method.mem_modelledSites (pc := 1) rfl rfl rfl)
  exact omitted call member named
#print axioms low_unlisted_refused

end Tests.DecodedSummary
