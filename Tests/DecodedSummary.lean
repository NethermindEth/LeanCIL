import CIL.Safety.DecodedSummary
import CIL.Safety.SymbolicExecution
import Tests.DecodedMethod

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
  assembly := pin, featureStates := addFeatureStates }

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
  rintro ⟨record, found, _, _, _, _, _, valid⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq] at found
  subst record
  exact (by decide +kernel : ¬ hiddenAdd.MaskValid [hiddenAdd] hiddenMethod) (valid _ rfl)
#print axioms hidden_add_rejected

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
    tokens.main [] addContract :=
  ⟨add_holds, addItem, rfl, rfl, rfl, rfl, by cil_kernel_rfl, add_body_decodes,
    by rintro method found; cases found; decide +kernel⟩
#print axioms addSummary

/-- A summary of the decoded one-record program is bound to the adder's identity. -/
theorem decoded_summary : DecodedSummary [addMethod] [addItem] testProfile testEnvironment 0 pin
    tokens.main [] addContract :=
  .of_decoded (index := 0) adder_program_decodes rfl (by cil_kernel_rfl) add_holds_alone
#print axioms decoded_summary

/-- The caller's call check, against the records' method table. -/
theorem caller_calls_valid :
    ManagedCallsValid (specializationTable evidence) [] (callModelled callerMethod) callerRaw
      [true, true, true, true] callerMethod := by
  decide +kernel
#print axioms caller_calls_valid

/-- Every summary of the index the caller's call enters is for the method its site names. -/
theorem summary_names_site {token : Nat} {arguments : List TypeExpr}
    (summary : DecodedSummary program evidence testProfile testEnvironment 1 pin token arguments
      addContract) : token = tokens.main ∧ arguments = [] :=
  summary.site caller_calls_valid (pc := 2) rfl rfl rfl rfl rfl rfl
#print axioms summary_names_site

/-- A summary of the index the caller's call enters, bound to another token, is refuted at that
    call. -/
theorem other_token_refused
    (summary : DecodedSummary program evidence testProfile testEnvironment 1 pin
      (tokens.main + 1) [] addContract) : False := by
  have named := (summary_names_site summary).1
  omega
#print axioms other_token_refused

/-- The caller returns the sum, proved from the adder's summary without stepping the adder. -/
theorem caller_returns (memory : Safety.Memory) (left right : W64) :
    WP (Execution (fun fuel => invoke program fuel 0
        [.scalar (.i64 left), .scalar (.i64 right)] memory))
      (fun (final, values) => final = memory ∧ values = [.scalar (.i64 (left + right))]) := by
  cil_contract_steps [addSummary.holds, addContract] with after sum added
  obtain ⟨rfl, rfl⟩ := added.post
  exact ⟨rfl, rfl⟩
#print axioms caller_returns

end Tests.DecodedSummary
