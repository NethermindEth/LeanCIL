import CIL.Extraction.DecodedMethod
import CIL.Safety.MethodContract

/-!
# Contracts bound to decoded methods

A `DecodedSummary` is a method contract proved for one index of a program together with the
evidence record that names the method there: the pinned assembly, the metadata token and the
type arguments, and the body bytes that decode to the method at that index. `BodiesDecode`
states, record by record, that the evidence decodes to the program, and
`decodedProgram?_eq_some` turns it into the decoded program the summary ranges over. At a call
site, `DecodedSummary.site` shows that the summary at the index the call's link enters is
for the method the site's metadata names.
-/

namespace CIL.Safety
open CIL.Extraction

/-- Each evidence record's pinned body bytes, with the record's links, decode to the method at
    the same index of `program`, and the two lists have the same length. -/
inductive BodiesDecode (profile : FeatureProfile) (environment : LayoutEnvironment) :
    List MethodEvidence → CIL.Program → Prop
  /-- No record and no method. -/
  | nil : BodiesDecode profile environment [] []
  /-- The first record decodes to the first method, and the rest to the rest. -/
  | cons {item : MethodEvidence} {method : CIL.Method} {items : List MethodEvidence}
      {methods : CIL.Program}
      (decodes : Method.ofBody? profile environment item.links item.body item.original
        item.arguments = some method)
      (rest : BodiesDecode profile environment items methods) :
      BodiesDecode profile environment (item :: items) (method :: methods)

/-- Bodies that decode record by record give `program` as the decoded program. -/
theorem decodedProgram?_eq_some {profile : FeatureProfile} {environment : LayoutEnvironment}
    {evidence : List MethodEvidence} {program : CIL.Program}
    (bodies : BodiesDecode profile environment evidence program) :
    decodedProgram? profile environment evidence = some program := by
  induction bodies with
  | nil => rfl
  | cons decodes _ tail =>
    unfold decodedProgram? at tail ⊢
    simp [List.mapM_cons, decodes, tail]

#print axioms decodedProgram?_eq_some

/-- The method at each index of a decoded program is the one that index's record decodes to. -/
theorem decodedProgram?_getElem {profile : FeatureProfile} {environment : LayoutEnvironment} :
    ∀ {evidence : List MethodEvidence} {program : CIL.Program} {index : Nat}
      {item : MethodEvidence},
      decodedProgram? profile environment evidence = some program →
      evidence[index]? = some item →
        Method.ofBody? profile environment item.links item.body item.original item.arguments =
          program[index]?
  | [], _, _, _, _, found => by simp at found
  | head :: items, program, index, item, decoded, found => by
    unfold decodedProgram? at decoded
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at decoded
    obtain ⟨method, decodes, methods, rest, rfl⟩ := decoded
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simpa using decodes
    | succ index =>
      simp only [List.getElem?_cons_succ] at found ⊢
      exact decodedProgram?_getElem rest found

#print axioms decodedProgram?_getElem

/-- Record `index` of `evidence` is the method with metadata token `token` of assembly `pin`
    at type arguments `arguments`, its closed body instantiates that definition, and its pinned
    body bytes decode to the method at `index` of `program`. -/
def DecodedAt (program : CIL.Program) (evidence : List MethodEvidence)
    (profile : FeatureProfile) (environment : LayoutEnvironment) (index : Nat)
    (pin : AssemblyPin) (token : Nat) (arguments : List TypeExpr) : Prop :=
  ∃ item, evidence[index]? = some item ∧ item.assembly = pin ∧ item.original.token = token ∧
    item.arguments = arguments ∧
    instantiateMethod environment.rawLayouts item.original arguments = some item.closed ∧
    Method.ofBody? profile environment item.links item.body item.original item.arguments =
      program[index]?

/-- `contract` holds for the method at `index`, and `bound` names that method by pinned
    assembly, metadata token and type arguments and ties it to the bytes it decodes from.
    `MethodContract.Certified` names only an index, which another extraction can give another
    body; an `ImportSlot` names a method with no body. A caller holding `bound` knows which
    metadata method and which bytes the contract was proved for. -/
structure DecodedSummary {Input Output : Type} (program : CIL.Program)
    (evidence : List MethodEvidence) (profile : FeatureProfile) (environment : LayoutEnvironment)
    (index : Nat) (pin : AssemblyPin) (token : Nat) (arguments : List TypeExpr)
    (contract : MethodContract Input Output) : Prop where
  /-- The contract of the method at `index`. -/
  holds : contract.Holds program index
  /-- The identity and bytes of the method at `index`. -/
  bound : DecodedAt program evidence profile environment index pin token arguments

/-- A contract proved for an index of the decoded program is a summary of the record there. -/
theorem DecodedSummary.of_decoded {Input Output : Type} {contract : MethodContract Input Output}
    {program : CIL.Program} {evidence : List MethodEvidence} {profile : FeatureProfile}
    {environment : LayoutEnvironment} {index : Nat} {item : MethodEvidence}
    (decoded : decodedProgram? profile environment evidence = some program)
    (found : evidence[index]? = some item)
    (instantiated :
      instantiateMethod environment.rawLayouts item.original item.arguments = some item.closed)
    (holds : contract.Holds program index) :
    DecodedSummary program evidence profile environment index item.assembly item.original.token
      item.arguments contract :=
  ⟨holds, item, found, rfl, rfl, rfl, instantiated, decodedProgram?_getElem decoded found⟩

#print axioms DecodedSummary.of_decoded

/-- At a live `call` whose link enters `index`, a summary of `index` is for the method the
    raw site names: the site's managed token and type arguments are the summary's. -/
theorem DecodedSummary.site {Input Output : Type} {contract : MethodContract Input Output}
    {program : CIL.Program} {evidence : List MethodEvidence} {profile : FeatureProfile}
    {environment : LayoutEnvironment} {index token : Nat} {pin : AssemblyPin}
    {arguments : List TypeExpr}
    (summary : DecodedSummary program evidence profile environment index pin token arguments
      contract)
    {imports : List ImportSlot} {modelled : MethodRef → Bool} {raw : RawMethod}
    {reachable : List Bool} {caller : CIL.Method}
    {pc siteToken : Nat} {method : MethodRef} {prefixes : CallPrefixes}
    {instruction : RawInstruction} {site : CallSite}
    (calls :
      ManagedCallsValid (specializationTable evidence) imports modelled raw reachable caller)
    (found : caller.code[pc]? = some (.call method prefixes))
    (live : reachable[pc]? = some true) (rawFound : raw.code[pc]? = some instruction)
    (operand : instruction.operand = .call site) (managed : site.target = .managed siteToken)
    (linked : caller.linkAt pc = some (.direct index)) :
    token = siteToken ∧ arguments = site.typeArguments := by
  obtain ⟨item, recorded, -, sameToken, sameArguments, instantiated, -⟩ := summary.bound
  obtain ⟨callee, selected, calleeToken, calleeArguments⟩ :=
    calls.callee_token found live rawFound operand managed linked
  simp only [specializationTable, List.getElem?_map, recorded, Option.map_some,
    Option.some.injEq] at selected
  subst selected
  subst sameArguments
  refine ⟨?_, calleeArguments⟩
  rw [← sameToken, ← instantiateMethod_token instantiated]
  exact calleeToken

#print axioms DecodedSummary.site

end CIL.Safety
