import CIL.Extraction.DecodedMethod
import CIL.Safety.OutcomeContract

/-!
# Contracts bound to decoded methods

A `DecodedSummary` is a method contract proved for one index of a program together with the
evidence record that names the method there: the pinned assembly, the metadata token and the
type arguments, and the body bytes, links and certified reachability mask used to decode it.
`decodedProgram?_eq_some` combines each record's body equation in `BodiesDecode` with the
program's mask and call-binding checks to identify the program the summary ranges over. At a call
site, `DecodedSummary.site` identifies the callee's token and type arguments. For a declaring type
with an explicit scope, `DecodedAt.direct_site` also identifies the callee's assembly pin.
-/

namespace CIL.Safety
open CIL.Extraction

/-- Each record's pinned body bytes, links and reachability mask decode to the method at the
    same index of `program`, and the two lists have the same length. -/
inductive BodiesDecode (profile : FeatureProfile) (environment : LayoutEnvironment) :
    List MethodEvidence → CIL.Program → Prop
  /-- No record and no method. -/
  | nil : BodiesDecode profile environment [] []
  /-- The first record decodes to the first method, and the rest to the rest. -/
  | cons {item : MethodEvidence} {method : CIL.Method} {items : List MethodEvidence}
      {methods : CIL.Program}
      (decodes : Method.ofBody? profile environment item.links item.reachable item.body
        item.original item.arguments = some method)
      (rest : BodiesDecode profile environment items methods) :
      BodiesDecode profile environment (item :: items) (method :: methods)

/-- Certified masks, call bindings and per-record body equations identify the decoded program. -/
theorem decodedProgram?_eq_some {profile : FeatureProfile} {environment : LayoutEnvironment}
    {evidence : List MethodEvidence} {program : CIL.Program}
    {imports : List ImportSlot} (bindings : programBindingsValid evidence program imports = true)
    (bodies : BodiesDecode profile environment evidence program) :
    decodedProgram? profile environment evidence imports = some program := by
  apply Option.filter_eq_some_iff.mpr
  refine ⟨?_, bindings⟩
  clear bindings
  induction bodies with
  | nil => rfl
  | cons decodes _ tail =>
    simp [List.mapM_cons, decodes, tail]

#print axioms decodedProgram?_eq_some

/-- The method at each index of a decoded program is the one that index's record decodes to. -/
private theorem bodyMap_getElem {profile : FeatureProfile} {environment : LayoutEnvironment} :
    ∀ {evidence : List MethodEvidence} {program : CIL.Program} {index : Nat}
      {item : MethodEvidence},
      (evidence.mapM fun entry => Method.ofBody? profile environment entry.links entry.reachable
        entry.body entry.original entry.arguments) = some program →
      evidence[index]? = some item →
        ∃ method, program[index]? = some method ∧
          Method.ofBody? profile environment item.links item.reachable item.body item.original
            item.arguments = some method
  | [], _, _, _, _, found => by simp at found
  | head :: items, program, index, item, decoded, found => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at decoded
    obtain ⟨method, decodes, methods, rest, rfl⟩ := decoded
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨method, rfl, decodes⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at found ⊢
      exact bodyMap_getElem rest found

#print axioms bodyMap_getElem

/-- The method at a decoded index is the result of decoding its record's pinned body. -/
theorem decodedProgram?_getElem {profile : FeatureProfile} {environment : LayoutEnvironment}
    {evidence : List MethodEvidence} {program : CIL.Program} {index : Nat} {item : MethodEvidence}
    {imports : List ImportSlot} (decoded : decodedProgram? profile environment evidence imports =
      some program)
    (found : evidence[index]? = some item) :
    Method.ofBody? profile environment item.links item.reachable item.body item.original
      item.arguments = program[index]? := by
  obtain ⟨method, present, decodes⟩ :=
    bodyMap_getElem (Option.filter_eq_some_iff.mp decoded).1 found
  exact decodes.trans present.symm

#print axioms decodedProgram?_getElem

/-- The feature certificate at each decoded index validates its record's mask and method. -/
theorem decodedProgram?_maskValid {profile : FeatureProfile} {environment : LayoutEnvironment}
    {evidence : List MethodEvidence} {program : CIL.Program} {index : Nat}
    {item : MethodEvidence} {method : Method}
    {imports : List ImportSlot} (decoded : decodedProgram? profile environment evidence imports =
      some program)
    (found : evidence[index]? = some item) (present : program[index]? = some method) :
    item.MaskValid evidence method := by
  have paired : (item, method) ∈ evidence.zip program :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨found, present⟩)
  have bindings : programBindingsValid evidence program imports = true :=
    (Option.filter_eq_some_iff.mp decoded).2
  unfold programBindingsValid at bindings
  have methods := (Bool.and_eq_true_iff.mp bindings).2
  exact (of_decide_eq_true (List.all_eq_true.mp methods (item, method) paired)).1

#print axioms decodedProgram?_maskValid

/-- The body's metadata and bytes certify this record's assembly, raw method and signature. -/
def _root_.CIL.Extraction.MethodEvidence.BodyBound (item : MethodEvidence) : Prop :=
  ∃ pins, BodyDecodes pins item.body.platform item.assembly item.body item.original item.arguments
    item.signature item.body.imports

/-- Record `index` of `evidence` is the method with metadata token `token` of assembly `pin`
    at type arguments `arguments`, its closed body instantiates that definition, and its pinned
    body bytes decode to the method at `index` of `program` under its certified mask. -/
def DecodedAt (program : CIL.Program) (evidence : List MethodEvidence)
    (profile : FeatureProfile) (environment : LayoutEnvironment) (index : Nat)
    (pin : AssemblyPin) (token : Nat) (arguments : List TypeExpr) : Prop :=
  ∃ item, evidence[index]? = some item ∧ item.assembly = pin ∧ item.original.token = token ∧
    item.arguments = arguments ∧
    instantiateMethod environment.rawLayouts item.original arguments = some item.closed ∧
    item.BodyBound ∧ ∃ method, program[index]? = some method ∧
      Method.ofBody? profile environment item.links item.reachable item.body item.original
        item.arguments = some method ∧ item.MaskValid evidence method

/-- An entire decoded program binds each recorded method to its pinned body and valid mask. -/
theorem DecodedAt.of_decoded {program : CIL.Program} {evidence : List MethodEvidence}
    {profile : FeatureProfile} {environment : LayoutEnvironment} {imports : List ImportSlot}
    {index : Nat} {item : MethodEvidence}
    (decoded : decodedProgram? profile environment evidence imports = some program)
    (found : evidence[index]? = some item) (body : item.BodyBound)
    (instantiated :
      instantiateMethod environment.rawLayouts item.original item.arguments = some item.closed) :
    DecodedAt program evidence profile environment index item.assembly item.original.token
      item.arguments := by
  obtain ⟨method, present, decodes⟩ :=
    bodyMap_getElem (Option.filter_eq_some_iff.mp decoded).1 found
  exact ⟨item, found, rfl, rfl, rfl, instantiated, body, method, present, decodes,
    decodedProgram?_maskValid decoded found present⟩

#print axioms DecodedAt.of_decoded

/-- A validated translation binds the method at the selected index to its pinned record. -/
theorem DecodedAt.of_translation {program : CIL.Program} {evidence : List MethodEvidence}
    {rawLayouts layouts pins platform imports} (valid : TranslationValid rawLayouts layouts pins platform evidence
      imports program) (index : Fin evidence.length) {method : Method}
    (present : program[index.val]? = some method) :
    DecodedAt program evidence method.profile method.environment index evidence[index].assembly
      evidence[index].original.token evidence[index].arguments := by
  have checked := translation_method_checked valid index method present
  have mask := checked.maskValid
  have body : evidence[index].BodyBound := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, certified, _⟩ := checked
    obtain ⟨assemblies, tables, identity, pinned, _, binding⟩ := certified
    exact ⟨pins, assemblies, tables, identity, pinned, rfl, binding⟩
  exact ⟨evidence[index], List.getElem?_eq_getElem index.isLt, rfl, rfl, rfl, mask.2.1, body,
    method, present, checked.ofBody?, mask⟩

#print axioms DecodedAt.of_translation

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
    {imports : List ImportSlot} (decoded : decodedProgram? profile environment evidence imports =
      some program)
    (found : evidence[index]? = some item) (body : item.BodyBound)
    (instantiated :
      instantiateMethod environment.rawLayouts item.original item.arguments = some item.closed)
    (holds : contract.Holds program index) :
    DecodedSummary program evidence profile environment index item.assembly item.original.token
      item.arguments contract :=
  ⟨holds, DecodedAt.of_decoded decoded found body instantiated⟩

#print axioms DecodedSummary.of_decoded

/-- A contract proved over a validated translation is a summary of its method's pinned record. -/
theorem DecodedSummary.of_translation {Input Output : Type} {contract : MethodContract Input Output}
    {program : CIL.Program} {evidence : List MethodEvidence} {rawLayouts layouts pins platform imports}
    (valid : TranslationValid rawLayouts layouts pins platform evidence imports program)
    (index : Fin evidence.length) {method : Method} (present : program[index.val]? = some method)
    (holds : contract.Holds program index) :
    DecodedSummary program evidence method.profile method.environment index evidence[index].assembly
      evidence[index].original.token evidence[index].arguments contract :=
  ⟨holds, DecodedAt.of_translation valid index present⟩

#print axioms DecodedSummary.of_translation

/-- A method's normal returns and named exceptions, proved for its pinned decoded body. -/
structure DecodedOutcomeSummary {Input Output : Type} (program : CIL.Program)
    (evidence : List MethodEvidence) (profile : FeatureProfile) (environment : LayoutEnvironment)
    (index : Nat) (pin : AssemblyPin) (token : Nat) (arguments : List TypeExpr)
    (contract : OutcomeContract Input Output) : Prop where
  /-- Each permitted input returns with the contract's frame and postcondition or raises
      the exception specified for that input and initial memory. -/
  holds : contract.Holds program index
  /-- The pinned bytes, metadata and checked reachability mask of the method. -/
  bound : DecodedAt program evidence profile environment index pin token arguments

/-- The translation certificate binds an outcome proof to its method's decoded record. -/
theorem DecodedOutcomeSummary.of_translation {Input Output : Type}
    {contract : OutcomeContract Input Output} {program : CIL.Program}
    {evidence : List MethodEvidence}
    {rawLayouts layouts pins platform imports} (valid : TranslationValid rawLayouts layouts pins platform evidence
      imports program) (index : Fin evidence.length) {method : Method}
    (present : program[index.val]? = some method) (holds : contract.Holds program index) :
    DecodedOutcomeSummary program evidence method.profile method.environment index
      evidence[index].assembly evidence[index].original.token evidence[index].arguments contract :=
  ⟨holds, DecodedAt.of_translation valid index present⟩

#print axioms DecodedOutcomeSummary.of_translation

/-- At a live `call` whose link enters `index`, a summary of `index` is for the method the
    raw site names: the site's managed token and type arguments are the summary's. -/
theorem DecodedSummary.site {Input Output : Type} {contract : MethodContract Input Output}
    {program : CIL.Program} {evidence : List MethodEvidence} {profile : FeatureProfile}
    {environment : LayoutEnvironment} {index token : Nat} {pin : AssemblyPin}
    {arguments : List TypeExpr}
    (summary : DecodedSummary program evidence profile environment index pin token arguments
      contract)
    {imports : List ImportSlot} {modelled : CallOpcode × MethodRef → Bool} {raw : RawMethod}
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
    (calls.direct_operand found live rawFound operand managed linked).2
  simp only [specializationTable, List.getElem?_map, recorded, Option.map_some,
    Option.some.injEq] at selected
  subst selected
  subst sameArguments
  refine ⟨?_, calleeArguments⟩
  rw [← sameToken, ← instantiateMethod_token instantiated]
  exact calleeToken

#print axioms DecodedSummary.site

/-- At a live direct managed call whose declaring type carries an assembly scope, the method
    entered by its link has that assembly identity, definition token and type arguments. -/
theorem DecodedAt.direct_site {program : Program} {evidence : List MethodEvidence}
    {profile : FeatureProfile} {environment : LayoutEnvironment} {index token : Nat}
    {pin : AssemblyPin} {arguments : List TypeExpr}
    (bound : DecodedAt program evidence profile environment index pin token arguments)
    {imports : List ImportSlot}
    {modelled : CallOpcode × MethodRef → Bool} {raw : RawMethod} {reachable : List Bool}
    {caller : Method} {pc siteToken : Nat} {method : MethodRef} {prefixes : CallPrefixes}
    {instruction : RawInstruction} {site : CallSite} {scope : String}
    (calls : ManagedCallsValid (specializationTable evidence) imports modelled raw reachable caller)
    (found : caller.code[pc]? = some (.call method prefixes))
    (live : reachable[pc]? = some true) (rawFound : raw.code[pc]? = some instruction)
    (operand : instruction.operand = .call site) (managed : site.target = .managed siteToken)
    (linked : caller.linkAt pc = some (.direct index))
    (hasScope : site.declaringType.headScope = some scope) :
    pin.identity = scope ∧ token = siteToken ∧ arguments = site.typeArguments := by
  obtain ⟨item, recorded, rfl, rfl, rfl, instantiated, _⟩ := bound
  obtain ⟨_, callee, selected, fits⟩ :=
    calls.direct_callee found live rawFound operand managed linked
  simp only [specializationTable, List.getElem?_map, recorded, Option.map_some,
    Option.some.injEq] at selected
  subst selected
  have scopeEq : site.declaringType.headScope = some item.assembly.identity :=
    beq_iff_eq.mp (Bool.and_eq_true_iff.mp fits).2
  simp only [calleeMatchesSite, Bool.and_eq_true, beq_iff_eq, and_assoc] at fits
  exact ⟨Option.some.inj (scopeEq.symm.trans hasScope),
    (instantiateMethod_token instantiated).symm.trans fits.2.1, fits.2.2.1⟩

#print axioms DecodedAt.direct_site

/-- In a validated program, an ordinary live direct call enters the MethodDef row in the
assembly selected by its original operand. A constrained slot can select an override, so the
ordinary-site premise checks that dispatch preserved this instruction at this position. -/
theorem _root_.CIL.Extraction.TranslationValid.direct_definition
    {rawLayouts layouts pins platform evidence imports program}
    (valid : TranslationValid rawLayouts layouts pins platform evidence imports program)
    (caller callee : Fin evidence.length) {body : Method} {pc target : Nat} {scope : String}
    {before : RawInstruction} {source : CallSite} {method : MethodRef} {prefixes : CallPrefixes}
    (present : program[caller.val]? = some body)
    (fetched : evidence[caller].original.code[pc]? = some before)
    (operand : before.operand = .call source) (managed : source.target = .managed target)
    (named : source.declaringType.headScope = some scope)
    (ordinary : (lowerConstrainedRaw evidence[caller].dispatchTypes evidence[caller].closed).code[pc]? =
      evidence[caller].closed.code[pc]?)
    (live : evidence[caller].reachable[pc]? = some true)
    (called : body.code[pc]? = some (.call method prefixes))
    (linked : body.linkAt pc = some (.direct callee.val)) :
    ∃ operandToken env site position index row,
      (operandToken, RawOperand.call source) ∈ evidence[caller].body.tokens.operands ∧
      evidence[caller].body.environment = .ok env ∧ env.methodSite operandToken = .ok site ∧
      site.definition = some (position, evidence[callee].original.token) ∧
      env.slices.find? position = some index ∧
      index.identity = bytesOf evidence[callee].assembly.identity ∧
      index.methodDef evidence[callee].original.token = .ok row := by
  have checked := translation_method_checked valid caller body present
  have calls := checked.2.2.2.2.1
  have inside := (List.getElem?_eq_some_iff.mp called).1
  rw [← calls.2.2.2.1] at inside
  have rawAt := List.getElem?_eq_getElem inside
  obtain ⟨closedSite, closedOperand, closedTarget, closedScope⟩ :=
    instantiateMethod_managedSite checked.1.1 fetched operand managed (scope := scope) named
      (ordinary ▸ rawAt : evidence[caller].closed.code[pc]? = _)
  have calleeInside : callee.val < program.length := valid.2.1 ▸ callee.isLt
  have bound := DecodedAt.of_translation valid callee (List.getElem?_eq_getElem calleeInside)
  obtain ⟨pinEq, tokenEq, _⟩ := bound.direct_site calls called live rawAt closedOperand
    closedTarget linked closedScope
  have callerBound := DecodedAt.of_translation valid caller present
  obtain ⟨item, entry, _, _, _, _, ⟨_, decodes⟩, _⟩ := callerBound
  have itemEq := Option.some.inj ((List.getElem?_eq_getElem caller.isLt).symm.trans entry)
  subst item
  obtain ⟨operandToken, env, site, position, index, row, listed, built, resolved, definition,
    lookup, methodRow, scopeEq⟩ := decodes.callManagedDefinition fetched operand managed
  rw [tokenEq, pinEq]
  exact ⟨operandToken, env, site, position, index, row, listed, built, resolved, definition,
    lookup, scopeEq scope named, methodRow⟩

#print axioms CIL.Extraction.TranslationValid.direct_definition

end CIL.Safety
