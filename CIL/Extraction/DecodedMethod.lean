import CIL.Extraction.ValueDecoding
import CIL.Extraction.Translation
import CIL.Extraction.Prefixes

/-!
# Methods decoded from raw definitions

`Method.ofRaw?` decodes a raw definition at its type arguments under its reachability mask.
Live sites use the instantiated operands and the preceding instruction. A dead site is a hole
carrying its raw opcode. The same definition supplies the signature, local kinds and live homes.
An unlinked call resolves against the runtime catalog or its named lowering family. The
resolver uses the method's layouts, profile and raw fold role. The first live hole prevents
method construction and identifies the pc and opcode in the closed decoder's error.
`Method.ofBody?` reads the code and init flag from pinned body bytes instead of the definition,
and `decodedProgram?` checks each method and the static values and identities of the program.
`Method.ofBody?_of_decodes` shows that for a definition whose body check passes, the method of
the bytes is the method of the definition, so a proof about the decoded program needs no
translator output.
-/

namespace CIL.Extraction

/-- The method a raw definition denotes at its type arguments, with the supplied link table. -/
def _root_.CIL.Method.ofRaw? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (source : RawMethod)
    (arguments : List TypeExpr) : Option Method := do
  let closed ← instantiateMethod environment.rawLayouts source arguments
  let storage ← closedArguments environment.rawLayouts closed
  (Method.ofClosed? profile environment links reachable closed storage).toOption

/-- A validated specialization gives the closed definition and storage for raw decoding. -/
theorem SpecializationValid.ofRaw?_eq_ofClosed? {environment : LayoutEnvironment}
    {source closed : RawMethod} {arguments : List TypeExpr} {storage : RawArguments}
    (valid : SpecializationValid environment.rawLayouts source arguments closed storage)
    (profile : FeatureProfile) (links : List (Nat × Link)) (reachable : List Bool) :
    Method.ofRaw? profile environment links reachable source arguments =
      (Method.ofClosed? profile environment links reachable closed storage).toOption := by
  simp only [Method.ofRaw?, valid.1, valid.2, bind, Option.bind]

#print axioms SpecializationValid.ofRaw?_eq_ofClosed?

/-- The method pinned body bytes denote with link table `links`: `checkBody` checks the
    definition's metadata, and the code, init flag and exception clauses are the ones decoded
    from the bytes. -/
def _root_.CIL.Method.ofBody? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (body : BodyEvidence)
    (original : RawMethod) (arguments : List TypeExpr) : Option Method := do
  let decoded ← (checkBody body original arguments).toOption
  Method.ofRaw? profile environment links reachable
    { original with
      code := decoded.code, initLocals := decoded.initLocals, handlers := decoded.handlers }
    arguments

/-- Find a unique matching type row in a carried slice. Forwarders are resolved against
the referenced assembly's identity columns before the implementation is searched. -/
private def constructorTypeLinks (env : MetadataEnv) (slices : List MetadataSlice)
    (token : Nat) : Option (List MetadataLink) := do
  let (columns, _, parts) ← (typeRefQualified env 0 resolveFuel token).toOption
  let some referenced ← (env.referencePosition columns token).toOption | none
  let slice ← slices[referenced]?
  let index ← (env.slice referenced token).toOption
  let routes := slice.rows.filterMap fun (key, _) => do
    guard (metadataTableOf key == Table.exportedType)
    let target ← (index.forwardedAssembly key parts).toOption
    let some position ← (env.referencePosition target key).toOption | none
    return (position, [(⟨linkForwarder, token, referenced, key⟩ : MetadataLink)])
  let candidates := ((referenced, []) :: routes).flatMap fun (position, forwarders) =>
    (slices[position]?.toList.flatMap (·.rows)).filterMap fun (key, _) => do
      guard (metadataTableOf key == Table.typeDef)
      let named ← (typeDefNamed env position resolveFuel key).toOption
      guard (named.parts == parts)
      return (⟨linkDefinition, token, position, key⟩ : MetadataLink) :: forwarders
  let [result] := candidates | none
  return result

/-- Insert a candidate link in the order required by the metadata table. Duplicate keys
remain in the list so table construction rejects conflicting or redundant evidence. -/
private def insertConstructorLink (link : MetadataLink) : List MetadataLink → List MetadataLink
  | [] => [link]
  | head :: tail =>
    if link.kind < head.kind || (link.kind == head.kind && link.source ≤ head.source) then
      link :: head :: tail
    else head :: insertConstructorLink link tail

/-- Bind external class constructors in the original caller to managed definitions. For each
`(pc, callee)` the added rows resolve the MemberRef of the `newobj` at `pc`; its defining
assembly, MethodDef and signature must match `callee`. A MemberRef several sites name binds once,
to one callee. The caller retains its own bytes, rows and declared signature, and its pins gain
each defining assembly they lack; a carried facade stays unpinned. -/
def BodyEvidence.bindConstructors? (body : BodyEvidence) (source : RawMethod)
    (sites : List (Nat × SpecializedMethod)) (dependencies : List MetadataSlice) :
    Option BodyEvidence := do
  let arity := source.genericParameters.length
  let ownerArity := source.ownerParameters.length
  let resolved ← sites.mapM fun (pc, callee) => do
    let token ← body.constructorTokenAt? arity ownerArity pc
    let .call external ← body.tokens.operands.lookup token | none
    let .external _ := external.target | none
    guard (external.method.name == name!".ctor" && callee.arguments.isEmpty &&
      callee.closed.genericParameters.isEmpty && callee.closed.ownerParameters.isEmpty)
    return (token, external, callee)
  let distinct := resolved.foldl (fun kept entry =>
    if kept.any (·.1 == entry.1) then kept else kept ++ [entry]) []
  guard (resolved.all fun (token, _, callee) =>
    distinct.any fun (other, _, bound) => other == token && bound == callee)
  let (first, _, _) ← distinct.head?
  let slices := body.metadata.others ++ dependencies
  let initial := { body.metadata with others := slices }
  let added := dependencies.map (fun slice => bytesOf slice.assembly.identity)
  let identities := body.identities ++ added
  let defining := distinct.foldl (fun kept (_, _, callee) =>
    let identity := bytesOf callee.assembly.identity
    if body.pinned.identities.contains identity || kept.contains identity then kept
    else kept ++ [identity]) []
  let pins := PinnedIndex.ofIdentities (body.pinned.identities ++ defining)
  let tables ← initial.tables.toOption
  let base := { body with metadata := initial, identities, tables, pinned := pins }
  let env ← base.environment.toOption
  let members ← distinct.mapM fun (token, _, callee) => do
    let [position] := identities.zipIdx.filterMap (fun (id, i) =>
        if id == bytesOf callee.assembly.identity then some i else none) | none
    return (⟨linkDefinition, token, position, callee.closed.token⟩ : MetadataLink)
  let index ← (env.slice 0 first).toOption
  let links := body.metadata.own.rows.flatMap fun (key, _) =>
    if metadataTableOf key == Table.typeRef && (index.link linkDefinition key).isNone then
      (constructorTypeLinks env initial.slices key).getD []
    else []
  let ordered := (members ++ links).foldr insertConstructorLink body.metadata.own.links
  let own := { body.metadata.own with links := ordered }
  let metadata := { initial with own }
  let tables ← metadata.tables.toOption
  let linked := { body with metadata, identities, tables, pinned := pins }
  let env ← linked.environment.toOption
  let frame ← (env.frame arity ownerArity).toOption
  let bound ← distinct.mapM fun (token, external, callee) => do
    let site ← (env.methodSite token).toOption
    let (position, definition) ← site.definition
    guard (identities[position]? == some (bytesOf callee.assembly.identity) &&
      definition == callee.closed.token)
    let owner ← callee.closed.receiverClass
    let method := { external.method with
      owner, hasThis := callee.closed.hasThis, parameters := callee.closed.parameters,
      returnType := callee.closed.returnType }
    -- Primitive MemberRef elements keep the caller's primitive scope. A named class element
    -- resolves through its TypeRef, including a forwarder to the defining assembly.
    let parameters := (site.parameters.zip
      (external.declared.parameters.zip method.parameters)).map fun (resolved, original, bound) =>
        match resolved with | .primitive _ => original | _ => bound
    let managed := { external with
      method, target := .managed definition, declared.parameters := parameters }
    let _ ← (checkCallOperand env frame token managed).toOption
    return (token, managed)
  let operands := body.tokens.operands.map fun entry =>
    match bound.lookup entry.1 with
    | some managed => (entry.1, .call managed)
    | none => entry
  return { linked with tokens := { operands } }

/-- The feature certificate checks this method's mask and code against its pinned body's
    specialization, using the constant returns of the surrounding records. -/
abbrev MethodEvidence.MaskValid (item : MethodEvidence) (all : List MethodEvidence)
    (method : Method) : Prop :=
  bodyMatches item.body item.original item.arguments = true ∧
  instantiateMethod method.environment.rawLayouts item.original item.arguments = some item.closed ∧
  FeatureFlowValid method.environment.rawLayouts.toArray (evidenceConstants all) (linkIndex method)
    item.closed method.profile item.featureStates item.reachable method.code

/-- A validated record checks the mask against the method and its pinned, specialized body. -/
theorem MethodEvidenceValid.maskValid {rawLayouts layouts pins platform all imports item method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method) :
    item.MaskValid all method := by
  obtain ⟨specialized, -, -, features, -, -, -, -, -, -, -, -, -, body, environment, -⟩ := valid
  unfold MethodEvidence.MaskValid
  rw [show method.environment = _ from environment]
  exact ⟨body.2.2.2.2.2.2.2, specialized.1, features⟩

#print axioms MethodEvidenceValid.maskValid

/-- The program binds each static identity and value and each method's mask and call targets. -/
def programBindingsValid (evidence : List MethodEvidence) (program : Program)
    (imports : List ImportSlot := []) : Bool :=
  let methods := specializationTable evidence
  decide (StaticValuesValid program ∧ StaticIdentitiesValid program (evidence.map (·.body))) &&
    (evidence.zip program).all fun (item, method) =>
      decide (item.MaskValid evidence method ∧
        ManagedCallsValid methods imports (callModelled method)
          (lowerConstrainedRaw item.dispatchTypes item.closed) item.reachable method ∧
        ConstrainedCallsValid item.dispatchTypes methods item.closed item.reachable method)

/-- A validated translation checks each mask and call binding against the pinned, closed body. -/
theorem TranslationValid.programBindingsValid {rawLayouts layouts pins platform evidence imports program}
    (valid : TranslationValid rawLayouts layouts pins platform evidence imports program) :
    programBindingsValid evidence program imports = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true ⟨valid.2.2.2.1, valid.2.2.2.2.1⟩, ?_⟩
  apply List.all_eq_true.mpr
  rintro ⟨item, method⟩ member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨recorded, compiled⟩ := List.getElem?_zip_eq_some.mp found
  obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp recorded
  have checked := translation_method_checked valid ⟨index, bound⟩ method compiled
  have mask := checked.maskValid
  obtain ⟨-, -, -, -, calls, -, -, -, -, -, -, -, dispatch, -⟩ := checked
  exact decide_eq_true ⟨mask, calls, dispatch⟩

#print axioms TranslationValid.programBindingsValid

/-- The pinned bodies determine the program. Its masks, calls, static identities and initializer
    results agree with the supplied evidence and import slots. -/
def decodedProgram? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (evidence : List MethodEvidence) (imports : List ImportSlot := []) : Option Program :=
  (evidence.mapM fun item =>
    Method.ofBody? profile environment item.links item.reachable item.body item.original
      item.arguments).filter fun program => programBindingsValid evidence program imports

/-- A decoded program validates initializer results and the identity of every static field. -/
theorem decodedProgram?_statics {profile : FeatureProfile} {environment : LayoutEnvironment}
    {evidence : List MethodEvidence} {imports : List ImportSlot} {program : Program}
    (decoded : decodedProgram? profile environment evidence imports = some program) :
    StaticValuesValid program ∧ StaticIdentitiesValid program (evidence.map (·.body)) :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (Option.filter_eq_some_iff.mp decoded).2).1

#print axioms decodedProgram?_statics

/-- A body that decodes to `method` passes `checkBody` with the method's own code, init flag and
    exception clauses. -/
theorem BodyDecodes.code {pins : List AssemblyPin} {platform : PlatformTable}
    {pin : AssemblyPin} {body : BodyEvidence}
    {method : RawMethod} {arguments : List TypeExpr} {signature : String}
    {calls : BodyImports}
    (decodes : BodyDecodes pins platform pin body method arguments signature calls) :
    ∃ decoded, checkBody body method arguments = .ok decoded ∧
      decoded.code = method.code ∧ decoded.initLocals = method.initLocals ∧
      decoded.handlers = method.handlers := by
  have matched := decodes.2.2.2.2.2.2.2
  unfold bodyMatches at matched
  split at matched
  · next decoded checks =>
    simp only [Bool.and_eq_true, beq_iff_eq] at matched
    exact ⟨decoded, checks, matched.1.1.2, matched.1.1.1.2, matched.2⟩
  · exact absurd matched Bool.false_ne_true

#print axioms BodyDecodes.code

/-- No branch of a method whose body decodes enters the instruction after a prefix. -/
theorem BodyDecodes.prefixEntryFree {pins : List AssemblyPin} {platform : PlatformTable}
    {pin : AssemblyPin}
    {body : BodyEvidence} {method : RawMethod} {arguments : List TypeExpr} {signature : String}
    {calls : BodyImports}
    (decodes : BodyDecodes pins platform pin body method arguments signature calls) :
    PrefixEntryFree method.code := by
  obtain ⟨decoded, checks, sameCode, _⟩ := BodyDecodes.code decodes
  exact sameCode ▸ checkBody_prefixEntryFree checks

#print axioms BodyDecodes.prefixEntryFree

/-- The closed code of a method's evidence has no branch into the instruction after a prefix:
    its body decodes, and instantiation keeps every opcode and branch destination. -/
theorem MethodEvidenceValid.prefixEntryFree {rawLayouts : List RawLayout}
    {layouts : Array ComputedLayout} {pins : List AssemblyPin} {platform : PlatformTable}
    {all : List MethodEvidence}
    {imports : List ImportSlot} {item : MethodEvidence} {method : Method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method) :
    PrefixEntryFree item.closed.code := by
  obtain ⟨specialized, -, -, -, -, -, -, -, -, -, -, -, -, decodes, -, -⟩ := valid
  exact instantiateMethod_prefixEntryFree specialized.1 decodes.prefixEntryFree

#print axioms MethodEvidenceValid.prefixEntryFree

/-- The instantiated code of a definition whose body the check accepts, read from that body,
    has no branch into the instruction after a prefix. -/
theorem checkBody_instantiated_prefixEntryFree {layouts : List RawLayout} {body : BodyEvidence}
    {original closed : RawMethod} {arguments : List TypeExpr} {decoded : DecodedBody}
    (checked : checkBody body original arguments = .ok decoded)
    (instantiated : instantiateMethod layouts
      { original with code := decoded.code, initLocals := decoded.initLocals } arguments =
        some closed) :
    PrefixEntryFree closed.code :=
  instantiateMethod_prefixEntryFree instantiated (checkBody_prefixEntryFree checked)

#print axioms checkBody_instantiated_prefixEntryFree

/-- For a body that decodes to `original`, the method of the bytes is the method of the
    definition. -/
theorem _root_.CIL.Method.ofBody?_of_decodes {pins : List AssemblyPin} {platform : PlatformTable}
    {pin : AssemblyPin}
    {body : BodyEvidence} {original : RawMethod} {arguments : List TypeExpr}
    {signature : String} {profile : FeatureProfile} {environment : LayoutEnvironment}
    {links : List (Nat × Link)} {reachable : List Bool}
    {calls : BodyImports}
    (decodes : BodyDecodes pins platform pin body original arguments signature calls) :
    Method.ofBody? profile environment links reachable body original arguments =
      Method.ofRaw? profile environment links reachable original arguments := by
  obtain ⟨decoded, checks, sameCode, sameInit, sameHandlers⟩ := BodyDecodes.code decodes
  unfold Method.ofBody?
  rw [checks]
  show Method.ofRaw? profile environment links reachable
    { original with
      code := decoded.code, initLocals := decoded.initLocals, handlers := decoded.handlers }
    arguments = _
  rw [sameCode, sameInit, sameHandlers]

#print axioms Method.ofBody?_of_decodes

/-- The pinned body and metadata of a validated record decode to the entire executable method. -/
theorem MethodEvidenceValid.ofBody? {rawLayouts layouts pins platform all imports item method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method) :
    Method.ofBody? method.profile method.environment item.links item.reachable item.body
      item.original item.arguments = some method := by
  have decoded := valid.decoded
  obtain ⟨specialized, -, -, -, -, -, -, -, -, -, -, -, -, body, environment, -⟩ := valid
  have storage : SpecializationValid method.environment.rawLayouts item.original item.arguments
      item.closed item.parameterInput := by
    rw [show method.environment = _ from environment]
    exact specialized
  rw [Method.ofBody?_of_decodes body, storage.ofRaw?_eq_ofClosed?, decoded]
  rfl

#print axioms MethodEvidenceValid.ofBody?

/-- A decoded method contains exactly the instructions of its closed definition. -/
theorem _root_.CIL.Method.ofClosed?_code {profile : FeatureProfile}
    {environment : LayoutEnvironment} {links : List (Nat × Link)} {reachable : List Bool}
    {closed : RawMethod} {storage : RawArguments} {method : Method}
    (decoded : Method.ofClosed? profile environment links reachable closed storage = .ok method) :
    method.code = methodCode profile environment links reachable closed :=
  (Method.ofClosed?_fields decoded).1

#print axioms Method.ofClosed?_code

/-- Each pc of a decoded method holds what `Instruction.ofRawAt` decodes at that pc of the
    instantiated definition's code, so the method has one instruction per raw instruction and a
    type test names the type argument and a field access the instantiated field. -/
theorem _root_.CIL.Method.ofRaw?_code {profile : FeatureProfile}
    {environment : LayoutEnvironment} {links : List (Nat × Link)} {reachable : List Bool}
    {source : RawMethod} {arguments : List TypeExpr} {method : Method}
    (decoded : Method.ofRaw? profile environment links reachable source arguments = some method) :
    ∃ closed, instantiateMethod environment.rawLayouts source arguments = some closed ∧
      ∀ pc, method.code[pc]? = Instruction.ofRawAt closed.code pc
        (methodInstruction profile environment.callLayouts closed.owner
          (firstEntryIndex closed.staticFields)
          (Std.TreeSet.ofList (links.map Prod.fst))
          (foldRoles closed.code).toArray reachable.toArray) := by
  unfold Method.ofRaw? at decoded
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
  obtain ⟨closed, instantiated, storage, _, built⟩ := decoded
  refine ⟨closed, instantiated, fun pc => ?_⟩
  cases checked : Method.ofClosed? profile environment links reachable closed storage with
  | error => rw [checked] at built; cases built
  | ok value =>
    rw [checked] at built
    cases built
    rw [Method.ofClosed?_code checked, methodCode_eq,
      Instruction.ofRawCode_getElem? closed.code pc _]

#print axioms Method.ofRaw?_code

end CIL.Extraction
