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
and `decodedProgram?` applies it to every evidence record.
`Method.ofBody?_of_decodes` shows that for a definition whose body check passes, the method of
the bytes is the method of the definition, so a proof about the decoded program needs no
translator output.
-/

namespace CIL.Extraction

/-- A closed body fails at a live opcode or cannot supply its declared frame or prefixes. -/
inductive MethodDecodeError where
  | liveHole (pc opcode : Nat)
  | invalidFrame
  | invalidPrefixes
  deriving DecidableEq, Repr

/-- The first reachable hole carries its instruction index and raw opcode. -/
def firstLiveHole : Nat → List Bool → List Instruction → Option MethodDecodeError
  | pc, live :: rest, instruction :: code =>
    match live, instruction with
    | true, .unadmitted opcode => some (.liveHole pc opcode)
    | _, _ => firstLiveHole (pc + 1) rest code
  | _, _, _ => none

/-- The method denoted by a closed definition and its argument storage. Its code contains
    one instruction per raw site and a hole carrying the opcode at each dead site. The frame
    requires supported local kinds, valid argument homes and accesses, and valid prefixes. -/
def _root_.CIL.Method.ofClosed? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (closed : RawMethod)
    (storage : RawArguments) : Except MethodDecodeError Method :=
  let code := methodCode profile environment links reachable closed
  if let some failure := firstLiveHole 0 reachable code then .error failure else
  match storage.locals.mapM (storageKind environment.layouts),
      expectedHomes environment.layouts storage reachable with
  | some localKinds, some parameterHomes =>
    let homes := requiredHomeIndices storage reachable
    if !rawPrefixesValid closed.returnType closed.code then .error .invalidPrefixes else
    if !argumentInstructionsValid storage homes reachable code then .error .invalidFrame else
    .ok {
      profile := profile, code := code, localKinds := localKinds,
      locals := localKinds.map (LocalKind.initialValue closed.initLocals),
      opaqueVectorLocals := rawOpaqueLocals closed reachable,
      parameterHomes := parameterHomes, declared := DeclaredSignature.ofRaw closed,
      environment := environment, links := links,
      staticSites := closed.rvaSites.map fun (pc, field) => (pc, field.descriptor),
      returnsValue := closed.returnType != .void }
  | _, _ => .error .invalidFrame

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
    definition's metadata, and the code and init flag are the ones decoded from the bytes. -/
def _root_.CIL.Method.ofBody? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (body : BodyEvidence)
    (original : RawMethod) (arguments : List TypeExpr) : Option Method := do
  let decoded ← (checkBody body original arguments).toOption
  Method.ofRaw? profile environment links reachable
    { original with code := decoded.code, initLocals := decoded.initLocals } arguments

/-- The feature certificate checks this method's mask and code against its pinned body's
    specialization, using the constant returns of the surrounding records. -/
abbrev MethodEvidence.MaskValid (item : MethodEvidence) (all : List MethodEvidence)
    (method : Method) : Prop :=
  bodyMatches item.body item.original item.arguments = true ∧
  instantiateMethod method.environment.rawLayouts item.original item.arguments = some item.closed ∧
  FeatureFlowValid method.environment.rawLayouts.toArray (evidenceConstants all) (linkIndex method)
    item.closed method.profile item.featureStates item.reachable method.code

/-- Each decoded method's reachability mask and call targets agree with its closed body. -/
def programBindingsValid (evidence : List MethodEvidence) (program : Program)
    (imports : List ImportSlot := []) : Bool :=
  let methods := specializationTable evidence
  (evidence.zip program).all fun (item, method) =>
    decide (item.MaskValid evidence method ∧
      ManagedCallsValid methods imports (callModelled method)
        (lowerConstrainedRaw item.dispatchTypes item.closed) item.reachable method ∧
      ConstrainedCallsValid item.dispatchTypes methods item.closed item.reachable method)

/-- A validated translation checks each mask and call binding against the pinned, closed body. -/
theorem TranslationValid.programBindingsValid {rawLayouts layouts pins evidence imports program}
    (valid : TranslationValid rawLayouts layouts pins evidence imports program) :
    programBindingsValid evidence program imports = true := by
  apply List.all_eq_true.mpr
  rintro ⟨item, method⟩ member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨recorded, compiled⟩ := List.getElem?_zip_eq_some.mp found
  obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp recorded
  have checked := translation_method_checked valid ⟨index, bound⟩ method compiled
  obtain ⟨specialized, -, -, features, calls, -, -, -, -, -, -, -, -, dispatch, body, env, -⟩ :=
    checked
  apply decide_eq_true
  refine ⟨?_, calls, dispatch⟩
  unfold MethodEvidence.MaskValid
  rw [show method.environment = _ from env]
  exact ⟨body.2.2.2.2.2.2, specialized.1, features⟩

#print axioms TranslationValid.programBindingsValid

/-- The program decoded from the pinned bodies, with validated reachability masks and call
    bindings to the program's own methods or the supplied import slots. -/
def decodedProgram? (profile : FeatureProfile) (environment : LayoutEnvironment)
    (evidence : List MethodEvidence) (imports : List ImportSlot := []) : Option Program :=
  (evidence.mapM fun item =>
    Method.ofBody? profile environment item.links item.reachable item.body item.original
      item.arguments).filter fun program => programBindingsValid evidence program imports

/-- A body that decodes to `method` passes `checkBody` with the method's own code and init flag. -/
theorem BodyDecodes.code {pins : List AssemblyPin} {pin : AssemblyPin} {body : BodyEvidence}
    {method : RawMethod} {arguments : List TypeExpr} {signature : String}
    (decodes : BodyDecodes pins pin body method arguments signature) :
    ∃ decoded, checkBody body method arguments = .ok decoded ∧
      decoded.code = method.code ∧ decoded.initLocals = method.initLocals := by
  have matched := decodes.2.2.2.2.2.2
  unfold bodyMatches at matched
  split at matched
  · next decoded checks =>
    simp only [Bool.and_eq_true, beq_iff_eq] at matched
    exact ⟨decoded, checks, matched.1.2, matched.1.1.2⟩
  · exact absurd matched Bool.false_ne_true

#print axioms BodyDecodes.code

/-- No branch of a method whose body decodes enters the instruction after a prefix. -/
theorem BodyDecodes.prefixEntryFree {pins : List AssemblyPin} {pin : AssemblyPin}
    {body : BodyEvidence} {method : RawMethod} {arguments : List TypeExpr} {signature : String}
    (decodes : BodyDecodes pins pin body method arguments signature) :
    PrefixEntryFree method.code := by
  obtain ⟨decoded, checks, sameCode, _⟩ := BodyDecodes.code decodes
  exact sameCode ▸ checkBody_prefixEntryFree checks

#print axioms BodyDecodes.prefixEntryFree

/-- The closed code of a method's evidence has no branch into the instruction after a prefix:
    its body decodes, and instantiation keeps every opcode and branch destination. -/
theorem MethodEvidenceValid.prefixEntryFree {rawLayouts : List RawLayout}
    {layouts : Array ComputedLayout} {pins : List AssemblyPin} {all : List MethodEvidence}
    {imports : List ImportSlot} {item : MethodEvidence} {method : Method}
    (valid : MethodEvidenceValid rawLayouts layouts pins all imports item method) :
    PrefixEntryFree item.closed.code := by
  obtain ⟨specialized, -, -, -, -, -, -, -, -, -, -, -, -, -, decodes, -, -⟩ := valid
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
theorem _root_.CIL.Method.ofBody?_of_decodes {pins : List AssemblyPin} {pin : AssemblyPin}
    {body : BodyEvidence} {original : RawMethod} {arguments : List TypeExpr}
    {signature : String} {profile : FeatureProfile} {environment : LayoutEnvironment}
    {links : List (Nat × Link)} {reachable : List Bool}
    (decodes : BodyDecodes pins pin body original arguments signature) :
    Method.ofBody? profile environment links reachable body original arguments =
      Method.ofRaw? profile environment links reachable original arguments := by
  obtain ⟨decoded, checks, sameCode, sameInit⟩ := BodyDecodes.code decodes
  unfold Method.ofBody?
  rw [checks]
  show Method.ofRaw? profile environment links reachable
    { original with code := decoded.code, initLocals := decoded.initLocals } arguments = _
  rw [sameCode, sameInit]

#print axioms Method.ofBody?_of_decodes

/-- Closed decoding preserves exactly the instruction list decoded from the closed body. -/
theorem _root_.CIL.Method.ofClosed?_code {profile : FeatureProfile}
    {environment : LayoutEnvironment} {links : List (Nat × Link)} {reachable : List Bool}
    {closed : RawMethod} {storage : RawArguments} {method : Method}
    (decoded : Method.ofClosed? profile environment links reachable closed storage = .ok method) :
    method.code = methodCode profile environment links reachable closed := by
  unfold Method.ofClosed? at decoded
  cases failure : firstLiveHole 0 reachable (methodCode profile environment links reachable closed)
    <;> simp only [failure] at decoded
  repeat' split at decoded
  all_goals first | contradiction | (cases decoded; rfl)

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
        (methodInstruction profile environment.callLayouts (firstEntryIndex closed.rvaSites)
          (Std.TreeSet.ofList (links.map Prod.fst))
          (foldRoles closed.locals closed.code).toArray reachable.toArray) := by
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
