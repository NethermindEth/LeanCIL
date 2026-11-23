import CIL.Extraction.Scalars
import CIL.Extraction.LayoutCoverage
import CIL.Extraction.UnsafeCalls
import CIL.Extraction.OpaqueLocals
import CIL.Extraction.ClosedMethod
import CIL.Extraction.ObjectOperands
import CIL.Extraction.StaticValues
import CIL.Extraction.StaticIdentities
import CIL.Extraction.ImportLayouts
import CIL.Extraction.Constrained
import CIL.Extraction.Assemblies
import CIL.Extraction.BodyDecoding
import CIL.Extraction.BodyDiagnostics
import CIL.EntryIndex
import CIL.Extraction.LinkIndex
import Std.Data.TreeMap.Lemmas
import CIL.Resolution

/-!
# Translation validity

The top of the extraction checks. `TranslationValid` conjoins the kernel-checked validators
for one extraction: layouts recompute, every emitted method passes the per-method validators
against its evidence record, static values are reproduced by their initializers, each static
identity stands for exactly one field, import
layouts agree, every body is owned by the pinned assembly its evidence names, and every method
definition is what its body bytes and carried metadata say. It is not a simulation proof for
every raw opcode; general instruction translation, that the carried metadata rows are the image's,
that the `platform` definitions every body is checked against are the platform's, and the PE
container stay trusted, as `docs/SOUNDNESS.md` describes.

Generated modules prove each method's evidence separately and assemble it with
`translation_of_methods`, so no validator is reduced twice.
-/

namespace CIL.Extraction

deriving instance DecidableEq for CIL.Instruction
deriving instance DecidableEq for CIL.Method

private instance (result : Except MethodDecodeError Method) (method : Method) :
    Decidable (result = .ok method) := by
  cases result with
  | error failure => exact isFalse (by intro same; cases same)
  | ok candidate => exact decidable_of_iff (candidate = method) ⟨congrArg Except.ok, Except.ok.inj⟩

/-- Every extracted method has exactly one record, in emitted program order. -/
structure MethodEvidence where
  original : RawMethod
  /-- The bytes `original` was decoded from, and the metadata its tokens resolve to. -/
  body : BodyEvidence
  arguments : List TypeExpr
  closed : RawMethod
  parameterInput : RawArguments
  reachable : List Bool
  featureStates : FeatureCertificate
  scalarStates : ScalarCertificate
  layoutUses : List LayoutUse
  dispatchTypes : List DispatchType := []
  /-- The pinned assembly whose metadata supplied this body. -/
  assembly : AssemblyPin := {}
  /-- The string a proof selects the method by: an extraction's `signatures` table lists these,
      and `BodyDecodes` equates each with Cecil's full name of the method its row defines. -/
  signature : String := ""
  /-- The link table the extraction states for the method's call sites and constructions; the
      call check ties each entry to its raw site. -/
  links : List (Nat × Link) := []

/-- The pin and owner identity of every original and closed body, for attribution checks. -/
def bodyOwners (evidence : List MethodEvidence) : List (AssemblyPin × String) :=
  evidence.flatMap fun item =>
    [(item.assembly, item.original.owner), (item.assembly, item.closed.owner)]

/-- The program's method table, as the call check sees it. -/
def specializationTable (evidence : List MethodEvidence) : List SpecializedMethod :=
  evidence.map fun item => ⟨item.arguments, item.closed, item.assembly⟩

/-- The word each program method returns, by emitted index, as its own feature certificate
    shows. An index past the program, such as a contract import, has none. -/
def evidenceConstants (evidence : List MethodEvidence) (index : Nat) : Option W32 :=
  evidence[index]?.bind fun item => constantReturn item.closed item.featureStates

/-- A readonly scalar load has exactly the width and extension of its raw field type. -/
private def staticLoadMatches (opcode : Nat) (instruction : Option RawInstruction)
    (descriptor : Option StaticDescriptor) : Bool :=
  match instruction, descriptor with
  | some instruction, some descriptor =>
    if instruction.opcode != opcode then false else
    match instruction.operand with
    | .field _ _ type _ _ => staticStorageMatches type descriptor
    | _ => false
  | _, _ => false

/-- Raw opcode of `ldsfld`. -/
private def ldsfldOpcode : Nat := 126
/-- Raw opcode of `ldsflda`. -/
private def ldsfldaOpcode : Nat := 127
/-- Raw opcode of `stsfld`. -/
private def stsfldOpcode : Nat := 128
/-- Raw opcode of `ldtoken`. -/
private def ldtokenOpcode : Nat := 208

/-- The raw instruction has `opcode` and names `field` as a static field, and the site at its pc,
    if any, carries the descriptor of `field`. -/
private def staticFieldMatches (opcode : Nat) (field : FieldRef)
    (instruction : Option RawInstruction) (descriptor : Option StaticDescriptor) : Bool :=
  match instruction with
  | some instruction => instruction.opcode == opcode &&
      instruction.operand == .field field.owner field.index field.type field.name true &&
      descriptor.all (·.field == field)
  | none => false

/-- Static field instructions agree with the raw field
    and its site descriptor, and each static load fits that descriptor. -/
def methodShapeInstructions (closed : RawMethod)
    (method : Method) : Bool :=
  let raw := FlowIndex.ofList closed.code
  let sites := firstEntryIndex method.staticSites
  method.code.zipIdx.all fun (op, pc) => match op with
    | .ldsfld field => staticFieldMatches ldsfldOpcode field (raw.get? pc) sites[pc]? &&
        staticLoadMatches ldsfldOpcode (raw.get? pc) sites[pc]?
    | .ldsflda field => staticFieldMatches ldsfldaOpcode field (raw.get? pc) sites[pc]? &&
        if (sites[pc]?.bind (·.initializer)).isSome then
          staticLoadMatches ldsfldaOpcode (raw.get? pc) sites[pc]? else true
    | .stsfld field => staticFieldMatches stsfldOpcode field (raw.get? pc) sites[pc]?
    | .ldtoken (.field field) => staticFieldMatches ldtokenOpcode field (raw.get? pc) sites[pc]?
    | _ => true

/-- Indexed instruction-shape checks agree with direct list lookups at every emitted pc. -/
theorem methodShapeInstructions_eq_scan (closed : RawMethod)
    (method : Method) :
    methodShapeInstructions closed method = method.code.zipIdx.all (fun (op, pc) =>
      match op with
      | .ldsfld field =>
          staticFieldMatches ldsfldOpcode field closed.code[pc]? (method.staticAt pc) &&
          staticLoadMatches ldsfldOpcode closed.code[pc]? (method.staticAt pc)
      | .ldsflda field =>
          staticFieldMatches ldsfldaOpcode field closed.code[pc]? (method.staticAt pc) &&
          if ((method.staticAt pc).bind (·.initializer)).isSome then
            staticLoadMatches ldsfldaOpcode closed.code[pc]? (method.staticAt pc) else true
      | .stsfld field =>
          staticFieldMatches stsfldOpcode field closed.code[pc]? (method.staticAt pc)
      | .ldtoken (.field field) =>
          staticFieldMatches ldtokenOpcode field closed.code[pc]? (method.staticAt pc)
      | _ => true) := by
  simp only [methodShapeInstructions, FlowIndex.get?_ofList, firstEntryIndex_get]
  rfl

#print axioms methodShapeInstructions_eq_scan
/-- Bind frame and return metadata, static-field instructions and all raw prefix sequences. -/
def MethodShapeValid (closed : RawMethod) (method : Method) : Prop :=
  method.profile.Valid ∧ method.returnsValue = (closed.returnType != .void) ∧
  method.locals = method.localKinds.map (LocalKind.initialValue closed.initLocals) ∧
  methodShapeInstructions closed method = true ∧
  prefixSequenceValid closed.returnType closed.code = true

instance (closed : RawMethod) (method : Method) :
    Decidable (MethodShapeValid closed method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The method's declared signature is the one its closed metadata implies. -/
def DeclaredValid (closed : RawMethod) (method : Method) : Prop :=
  method.declared = DeclaredSignature.ofRaw closed

-- Generated proofs use `rfl`, which compares the two signature literals once per method.
instance (closed : RawMethod) (method : Method) : Decidable (DeclaredValid closed method) :=
  inferInstanceAs (Decidable (_ = _))

/-- The method's environment is the program's layout tables, so every method of one extraction
    shares it. -/
def MethodEnvironmentValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (method : Method) : Prop :=
  method.environment = { rawLayouts := rawLayouts, layouts := layouts }

/-- Valid signature and environment metadata determine return narrowing independently of code. -/
theorem returnNarrow_of_shape {rawLayouts : List RawLayout}
    {layouts : Array ComputedLayout} {closed : RawMethod} {method : Method}
    (shape : MethodShapeValid closed method) (declared : DeclaredValid closed method)
    (environment : MethodEnvironmentValid rawLayouts layouts method) :
    method.returnNarrow = declaredNarrow rawLayouts closed.returnType := by
  have returns := shape.2.1
  change method.declared = _ at declared
  change method.environment = _ at environment
  by_cases void : closed.returnType = .void
  · simp [Method.returnNarrow, returns, void, declaredNarrow, typeStorage, typeStorageAt]
  · simp [Method.returnNarrow, returns, void, declared, DeclaredSignature.ofRaw, environment]

#print axioms returnNarrow_of_shape

/-- A list an option-valued function maps entirely holds at each index the image of the input
    there. -/
private theorem getElem?_of_mapM {α β : Type} {make : α → Option β} :
    ∀ {inputs : List α} {outputs : List β}, inputs.mapM make = some outputs →
      ∀ index : Nat, outputs[index]? = inputs[index]?.bind make
  | [], outputs, made, index => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at made
    subst made
    simp
  | input :: rest, outputs, made, index => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at made
    obtain ⟨output, first, others, remaining, rfl⟩ := made
    cases index with
    | zero => simp [first]
    | succ index => simp [getElem?_of_mapM remaining index]

/-- Substitution changes type arguments while preserving a scoped declaring type's assembly. -/
private theorem substituteType_headScope {arguments : List TypeExpr} {owner closed : TypeExpr}
    {scope : String} (substituted : substituteType arguments owner = some closed)
    (named : owner.headScope = some scope) : closed.headScope = some scope := by
  induction owner generalizing closed with
  | apply head arg ih _ =>
    simp only [substituteType, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at substituted
    obtain ⟨newHead, ready, _, _, rfl⟩ := substituted
    exact ih (closed := newHead) ready named
  | enum name base _ =>
    simp [substituteType, Option.map_eq_some_iff] at substituted
    obtain ⟨_, _, rfl⟩ := substituted
    exact named
  | _ =>
    first
    | solve | cases named
    | simp [substituteType] at substituted
      subst closed
      exact named

#print axioms substituteType_headScope

/-- A direct managed call retains its definition token and declaring assembly when instantiated. -/
theorem instantiateMethod_managedSite {layouts : List RawLayout} {original closed : RawMethod}
    {arguments : List TypeExpr} {pc token : Nat} {scope : String}
    {before after : RawInstruction} {source : CallSite}
    (instantiated : instantiateMethod layouts original arguments = some closed)
    (fetched : original.code[pc]? = some before) (called : before.operand = .call source)
    (managed : source.target = .managed token) (named : source.declaringType.headScope = some scope)
    (present : closed.code[pc]? = some after) :
    ∃ site, after.operand = .call site ∧ site.target = .managed token ∧
      site.declaringType.headScope = some scope := by
  unfold instantiateMethod at instantiated
  split at instantiated
  · cases instantiated
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at instantiated
    obtain ⟨_, _, _, _, _, _, code, mapped, rfl⟩ := instantiated
    change code[pc]? = some after at present
    rw [getElem?_of_mapM mapped pc, fetched] at present
    simp only [Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq, called,
      substituteOperand, Option.bind_eq_bind, Option.pure_def] at present
    obtain ⟨operand, made, rfl⟩ := present
    obtain ⟨owner, replaced, _, _, _, _, _, _, rest⟩ := made
    split at rest <;> simp [managed, substituteTarget, Option.bind_eq_some_iff] at rest
    all_goals
      obtain ⟨_, _, rfl⟩ := rest
      exact ⟨_, rfl, rfl, substituteType_headScope replaced named⟩

#print axioms instantiateMethod_managedSite

/-- Substituting type arguments into an operand keeps every branch destination. -/
theorem substituteOperand_branchesTo {arguments : List TypeExpr} {layouts : List RawLayout}
    {arity : Nat} {instruction : RawInstruction} {operand : RawOperand}
    (substituted : substituteOperand arguments layouts arity instruction.operand = some operand)
    (target : Nat) :
    branchesTo target { instruction with operand } = branchesTo target instruction := by
  rcases instruction with ⟨offset, opcode, original⟩
  cases original
  case target destination =>
    simp only [substituteOperand, Option.some.injEq] at substituted
    subst substituted; rfl
  case targets destinations =>
    simp only [substituteOperand, Option.some.injEq] at substituted
    subst substituted; rfl
  all_goals
    simp only [branchesTo]
    cases operand <;> try rfl
  all_goals (try simp [substituteOperand, Option.bind_eq_some_iff] at substituted)
  all_goals
    obtain ⟨_, _, _, _, _, _, _, _, rest⟩ := substituted
    split at rest <;> simp [Option.bind_eq_some_iff] at rest

#print axioms substituteOperand_branchesTo

/-- Instantiation keeps every opcode and branch destination, so it keeps `PrefixEntryFree`. -/
theorem instantiateMethod_prefixEntryFree {layouts : List RawLayout} {original closed : RawMethod}
    {arguments : List TypeExpr}
    (instantiated : instantiateMethod layouts original arguments = some closed)
    (free : PrefixEntryFree original.code) : PrefixEntryFree closed.code := by
  unfold instantiateMethod at instantiated
  split at instantiated
  · cases instantiated
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at instantiated
    obtain ⟨_, _, _, _, _, _, code, substituted, rfl⟩ := instantiated
    have entries := getElem?_of_mapM substituted
    have closedAt : ∀ (index : Nat) (instruction : RawInstruction),
        code[index]? = some instruction →
        ∃ source operand, original.code[index]? = some source ∧
          substituteOperand arguments layouts original.genericParameters.length source.operand =
            some operand ∧ instruction = { source with operand } := by
      intro index instruction found
      rw [entries index] at found
      cases source : original.code[index]? with
      | none => simp [source] at found
      | some source' =>
        simp only [source, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at found
        obtain ⟨operand, substitutedHere, rfl⟩ := found
        exact ⟨source', operand, rfl, substitutedHere, rfl⟩
    intro pc instruction fetched isPrefix
    obtain ⟨source, _, sourceAt, _, rfl⟩ := closedAt pc instruction fetched
    have clear := free pc source sourceAt isPrefix
    rw [List.any_eq_false] at clear ⊢
    intro other member branches
    obtain ⟨position, otherAt⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨otherSource, operand, otherSourceAt, otherSubstituted, rfl⟩ :=
      closedAt position other otherAt
    rw [substituteOperand_branchesTo otherSubstituted] at branches
    exact clear otherSource (List.mem_of_getElem? otherSourceAt) branches

#print axioms instantiateMethod_prefixEntryFree

/-- A storage native dispatch chooses is a callable that never narrows, for a pointer type,
    which never narrows either. -/
private theorem nativeDispatchStorage_narrow (context : NativeDispatchContext) (type : TypeExpr)
    (storage : StorageType) (chosen : nativeDispatchStorage context type = some storage) :
    storage.narrow = none ∧ type.narrowCandidate = false := by
  unfold nativeDispatchStorage at chosen
  cases signature : context.signature with
  | none => simp [signature] at chosen
  | some value =>
    simp only [signature, Option.bind_eq_bind, Option.bind_some] at chosen
    cases type <;> simp_all [Option.any, TypeExpr.narrowCandidate] <;>
      (try split at chosen) <;> simp_all [StorageType.narrow]
    all_goals (obtain ⟨_, rfl⟩ := chosen; rfl)

/-- The storage a specialization gives a parameter narrows exactly as its declared type does. -/
theorem parameterStorage_narrow (layouts : List RawLayout) (context : NativeDispatchContext)
    (type : TypeExpr) (storage : StorageType)
    (stored : (nativeDispatchStorage context type <|> typeStorage layouts type) = some storage) :
    storage.narrow = declaredNarrow layouts type := by
  cases native : nativeDispatchStorage context type with
  | some chosen =>
    rw [native] at stored
    simp only [Option.some.injEq, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at stored
    subst stored
    obtain ⟨wide, shape⟩ := nativeDispatchStorage_narrow context type chosen native
    rw [wide, declaredNarrow_of_not_candidate _ _ shape]
  | none =>
    rw [native] at stored
    simp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at stored
    rw [declaredNarrow_eq_storage, stored]
    rfl

#print axioms parameterStorage_narrow

/-- Under validated evidence an argument without a home is read narrowed exactly as its raw
    storage narrows, so `ldarg` reads it as the evidence check's storage says. -/
theorem argumentAccess_of_evidence {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {original closed : RawMethod} {typeArguments : List TypeExpr} {raw : RawArguments}
    {reachable : List Bool} {method : Method} {index : Nat} {type : StorageType}
    (specialized : SpecializationValid rawLayouts original typeArguments closed raw)
    (declared : DeclaredValid closed method)
    (environment : MethodEnvironmentValid rawLayouts layouts method)
    (homes : ParameterHomesValid layouts raw reachable method)
    (unhomed : index ∉ requiredHomeIndices raw reachable)
    (found : raw.arguments[index]? = some type) :
    method.argumentAccess index = .value type.narrow := by
  have absent : method.parameterHomes.findIdx? (fun home => home.1 == index) = none := by
    rw [homeKeys_findIdx? homes.2.2.2.2.1, List.findIdx?_eq_none_iff]
    intro required member
    rw [beq_eq_false_iff_ne]
    intro same
    exact unhomed (same ▸ member)
  change method.declared = _ at declared
  change method.environment = _ at environment
  have closedEq := specialized.2
  rw [closedArguments_eq_list] at closedEq
  simp only [closedArgumentsWith, Option.bind_eq_some_iff, bind, pure, Option.some.injEq]
    at closedEq
  obtain ⟨parameters, mapped, _, _, _, _, rfl⟩ := closedEq
  simp only [Method.argumentAccess, absent, declared, environment, DeclaredSignature.ofRaw]
  congr 1
  have entry := getElem?_of_mapM mapped
  by_cases receiver : closed.hasThis
  · simp only [receiver, ite_true] at found ⊢
    cases index with
    | zero =>
      simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      split <;> rfl
    | succ position =>
      simp only [List.cons_append, List.getElem?_cons_succ, List.nil_append] at found
      rw [entry position] at found
      simp only [DeclaredSignature.argumentType]
      cases parameter : closed.parameters[position]? with
      | none => simp [parameter] at found
      | some declaredType =>
        simp only [parameter, Option.bind_some] at found ⊢
        exact (parameterStorage_narrow _ _ _ _ found).symm
  · simp only [receiver, Bool.false_eq_true, ite_false, List.nil_append] at found ⊢
    rw [entry index] at found
    simp only [DeclaredSignature.argumentType]
    cases parameter : closed.parameters[index]? with
    | none => simp [parameter] at found
    | some declaredType =>
      simp only [parameter, Option.bind_some] at found ⊢
      exact (parameterStorage_narrow _ _ _ _ found).symm

#print axioms argumentAccess_of_evidence

-- Generated proofs use `rfl`, which unfolds the two shared constants; deciding this instance
-- compares the layout tables element by element, once per method.
instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout) (method : Method) :
    Decidable (MethodEnvironmentValid rawLayouts layouts method) :=
  inferInstanceAs (Decidable (_ = _))

/-- One emitted method against its evidence record: every per-method validator, in the
    order generated modules supply their proofs. `pins` are the assemblies the extraction pins,
    shared by every method. -/
def MethodEvidenceValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (platform : PlatformTable) (all : List MethodEvidence)
    (imports : List ImportSlot)
    (item : MethodEvidence) (method : Method) : Prop :=
  SpecializationValid rawLayouts item.original item.arguments item.closed item.parameterInput ∧
  ParameterHomesValid layouts item.parameterInput item.reachable method ∧
  MethodLayoutsValid rawLayouts layouts method item.layoutUses ∧
  FeatureFlowValid rawLayouts.toArray (evidenceConstants all) (linkIndex method) item.closed
    method.profile item.featureStates item.reachable method.code ∧
  ManagedCallsValid (specializationTable all) imports (callModelled method)
    (lowerConstrainedRaw item.dispatchTypes item.closed) item.reachable method ∧
  LayoutUsesComplete rawLayouts item.closed item.parameterInput item.reachable item.layoutUses ∧
  MethodShapeValid item.closed method ∧
  UnsafeCallsValid item.closed item.reachable method.code ∧
  Method.ofClosed? method.profile method.environment item.links item.reachable item.closed
    item.parameterInput = .ok method ∧
  OpaqueLocalsValid item.closed method ∧
  ObjectOperandsValid item.closed item.reachable method ∧
  (ScalarFlowValid item.closed item.featureStates item.scalarStates method.code ∧
    method.code =
      methodCode method.profile method.environment method.links item.reachable item.closed) ∧
  ConstrainedCallsValid item.dispatchTypes (specializationTable all) item.closed item.reachable
    method ∧
  BodyDecodes pins platform item.assembly item.body item.original item.arguments item.signature
    ((ImportSlotIndex.ofList imports).forLinks all.length method.links) /\
  MethodEnvironmentValid rawLayouts layouts method ∧
  DeclaredValid item.closed method ∧ item.links = method.links

instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (platform : PlatformTable) (all : List MethodEvidence)
    (imports : List ImportSlot)
    (item : MethodEvidence) (method : Method) :
    Decidable (MethodEvidenceValid rawLayouts layouts pins platform all imports item method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    _))

/-- The record supplies exactly the executable links checked for its method. -/
theorem MethodEvidenceValid.links_eq {rawLayouts layouts pins platform all imports item method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method) :
    item.links = method.links := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, links⟩ := valid
  exact links
#print axioms MethodEvidenceValid.links_eq

/-- Validated evidence decodes at its own links and mask to the complete executable method. -/
theorem MethodEvidenceValid.decoded {rawLayouts layouts pins platform all imports item method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method) :
    Method.ofClosed? method.profile method.environment item.links item.reachable item.closed
      item.parameterInput = .ok method := by
  obtain ⟨-, -, -, -, -, -, -, -, decoded, -⟩ := valid
  exact decoded

#print axioms MethodEvidenceValid.decoded

/-- A validated method retains the identities, bytes and initializers of its checked static
    sites. -/
theorem MethodEvidenceValid.staticSites_eq {rawLayouts layouts pins platform all imports item method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method) :
    method.staticSites = item.closed.staticDescriptors := by
  exact (Method.ofClosed?_fields valid.decoded).2

#print axioms MethodEvidenceValid.staticSites_eq

/-- Validated evidence runs under a valid feature profile, which its shape check states. -/
theorem MethodEvidenceValid.profile_valid {rawLayouts layouts pins platform all imports item method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method) :
    method.profile.Valid := by
  obtain ⟨-, -, -, -, -, -, shape, -⟩ := valid
  exact shape.1
#print axioms MethodEvidenceValid.profile_valid

/-- A validated record binds every emitted instruction to its decoding. -/
theorem MethodEvidenceValid.code_eq {rawLayouts : List RawLayout}
    {layouts : Array ComputedLayout} {pins : List AssemblyPin} {all : List MethodEvidence}
    {imports : List ImportSlot} {item : MethodEvidence} {method : Method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method) : method.code =
      methodCode method.profile method.environment method.links item.reachable item.closed := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨_, same⟩, _⟩ := valid
  exact same

#print axioms MethodEvidenceValid.code_eq

/-- The runtime catalog agrees with every call of a validated method. -/
theorem MethodEvidenceValid.modelsAgree {rawLayouts layouts pins platform all imports item method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method) :
    RuntimeModelsAgree item.closed item.reachable method := by
  have decoded := valid.decoded
  rw [valid.links_eq] at decoded
  obtain ⟨-, -, -, features, -⟩ := valid
  exact RuntimeModelsAgree.of_closed decoded features

#print axioms MethodEvidenceValid.modelsAgree

/-- Every reachable method-token call outside a fold in validated evidence has a raw claim. -/
theorem MethodEvidenceValid.siteClaimTotal {rawLayouts : List RawLayout}
    {layouts : Array ComputedLayout} {pins : List AssemblyPin} {all : List MethodEvidence}
    {imports : List ImportSlot} {item : MethodEvidence} {method : Method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method)
    {pc : Nat} {raw : RawInstruction} (atRaw : item.closed.code[pc]? = some raw)
    (atLive : item.reachable[pc]? = some true) :
    SiteClaimTotal method.environment (method.linkAt pc) raw true
      ((foldRoles item.closed.code)[pc]?.join) := by
  exact valid.modelsAgree.siteClaimTotal atRaw atLive

#print axioms MethodEvidenceValid.siteClaimTotal

/-- At a reachable pc that a fold owns, validated evidence emits the instruction its role fixes. -/
theorem MethodEvidenceValid.foldOwnedSite {rawLayouts : List RawLayout}
    {layouts : Array ComputedLayout} {pins : List AssemblyPin} {all : List MethodEvidence}
    {imports : List ImportSlot} {item : MethodEvidence} {method : Method}
    (valid : MethodEvidenceValid rawLayouts layouts pins platform all imports item method)
    {pc : Nat} {raw : RawInstruction} {emitted : Instruction}
    (atRaw : item.closed.code[pc]? = some raw) (atLive : item.reachable[pc]? = some true)
    (atCode : method.code[pc]? = some emitted)
    (owned : foldOwnsSite ((foldRoles item.closed.code)[pc]?.join) = true) :
    ((foldRoles item.closed.code)[pc]?.join).bind
      (Instruction.ofRole? · none raw) = some emitted := by
  exact valid.modelsAgree.foldOwnedSite atRaw atLive atCode owned

#print axioms MethodEvidenceValid.foldOwnedSite

/-- `MethodEvidenceValid` for a program lookup; a missing method fails. -/
private def MethodAtValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (platform : PlatformTable) (all : List MethodEvidence)
    (imports : List ImportSlot)
    (item : MethodEvidence) (method : Option Method) : Prop :=
  match method with
  | none => False
  | some value => MethodEvidenceValid rawLayouts layouts pins platform all imports item value

private instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (platform : PlatformTable) (all : List MethodEvidence)
    (imports : List ImportSlot)
    (item : MethodEvidence) (method : Option Method) :
    Decidable (MethodAtValid rawLayouts layouts pins platform all imports item method) := by
  cases method <;> dsimp [MethodAtValid] <;> infer_instance

/-- The architecture layouts are computed for: the first method's profile, or `.scalar` for
    an empty program. -/
abbrev programArchitecture (program : Program) : Architecture :=
  ((program.head?).map fun method => method.profile.architecture).getD .scalar

/-- Every type in a dispatch catalog comes from one of the certificate's input assemblies. -/
def DispatchPinsValid (pins : List AssemblyPin) (evidence : List MethodEvidence) : Bool :=
  evidence.all fun item => item.dispatchTypes.all fun type => pins.contains type.assembly

/-- The certificate covers the entire emitted program, with no optional method list; calls
    past it must match `imports`, and every body is checked against the one list of `pins` and
    the one list of `platform` definitions. -/
def TranslationValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (platform : PlatformTable) (evidence : List MethodEvidence)
    (imports : List ImportSlot) (program : Program) : Prop :=
  LayoutsValid rawLayouts layouts (programArchitecture program) ∧
    evidence.length = program.length ∧
  (∀ index : Fin evidence.length,
    MethodAtValid rawLayouts layouts pins platform evidence imports evidence[index]
      program[index.val]?) ∧
  StaticValuesValid program ∧
  StaticIdentitiesValid program (evidence.map (·.body)) ∧
  ImportedLayoutsValid imports (programArchitecture program) ∧
  ImportedLocalLayoutsBound rawLayouts layouts imports ∧
  AttributionValid (bodyOwners evidence) = true ∧ DispatchPinsValid pins evidence = true

instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (platform : PlatformTable) (evidence : List MethodEvidence)
    (imports : List ImportSlot) (program : Program) :
    Decidable (TranslationValid rawLayouts layouts pins platform evidence imports program) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Compose independently checked methods without reducing their validators again. -/
inductive MethodsChecked (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (platform : PlatformTable) (all : List MethodEvidence)
    (imports : List ImportSlot) :
    List MethodEvidence → Program → Prop where
  | nil : MethodsChecked rawLayouts layouts pins platform all imports [] []
  | cons {item rest method program} :
      MethodEvidenceValid rawLayouts layouts pins platform all imports item method →
      MethodsChecked rawLayouts layouts pins platform all imports rest program →
      MethodsChecked rawLayouts layouts pins platform all imports (item :: rest)
        (method :: program)

/-- Assembles `TranslationValid` from the program-wide checks and per-method proofs. -/
theorem translation_of_methods {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {pins : List AssemblyPin} {platform : PlatformTable} {evidence : List MethodEvidence}
    {imports : List ImportSlot}
    {program : Program}
    (layout : LayoutsValid rawLayouts layouts (programArchitecture program))
    (statics : StaticValuesValid program)
    (identities : StaticIdentitiesValid program (evidence.map (·.body)))
    (importLayouts : ImportedLayoutsValid imports (programArchitecture program))
    (importedLocals : ImportedLocalLayoutsBound rawLayouts layouts imports)
    (attribution : AttributionValid (bodyOwners evidence) = true)
    (dispatchPins : DispatchPinsValid pins evidence = true)
    (methods : MethodsChecked rawLayouts layouts pins platform evidence imports evidence program) :
    TranslationValid rawLayouts layouts pins platform evidence imports program := by
  have compose {items code}
      (checked : MethodsChecked rawLayouts layouts pins platform evidence imports items code) :
      items.length = code.length ∧ ∀ index : Fin items.length,
        MethodAtValid rawLayouts layouts pins platform evidence imports items[index]
          code[index.val]? := by
    induction checked with
    | nil => exact ⟨rfl, fun index => Fin.elim0 index⟩
    | @cons item rest method code valid tail ih =>
      refine ⟨congrArg Nat.succ ih.1, ?_⟩
      intro ⟨index, bound⟩
      cases index with
      | zero => exact valid
      | succ index => exact ih.2 ⟨index, Nat.lt_of_succ_lt_succ bound⟩
  exact ⟨layout, (compose methods).1, (compose methods).2, statics, identities, importLayouts,
    importedLocals, attribution, dispatchPins⟩

/-- Each method of a valid translation passes every per-method validator. -/
theorem translation_method_checked {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {pins : List AssemblyPin} {platform : PlatformTable} {evidence : List MethodEvidence}
    {imports : List ImportSlot}
    {program : Program}
    (valid : TranslationValid rawLayouts layouts pins platform evidence imports program)
    (index : Fin evidence.length) (method : Method) (found : program[index.val]? = some method) :
    MethodEvidenceValid rawLayouts layouts pins platform evidence imports evidence[index]
      method := by
  have checked := valid.2.2.1 index
  simpa [MethodAtValid, found] using checked

#print axioms translation_method_checked
#print axioms translation_of_methods
end CIL.Extraction
