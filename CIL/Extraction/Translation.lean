import CIL.Extraction.Scalars
import CIL.Extraction.LayoutCoverage
import CIL.Extraction.UnsafeCalls
import CIL.Extraction.ExactIntrinsics
import CIL.Extraction.VectorInitialization
import CIL.Extraction.StaticValues
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
against its evidence record, static values are reproduced by their initializers, import
layouts agree, every body is owned by the pinned assembly its evidence names, and every decoded
method definition is what its body bytes and carried metadata say. It is not a simulation proof for
every raw opcode; general instruction translation, that the carried metadata rows are the image's,
definitions in platform assemblies and the PE container stay trusted, as `docs/SOUNDNESS.md`
describes.

Generated modules prove each method's evidence separately and assemble it with
`translation_of_methods`, so no validator is reduced twice.
-/

namespace CIL.Extraction

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

/-- The pin and owner identity of every original and closed body, for attribution checks. -/
def bodyOwners (evidence : List MethodEvidence) : List (AssemblyPin × String) :=
  evidence.flatMap fun item =>
    [(item.assembly, item.original.owner), (item.assembly, item.closed.owner)]

/-- The program's method table, as the call check sees it. -/
def specializationTable (evidence : List MethodEvidence) : List SpecializedMethod :=
  evidence.map fun item => ⟨item.arguments, item.closed⟩

/-- The word each program method returns, by emitted index, as its own feature certificate
    shows. An index past the program, such as a contract import, has none. -/
def evidenceConstants (evidence : List MethodEvidence) (index : Nat) : Option W32 :=
  evidence[index]?.bind fun item => constantReturn item.closed item.featureStates

/-- The zero value of each local kind, used when the method zero-initializes its locals. -/
private def initialLocal : LocalKind → Value
  | .reference | .span .. | .array _ | .methodPointer _ | .methodTable _ | .object => .nullRef
  | .byte => .i8 0
  | .narrow _ | .word32 => .i32 0
  | .word64 => .i64 0
  | .vector128 => .v128 0
  | .vector256 => .v256 0
  | .vector512 => .v512 0
  | .aggregate size => .aggregate (List.replicate size.val 0)

/-- The value a local of `kind` starts with: its zero when the body initializes locals. -/
def _root_.CIL.LocalKind.initialValue (initLocals : Bool) (kind : LocalKind) : Value :=
  if initLocals then initialLocal kind else .unmodeled

/-- Integer static-field storage and its narrow-load signedness. -/
private def staticScalarType : TypeExpr → Option (Nat × Bool)
  | .enum _ underlying => staticScalarType underlying
  | .atom scope name =>
    if scope != runtimeScope then none else
    match name with
    | "System.SByte" => some (1, true)
    | "System.Byte" | "System.Boolean" => some (1, false)
    | "System.Int16" => some (2, true)
    | "System.UInt16" | "System.Char" => some (2, false)
    | "System.Int32" | "System.UInt32" => some (4, false)
    | "System.Int64" | "System.UInt64" | "System.IntPtr" | "System.UIntPtr" => some (8, false)
    | _ => none
  | _ => none

/-- A readonly scalar load has exactly the width and extension of its raw field type. -/
private def staticLoadMatches (opcode : Nat) (instruction : Option RawInstruction)
    (descriptor : Option StaticDescriptor) : Bool :=
  match instruction, descriptor with
  | some instruction, some descriptor =>
    if instruction.opcode != opcode then false else
    match instruction.operand with
    | .field _ _ type _ _ =>
      match staticScalarType type with
      | some (width, signed) => descriptor.bytes.length == width && descriptor.scalar == some signed
      | none => descriptor.scalar.isNone
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

/-- The raw instruction has `opcode` and names `field` as a static field. -/
private def staticFieldMatches (opcode : Nat) (field : FieldRef)
    (instruction : Option RawInstruction) : Bool :=
  match instruction with
  | some instruction => instruction.opcode == opcode &&
      instruction.operand == .field field.owner field.index field.type field.name true
  | none => false

/-- Every static field instruction names the field of the raw instruction at its pc, and every
    static load fits the descriptor bound there, using precomputed instruction and site indexes. -/
def methodShapeInstructions (closed : RawMethod)
    (method : Method) : Bool :=
  let raw := FlowIndex.ofList closed.code
  let sites := firstEntryIndex method.staticSites
  method.code.zipIdx.all fun (op, pc) => match op with
    | .ldsfld field => staticFieldMatches ldsfldOpcode field (raw.get? pc) &&
        staticLoadMatches ldsfldOpcode (raw.get? pc) sites[pc]?
    | .ldsflda field => staticFieldMatches ldsfldaOpcode field (raw.get? pc) &&
        if (sites[pc]?.bind (·.initializer)).isSome then
          staticLoadMatches ldsfldaOpcode (raw.get? pc) sites[pc]? else true
    | .stsfld field => staticFieldMatches stsfldOpcode field (raw.get? pc)
    | .ldtoken (.field field) => staticFieldMatches ldtokenOpcode field (raw.get? pc)
    | _ => true

/-- Indexed instruction-shape checks agree with direct list lookups at every emitted pc. -/
theorem methodShapeInstructions_eq_scan (closed : RawMethod)
    (method : Method) :
    methodShapeInstructions closed method = method.code.zipIdx.all (fun (op, pc) =>
      match op with
      | .ldsfld field => staticFieldMatches ldsfldOpcode field closed.code[pc]? &&
          staticLoadMatches ldsfldOpcode closed.code[pc]? (method.staticAt pc)
      | .ldsflda field => staticFieldMatches ldsfldaOpcode field closed.code[pc]? &&
          if ((method.staticAt pc).bind (·.initializer)).isSome then
            staticLoadMatches ldsfldaOpcode closed.code[pc]? (method.staticAt pc) else true
      | .stsfld field => staticFieldMatches stsfldOpcode field closed.code[pc]?
      | .ldtoken (.field field) => staticFieldMatches ldtokenOpcode field closed.code[pc]?
      | _ => true) := by
  simp only [methodShapeInstructions, FlowIndex.get?_ofList, firstEntryIndex_get]
  rfl

#print axioms methodShapeInstructions_eq_scan
/-- The declared signature a closed raw method implies: its receiver kind, parameter types,
    return type and localsinit flag. Instantiation and metadata binding refuse explicit receiver
    signatures. -/
def _root_.CIL.DeclaredSignature.ofRaw (closed : RawMethod) : DeclaredSignature where
  receiver :=
    if closed.hasThis then some (if closed.objectReceiver then .object else .reference) else none
  parameters := closed.parameters
  returnType := closed.returnType
  initLocals := closed.initLocals

/-- Bind non-instruction method fields that affect frame setup and return behavior. -/
def MethodShapeValid (closed : RawMethod) (method : Method) : Prop :=
  method.profile.Valid ∧ method.returnsValue = (closed.returnType != .void) ∧
  method.locals = method.localKinds.map (LocalKind.initialValue closed.initLocals) ∧
  methodShapeInstructions closed method = true

instance (closed : RawMethod) (method : Method) :
    Decidable (MethodShapeValid closed method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

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
  · simp [Method.returnNarrow, returns, void, declaredNarrow, typeStorage]
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
    (pins : List AssemblyPin) (all : List MethodEvidence) (imports : List ImportSlot)
    (item : MethodEvidence) (method : Method) : Prop :=
  SpecializationValid rawLayouts item.original item.arguments item.closed item.parameterInput ∧
  ParameterHomesValid layouts item.parameterInput item.reachable method ∧
  MethodLayoutsValid rawLayouts layouts method item.layoutUses ∧
  FeatureFlowValid rawLayouts.toArray (evidenceConstants all) item.closed method.profile
    item.featureStates item.reachable method.code ∧
  ManagedCallsValid (specializationTable all) imports
    (lowerConstrainedRaw item.dispatchTypes item.closed) item.reachable method ∧
  LayoutUsesComplete rawLayouts item.closed item.parameterInput item.reachable item.layoutUses ∧
  MethodShapeValid item.closed method ∧
  UnsafeCallsValid rawLayouts item.closed item.reachable method.code ∧
  ExactIntrinsicsValid item.closed item.reachable method ∧
  OpaqueLocalsValid item.closed method ∧
  VectorInitializationsValid item.closed item.reachable method ∧
  ScalarFlowValid rawLayouts.toArray item.closed item.featureStates item.scalarStates method.code ∧
  ConstrainedCallsValid item.dispatchTypes (specializationTable all) item.closed item.reachable
    method ∧
  BodyDecodes pins item.assembly item.body item.original item.arguments item.signature ∧
  MethodEnvironmentValid rawLayouts layouts method ∧
  DeclaredValid item.closed method

instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (all : List MethodEvidence) (imports : List ImportSlot)
    (item : MethodEvidence) (method : Method) :
    Decidable (MethodEvidenceValid rawLayouts layouts pins all imports item method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- `MethodEvidenceValid` for a program lookup; a missing method fails. -/
private def MethodAtValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (all : List MethodEvidence) (imports : List ImportSlot)
    (item : MethodEvidence) (method : Option Method) : Prop :=
  match method with
  | none => False
  | some value => MethodEvidenceValid rawLayouts layouts pins all imports item value

private instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (all : List MethodEvidence) (imports : List ImportSlot)
    (item : MethodEvidence) (method : Option Method) :
    Decidable (MethodAtValid rawLayouts layouts pins all imports item method) := by
  cases method <;> dsimp [MethodAtValid] <;> infer_instance

/-- The architecture layouts are computed for: the first method's profile, or `.scalar` for
    an empty program. -/
abbrev programArchitecture (program : Program) : Architecture :=
  ((program.head?).map fun method => method.profile.architecture).getD .scalar

/-- The certificate covers the entire emitted program, with no optional method list; calls
    past it must match `imports`, and every body is checked against the one list of `pins`. -/
def TranslationValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (evidence : List MethodEvidence) (imports : List ImportSlot)
    (program : Program) : Prop :=
  LayoutsValid rawLayouts layouts (programArchitecture program) ∧
    evidence.length = program.length ∧
  (∀ index : Fin evidence.length,
    MethodAtValid rawLayouts layouts pins evidence imports evidence[index]
      program[index.val]?) ∧
  StaticValuesValid program ∧
  ImportedLayoutsValid imports (programArchitecture program) ∧
  ImportedLocalLayoutsBound rawLayouts layouts imports ∧
  AttributionValid (bodyOwners evidence) = true

instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (evidence : List MethodEvidence) (imports : List ImportSlot)
    (program : Program) :
    Decidable (TranslationValid rawLayouts layouts pins evidence imports program) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Compose independently checked methods without reducing their validators again. -/
inductive MethodsChecked (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (pins : List AssemblyPin) (all : List MethodEvidence) (imports : List ImportSlot) :
    List MethodEvidence → Program → Prop where
  | nil : MethodsChecked rawLayouts layouts pins all imports [] []
  | cons {item rest method program} :
      MethodEvidenceValid rawLayouts layouts pins all imports item method →
      MethodsChecked rawLayouts layouts pins all imports rest program →
      MethodsChecked rawLayouts layouts pins all imports (item :: rest) (method :: program)

/-- Assembles `TranslationValid` from the program-wide checks and per-method proofs. -/
theorem translation_of_methods {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {pins : List AssemblyPin} {evidence : List MethodEvidence} {imports : List ImportSlot}
    {program : Program}
    (layout : LayoutsValid rawLayouts layouts (programArchitecture program))
    (statics : StaticValuesValid program)
    (importLayouts : ImportedLayoutsValid imports (programArchitecture program))
    (importedLocals : ImportedLocalLayoutsBound rawLayouts layouts imports)
    (attribution : AttributionValid (bodyOwners evidence) = true)
    (methods : MethodsChecked rawLayouts layouts pins evidence imports evidence program) :
    TranslationValid rawLayouts layouts pins evidence imports program := by
  have compose {items code}
      (checked : MethodsChecked rawLayouts layouts pins evidence imports items code) :
      items.length = code.length ∧ ∀ index : Fin items.length,
        MethodAtValid rawLayouts layouts pins evidence imports items[index]
          code[index.val]? := by
    induction checked with
    | nil => exact ⟨rfl, fun index => Fin.elim0 index⟩
    | @cons item rest method code valid tail ih =>
      refine ⟨congrArg Nat.succ ih.1, ?_⟩
      intro ⟨index, bound⟩
      cases index with
      | zero => exact valid
      | succ index => exact ih.2 ⟨index, Nat.lt_of_succ_lt_succ bound⟩
  exact ⟨layout, (compose methods).1, (compose methods).2, statics, importLayouts,
    importedLocals, attribution⟩

/-- Each method of a valid translation passes every per-method validator. -/
theorem translation_method_checked {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {pins : List AssemblyPin} {evidence : List MethodEvidence} {imports : List ImportSlot}
    {program : Program} (valid : TranslationValid rawLayouts layouts pins evidence imports program)
    (index : Fin evidence.length) (method : Method) (found : program[index.val]? = some method) :
    MethodEvidenceValid rawLayouts layouts pins evidence imports evidence[index] method := by
  have checked := valid.2.2.1 index
  simpa [MethodAtValid, found] using checked

#print axioms translation_method_checked
#print axioms translation_of_methods
end CIL.Extraction
