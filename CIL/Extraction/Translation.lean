import CIL.Extraction.Scalars
import CIL.Extraction.LayoutCoverage
import CIL.Extraction.UnsafeCalls
import CIL.Extraction.DivisionIntrinsics
import CIL.Extraction.VectorInitialization
import CIL.Extraction.StaticValues
import CIL.Extraction.ImportLayouts
import CIL.Extraction.Constrained
import Std.Data.TreeMap.Lemmas

/-!
# Translation validity

The top of the extraction checks. `TranslationValid` conjoins the kernel-checked validators
for one extraction: layouts recompute, every emitted method passes the per-method validators
against its evidence record, static values are reproduced by their initializers, and import
layouts agree. It is not a simulation proof for every raw opcode; general instruction
translation and metadata decoding stay trusted, as `docs/SOUNDNESS.md` describes.

Generated modules prove each method's evidence separately and assemble it with
`translation_of_methods`, so no validator is reduced twice.
-/

namespace CIL.Extraction

/-- Every extracted method has exactly one record, in emitted program order. -/
structure MethodEvidence where
  original : RawMethod
  arguments : List TypeExpr
  closed : RawMethod
  parameterInput : RawArguments
  reachable : List Bool
  featureStates : FeatureCertificate
  scalarStates : ScalarCertificate
  layoutUses : List LayoutUse
  dispatchTypes : List DispatchType := []

/-- The program's method table, as the call check sees it. -/
def specializationTable (evidence : List MethodEvidence) : List SpecializedMethod :=
  evidence.map fun item => ⟨item.arguments, item.closed⟩

/-- The zero value of each local kind, used when the method zero-initializes its locals. -/
private def initialLocal : LocalKind → Value
  | .reference | .span .. | .array _ | .methodPointer _ | .methodTable _ => .nullRef
  | .byte => .i8 0
  | .narrow _ | .word32 => .i32 0
  | .word64 => .i64 0
  | .vector128 => .v128 0
  | .vector256 => .v256 0
  | .vector512 => .v512 0
  | .aggregate size => .aggregate (List.replicate size.val 0)

/-- Narrow return conversion is part of the closed metadata signature. -/
def returnNarrow (layouts : List RawLayout) (type : TypeExpr) : Option NarrowKind := do
  let .field field ← typeStorage layouts type | none
  match field with
  | .signed8 => some .signed8
  | .unsigned8 | .boolean => some .unsigned8
  | .signed16 => some .signed16
  | .unsigned16 | .character => some .unsigned16
  | _ => none

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

/-- Index static sites with the same first-match behavior as the metadata list. -/
private def staticSiteIndex : List (Nat × StaticDescriptor) → Std.TreeMap Nat StaticDescriptor
  | [] => ∅
  | (pc, descriptor) :: sites => (staticSiteIndex sites).insert pc descriptor

/-- Duplicate sites retain the first descriptor, including malformed evidence. -/
private theorem staticSiteIndex_get (sites : List (Nat × StaticDescriptor)) (pc : Nat) :
    (staticSiteIndex sites)[pc]? = (sites.find? (fun site => site.1 == pc)).map Prod.snd := by
  induction sites with
  | nil => simp [staticSiteIndex]
  | cons site sites ih =>
    rcases site with ⟨index, descriptor⟩
    simp only [staticSiteIndex, Std.TreeMap.getElem?_insert, List.find?_cons]
    by_cases same : index = pc
    · subst index; simp
    · have different : (index == pc) = false := beq_eq_false_iff_ne.mpr same
      simp [same, ih, different]

#print axioms staticSiteIndex_get

/-- A readonly scalar load has exactly the width and extension of its raw field type. -/
private def staticLoadMatches (instruction : Option RawInstruction)
    (descriptor : Option StaticDescriptor) : Bool :=
  match instruction, descriptor with
  | some instruction, some descriptor =>
    if instruction.opcode != 126 then false else
    match instruction.operand with
    | .field _ _ type _ =>
      match staticScalarType type with
      | some (width, signed) => descriptor.bytes.length == width && descriptor.scalar == some signed
      | none => descriptor.scalar.isNone
    | _ => false
  | _, _ => false

/-- Check return conversions and static loads using precomputed instruction and site indexes. -/
def methodShapeInstructions (layouts : List RawLayout) (closed : RawMethod)
    (method : Method) : Bool :=
  let raw := FlowIndex.ofList closed.code
  let sites := staticSiteIndex method.staticSites
  method.code.zipIdx.all fun (op, pc) => match op with
    | .ret narrow => narrow == returnNarrow layouts closed.returnType
    | .memory (.staticValue _) => staticLoadMatches (raw.get? pc) sites[pc]?
    | _ => true

/-- Indexed instruction-shape checks agree with direct list lookups at every emitted pc. -/
theorem methodShapeInstructions_eq_scan (layouts : List RawLayout) (closed : RawMethod)
    (method : Method) :
    methodShapeInstructions layouts closed method = method.code.zipIdx.all (fun (op, pc) =>
      match op with
      | .ret narrow => narrow == returnNarrow layouts closed.returnType
      | .memory (.staticValue _) => staticLoadMatches closed.code[pc]?
          ((method.staticSites.find? (fun site => site.1 == pc)).map Prod.snd)
      | _ => true) := by
  simp only [methodShapeInstructions, FlowIndex.get?_ofList, staticSiteIndex_get]

#print axioms methodShapeInstructions_eq_scan
/-- Bind non-instruction method fields that affect frame setup and return behavior. -/
def MethodShapeValid (layouts : List RawLayout) (closed : RawMethod) (method : Method) : Prop :=
  method.profile.Valid ∧ method.returnsValue = (closed.returnType != .void) ∧
  method.locals = method.localKinds.map (fun kind =>
    if closed.initLocals then initialLocal kind else .unmodeled) ∧
  method.vectorLocals = [] ∧ method.vectorArgs = [] ∧
  methodShapeInstructions layouts closed method = true

instance (layouts : List RawLayout) (closed : RawMethod) (method : Method) :
    Decidable (MethodShapeValid layouts closed method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- One emitted method against its evidence record: every per-method validator, in the
    order generated modules supply their proofs. -/
def MethodEvidenceValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (imports : List ImportSlot) (item : MethodEvidence)
    (method : Method) : Prop :=
  SpecializationValid rawLayouts item.original item.arguments item.closed item.parameterInput ∧
  ParameterHomesValid layouts item.parameterInput item.reachable method ∧
  MethodLayoutsValid rawLayouts layouts method item.layoutUses ∧
  FeatureFlowValid item.closed method.profile item.featureStates item.reachable method.code ∧
  ManagedCallsValid (specializationTable all) imports
    (lowerConstrainedRaw item.dispatchTypes item.closed) item.reachable method ∧
  LayoutUsesComplete rawLayouts item.closed item.parameterInput item.reachable item.layoutUses ∧
  MethodShapeValid rawLayouts item.closed method ∧
  UnsafeCallsValid rawLayouts item.closed item.reachable method.code ∧
  DivisionIntrinsicsValid item.closed item.reachable method ∧
  OpaqueLocalsValid item.closed method ∧
  VectorInitializationsValid item.closed item.reachable method ∧
  ScalarFlowValid item.closed item.featureStates item.scalarStates method.code ∧
  ConstrainedCallsValid item.dispatchTypes (specializationTable all) item.closed item.reachable method

instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (imports : List ImportSlot) (item : MethodEvidence)
    (method : Method) :
    Decidable (MethodEvidenceValid rawLayouts layouts all imports item method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- `MethodEvidenceValid` for a program lookup; a missing method fails. -/
private def MethodAtValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (imports : List ImportSlot) (item : MethodEvidence)
    (method : Option Method) : Prop :=
  match method with
  | none => False
  | some value => MethodEvidenceValid rawLayouts layouts all imports item value

private instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (imports : List ImportSlot) (item : MethodEvidence)
    (method : Option Method) :
    Decidable (MethodAtValid rawLayouts layouts all imports item method) := by
  cases method <;> dsimp [MethodAtValid] <;> infer_instance

/-- The architecture layouts are computed for: the first method's profile, or `.scalar` for
    an empty program. -/
abbrev programArchitecture (program : Program) : Architecture :=
  ((program.head?).map fun method => method.profile.architecture).getD .scalar

/-- The certificate covers the entire emitted program, with no optional method list; calls
    past it must match `imports`. -/
def TranslationValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (evidence : List MethodEvidence) (imports : List ImportSlot) (program : Program) : Prop :=
  LayoutsValid rawLayouts layouts (programArchitecture program) ∧
    evidence.length = program.length ∧
  (∀ index : Fin evidence.length,
    MethodAtValid rawLayouts layouts evidence imports evidence[index] program[index.val]?) ∧
  StaticValuesValid program ∧
  ImportedLayoutsValid imports (programArchitecture program)

instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (evidence : List MethodEvidence) (imports : List ImportSlot) (program : Program) :
    Decidable (TranslationValid rawLayouts layouts evidence imports program) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Compose independently checked methods without reducing their validators again. -/
inductive MethodsChecked (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (imports : List ImportSlot) :
    List MethodEvidence → Program → Prop where
  | nil : MethodsChecked rawLayouts layouts all imports [] []
  | cons {item rest method program} :
      MethodEvidenceValid rawLayouts layouts all imports item method →
      MethodsChecked rawLayouts layouts all imports rest program →
      MethodsChecked rawLayouts layouts all imports (item :: rest) (method :: program)

/-- Assembles `TranslationValid` from the program-wide checks and per-method proofs. -/
theorem translation_of_methods {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {evidence : List MethodEvidence} {imports : List ImportSlot} {program : Program}
    (layout : LayoutsValid rawLayouts layouts (programArchitecture program))
    (statics : StaticValuesValid program)
    (importLayouts : ImportedLayoutsValid imports (programArchitecture program))
    (methods : MethodsChecked rawLayouts layouts evidence imports evidence program) :
    TranslationValid rawLayouts layouts evidence imports program := by
  have compose {items code}
      (checked : MethodsChecked rawLayouts layouts evidence imports items code) :
      items.length = code.length ∧ ∀ index : Fin items.length,
        MethodAtValid rawLayouts layouts evidence imports items[index] code[index.val]? := by
    induction checked with
    | nil => exact ⟨rfl, fun index => Fin.elim0 index⟩
    | @cons item rest method code valid tail ih =>
      refine ⟨congrArg Nat.succ ih.1, ?_⟩
      intro ⟨index, bound⟩
      cases index with
      | zero => exact valid
      | succ index => exact ih.2 ⟨index, Nat.lt_of_succ_lt_succ bound⟩
  exact ⟨layout, (compose methods).1, (compose methods).2, statics, importLayouts⟩

/-- Each method of a valid translation passes every per-method validator. -/
theorem translation_method_checked {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {evidence : List MethodEvidence} {imports : List ImportSlot} {program : Program}
    (valid : TranslationValid rawLayouts layouts evidence imports program)
    (index : Fin evidence.length) (method : Method) (found : program[index.val]? = some method) :
    MethodEvidenceValid rawLayouts layouts evidence imports evidence[index] method := by
  have checked := valid.2.2.1 index
  simpa [MethodAtValid, found] using checked

#print axioms translation_method_checked
#print axioms translation_of_methods
end CIL.Extraction
