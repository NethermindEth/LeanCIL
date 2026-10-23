import CIL.Extraction.Scalars
import CIL.Extraction.LayoutCoverage
import CIL.Extraction.UnsafeCalls
import CIL.Extraction.DivisionIntrinsics
import CIL.Extraction.VectorInitialization
import CIL.Extraction.StaticValues
import CIL.Extraction.ImportLayouts

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

def specializationTable (evidence : List MethodEvidence) : List SpecializedMethod :=
  evidence.map fun item => ⟨item.arguments, item.closed⟩

private def initialLocal : LocalKind → Value
  | .reference => .nullRef
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
/-- Bind non-instruction method fields that affect frame setup and return behavior. -/
def MethodShapeValid (layouts : List RawLayout) (closed : RawMethod) (method : Method) : Prop :=
  method.profile.Valid ∧ method.returnsValue = (closed.returnType != .void) ∧
  method.locals = method.localKinds.map (fun kind =>
    if closed.initLocals then initialLocal kind else .unmodeled) ∧
  method.vectorLocals = [] ∧ method.vectorArgs = [] ∧
  method.code.all (fun op => match op with
    | .ret narrow => narrow == returnNarrow layouts closed.returnType
    | _ => true) = true

instance (layouts : List RawLayout) (closed : RawMethod) (method : Method) : Decidable (MethodShapeValid layouts closed method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
def MethodEvidenceValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (imports : List ImportSlot) (item : MethodEvidence) (method : Method) : Prop :=
  SpecializationValid rawLayouts item.original item.arguments item.closed item.parameterInput ∧
  ParameterHomesValid layouts item.parameterInput item.reachable method ∧
  MethodLayoutsValid rawLayouts layouts method item.layoutUses ∧
  FeatureFlowValid item.closed method.profile item.featureStates item.reachable method.code ∧
  ManagedCallsValid (specializationTable all) imports item.closed item.reachable method ∧
  LayoutUsesComplete rawLayouts item.closed item.parameterInput item.reachable item.layoutUses ∧
  MethodShapeValid rawLayouts item.closed method ∧
  UnsafeCallsValid rawLayouts item.closed item.reachable method.code ∧
  DivisionIntrinsicsValid item.closed item.reachable method ∧
  OpaqueLocalsValid item.closed method ∧
  VectorInitializationsValid item.closed item.reachable method ∧
  ScalarFlowValid item.closed item.featureStates item.scalarStates method.code

instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (imports : List ImportSlot) (item : MethodEvidence) (method : Method) :
    Decidable (MethodEvidenceValid rawLayouts layouts all imports item method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private def MethodAtValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (imports : List ImportSlot) (item : MethodEvidence) (method : Option Method) : Prop :=
  match method with
  | none => False
  | some value => MethodEvidenceValid rawLayouts layouts all imports item value

private instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (imports : List ImportSlot) (item : MethodEvidence) (method : Option Method) :
    Decidable (MethodAtValid rawLayouts layouts all imports item method) := by
  cases method <;> dsimp [MethodAtValid] <;> infer_instance
/-- The certificate covers the entire emitted program, with no optional method list; calls past it must match `imports`. -/
def TranslationValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (evidence : List MethodEvidence) (imports : List ImportSlot) (program : Program) : Prop :=
  LayoutsValid rawLayouts layouts (((program.head?).map fun method => method.profile.architecture).getD .scalar) ∧ evidence.length = program.length ∧
  (∀ index : Fin evidence.length, MethodAtValid rawLayouts layouts evidence imports evidence[index] program[index.val]?) ∧
  StaticValuesValid program ∧
  ImportedLayoutsValid imports (((program.head?).map fun method => method.profile.architecture).getD .scalar)

instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (evidence : List MethodEvidence) (imports : List ImportSlot) (program : Program) :
    Decidable (TranslationValid rawLayouts layouts evidence imports program) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Compose independently checked methods without reducing their validators again. -/
inductive MethodsChecked (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (imports : List ImportSlot) : List MethodEvidence → Program → Prop where
  | nil : MethodsChecked rawLayouts layouts all imports [] []
  | cons {item rest method program} : MethodEvidenceValid rawLayouts layouts all imports item method →
      MethodsChecked rawLayouts layouts all imports rest program →
      MethodsChecked rawLayouts layouts all imports (item :: rest) (method :: program)

theorem translation_of_methods {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {evidence : List MethodEvidence} {imports : List ImportSlot} {program : Program}
    (layout : LayoutsValid rawLayouts layouts (((program.head?).map fun method => method.profile.architecture).getD .scalar))
    (statics : StaticValuesValid program)
    (importLayouts : ImportedLayoutsValid imports (((program.head?).map fun method => method.profile.architecture).getD .scalar))
    (methods : MethodsChecked rawLayouts layouts evidence imports evidence program) :
    TranslationValid rawLayouts layouts evidence imports program := by
  have compose {items code} (checked : MethodsChecked rawLayouts layouts evidence imports items code) :
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
