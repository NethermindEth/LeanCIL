import CIL.Extraction.Features
import CIL.Extraction.LayoutCoverage

namespace CIL.Extraction

/-- Every extracted method has exactly one record, in emitted program order. -/
structure MethodEvidence where
  original : RawMethod
  arguments : List TypeExpr
  closed : RawMethod
  parameterInput : RawArguments
  reachable : List Bool
  featureStates : FeatureCertificate
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
    (all : List MethodEvidence) (item : MethodEvidence) (method : Method) : Prop :=
  SpecializationValid rawLayouts item.original item.arguments item.closed item.parameterInput ∧
  ParameterHomesValid layouts item.parameterInput item.reachable method ∧
  MethodLayoutsValid rawLayouts layouts method item.layoutUses ∧
  FeatureFlowValid item.closed method.profile item.featureStates item.reachable method.code ∧
  ManagedCallsValid (specializationTable all) item.closed item.reachable method ∧
  LayoutUsesComplete rawLayouts item.closed item.parameterInput item.reachable item.layoutUses ∧
  MethodShapeValid rawLayouts item.closed method

instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (item : MethodEvidence) (method : Method) :
    Decidable (MethodEvidenceValid rawLayouts layouts all item method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private def MethodAtValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (item : MethodEvidence) (method : Option Method) : Prop :=
  match method with
  | none => False
  | some value => MethodEvidenceValid rawLayouts layouts all item value

private instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (all : List MethodEvidence) (item : MethodEvidence) (method : Option Method) :
    Decidable (MethodAtValid rawLayouts layouts all item method) := by
  cases method <;> dsimp [MethodAtValid] <;> infer_instance
/-- The certificate covers the entire emitted program, with no optional method list. -/
def TranslationValid (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (evidence : List MethodEvidence) (program : Program) : Prop :=
  LayoutsValid rawLayouts layouts ∧ evidence.length = program.length ∧
  ∀ index : Fin evidence.length, MethodAtValid rawLayouts layouts evidence evidence[index] program[index.val]?

instance (rawLayouts : List RawLayout) (layouts : Array ComputedLayout)
    (evidence : List MethodEvidence) (program : Program) :
    Decidable (TranslationValid rawLayouts layouts evidence program) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem translation_method_checked {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {evidence : List MethodEvidence} {program : Program}
    (valid : TranslationValid rawLayouts layouts evidence program)
    (index : Fin evidence.length) (method : Method) (found : program[index.val]? = some method) :
    MethodEvidenceValid rawLayouts layouts evidence evidence[index] method := by
  have checked := valid.2.2 index
  simpa [MethodAtValid, found] using checked

#print axioms translation_method_checked
end CIL.Extraction
