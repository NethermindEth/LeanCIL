import CIL.Extraction.Generics
import CIL.Extraction.FlowIndex
import CIL.Extraction.Folds
import Std.Data.TreeSet.Lemmas

/-! Indexed local eligibility for feature facts, equivalent to scanning raw metadata. -/

namespace CIL.Extraction

/-- The local whose address an instruction takes, including both `ldloca` encodings. -/
private def addressedLocal (instruction : RawInstruction) : Option Nat :=
  if instruction.opcode == 18 || instruction.opcode == 65037 then localIndex instruction
  else none

/-- Word locals admit every fact; boolean locals admit only zero or one. -/
inductive FeatureLocalKind where
  | unknown
  | word
  | boolean

/-- Classify the exact runtime identity, rejecting every unsupported or malformed type. -/
def FeatureLocalKind.ofType : TypeExpr → FeatureLocalKind
  | .atom scope name =>
    if scope != runtimeScope then .unknown
    else if name == "System.Int32" || name == "System.UInt32" then .word
    else if name == "System.Boolean" then .boolean else .unknown
  | _ => .unknown

/-- A known fact must respect the local's admitted runtime representation. -/
def FeatureLocalKind.accepts (kind : FeatureLocalKind) (fact : Option W32) : Bool :=
  match kind with
  | .unknown => false
  | .word => true
  | .boolean => fact == some 0 || fact == some 1

/-- The original local rule, independent of any precomputed index. -/
def featureLocalEligible (raw : RawMethod) (index : Nat) (fact : Option W32) : Bool :=
  if fact.isNone then true
  else if raw.code.any (fun instruction =>
    (instruction.opcode == 18 || instruction.opcode == 65037) &&
      localIndex instruction == some index) then false
  else match raw.locals[index]? with
    | some (.atom scope name) => scope == runtimeScope &&
        (name == "System.Int32" || name == "System.UInt32" ||
          name == "System.Boolean" && (fact == some 0 || fact == some 1))
    | _ => false

/-- Address exclusions and exact type classifications shared by every certificate state. -/
structure FeatureLocalIndex where
  addressed : Std.TreeSet Nat
  kinds : FlowIndex FeatureLocalKind

/-- Classify each raw local once and collect addressed slots in one instruction traversal. -/
def FeatureLocalIndex.ofRaw (raw : RawMethod) : FeatureLocalIndex :=
  ⟨Std.TreeSet.ofList (raw.code.filterMap addressedLocal),
    FlowIndex.ofList (raw.locals.map FeatureLocalKind.ofType)⟩

/-- Unknown facts remain admissible, including missing or addressed locals. -/
def FeatureLocalIndex.eligible (locals : FeatureLocalIndex) (index : Nat)
    (fact : Option W32) : Bool :=
  if fact.isNone then true else if locals.addressed.contains index then false
  else ((locals.kinds.get? index).getD .unknown).accepts fact

/-- Collecting addressed slots preserves the raw opcode and local-index checks exactly. -/
private theorem addressedLocal_contains (code : List RawInstruction) (index : Nat) :
    (code.filterMap addressedLocal).contains index = code.any (fun instruction =>
      (instruction.opcode == 18 || instruction.opcode == 65037) &&
        localIndex instruction == some index) := by
  apply Bool.eq_iff_iff.mpr
  simp [List.mem_filterMap, addressedLocal, List.any_eq_true]

#print axioms addressedLocal_contains

/-- Indexed lookup preserves the original rule for every index, type, address and fact. -/
theorem FeatureLocalIndex.eligible_eq (raw : RawMethod) (index : Nat) (fact : Option W32) :
    (FeatureLocalIndex.ofRaw raw).eligible index fact = featureLocalEligible raw index fact := by
  simp only [FeatureLocalIndex.eligible, FeatureLocalIndex.ofRaw,
    Std.TreeSet.contains_ofList, addressedLocal_contains, FlowIndex.get?_ofList,
    List.getElem?_map, featureLocalEligible]
  split <;> rename_i unknown
  · rfl
  split <;> rename_i addressed
  · rfl
  cases found : raw.locals[index]? with
  | none => rfl
  | some type =>
    cases type <;> try rfl
    rename_i scope name
    by_cases scopeValid : scope = runtimeScope
    · by_cases word : name = "System.Int32" ∨ name = "System.UInt32"
      · rcases word with word | word <;>
          simp [FeatureLocalKind.ofType, FeatureLocalKind.accepts, scopeValid, word]
      · simp only [not_or] at word
        by_cases boolean : name = "System.Boolean" <;>
          simp [FeatureLocalKind.ofType, FeatureLocalKind.accepts, scopeValid, word, boolean]
    · simp [FeatureLocalKind.ofType, FeatureLocalKind.accepts, scopeValid]

#print axioms FeatureLocalIndex.eligible_eq

end CIL.Extraction
