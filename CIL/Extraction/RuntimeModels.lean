import CIL.Extraction.ModelTable
import CIL.Extraction.ObjectConstruction
import CIL.Extraction.IntegerMath
import CIL.Extraction.VectorModels
import CIL.Extraction.MarshalModels
import CIL.Extraction.BitModels
import CIL.Extraction.UnsafeReinterpretations
import CIL.Extraction.UnsafeOffsets

/-!
# Runtime model resolution

`runtimeModel` resolves a call through the table of every modelled runtime method. A call of a
modelled method keeps its call and states no link (`callModelled`, which `ManagedCallsValid`
reads), and the checked interpreter runs the model its operand names. At an unlinked
method-token call, the raw selector gives a resolving model priority over a lowered family.
-/

namespace CIL.Extraction

/-- The runtime methods with a model. -/
def modelEntries : List ModelEntry :=
  objectConstructorEntry :: vectorEntries ++ integerMathEntries ++ bitEntries ++ unsafeEntries ++
    marshalEntries ++ unsafeReinterpretEntries ++ unsafeOffsetEntries

/-- The table of `modelEntries`. -/
def runtimeModels : ModelTable := model_table% modelEntries

/-- The runtime model a call under `opcode` to `method` stands for, if any. -/
def runtimeModel (environment : LayoutEnvironment) (opcode : CallOpcode) (method : MethodRef) :
    Option RuntimeModel :=
  runtimeModels.find environment opcode method

/-- The mechanism responsible for a method-token call site. -/
inductive SiteClaim (Family : Type) where
  | link
  | model
  | lowered (family : Family)
  | refused
  deriving DecidableEq, Repr

/-- A link claims its pc first, followed by a model family or resolving overload, then a
    lowered family named by the raw operand. -/
def siteClaim {Family : Type} (familyOf : RawInstruction → Option Family)
    (environment : LayoutEnvironment) (link : Option Link) (raw : RawInstruction)
    (claims : LayoutEnvironment → CallOpcode → MethodRef → Bool := runtimeModels.claims) :
    SiteClaim Family :=
  if !methodTokenCall raw.opcode then .refused else
  match raw.operand with
  | .call site =>
    if link.isSome then .link
    else if (callOpcode? raw.opcode).any (fun op => claims environment op site.method) then .model
    else (familyOf raw).elim .refused .lowered
  | _ => .refused

/-- Every live direct call, virtual call or construction has a claim. -/
def SiteClaimTotal {Family : Type} (familyOf : RawInstruction → Option Family)
    (environment : LayoutEnvironment) (link : Option Link) (raw : RawInstruction)
    (live : Bool) : Prop :=
  live = true → methodTokenCall raw.opcode = true →
    siteClaim familyOf environment link raw ≠ .refused

/-- Whether a runtime model stands for a `call` of `method` in `body`, which then states no
    link. -/
def callModelled (body : Method) (method : MethodRef) : Bool :=
  (runtimeModel body.environment .call method).isSome

/-- Every entry of the runtime table is one of `modelEntries`. -/
theorem runtimeModels_entries : ∀ group ∈ runtimeModels.toList, ∀ entry ∈ group.2,
    entry ∈ modelEntries := by
  simp [runtimeModels, SearchTree.toList, modelEntries, vectorEntries, integerMathEntries,
    marshalEntries, bitEntries, bitHelpers, bitHelperModel,
    mathOperations, mathIntegers, IntegerMath.signedOnly, unsafeEntries, unsafeReinterpretEntries,
    unsafeOffsetEntries]

#print axioms runtimeModels_entries

/-- A model the runtime table gives has every property the models of each entry of
    `modelEntries` have, so adding an entry adds one case to such a proof. -/
theorem runtimeModel_yields {property : RuntimeModel → Prop}
    (every : ∀ entry ∈ modelEntries, entry.Yields property) {environment : LayoutEnvironment}
    {opcode : CallOpcode} {method : MethodRef} {model : RuntimeModel}
    (found : runtimeModel environment opcode method = some model) : property model :=
  ModelTable.find_yields (fun group listed entry member =>
    every entry (runtimeModels_entries group listed entry member)) found

#print axioms runtimeModel_yields

/-- The catalog used by extracted methods and the checked interpreter. -/
def runtimeCatalog : ModelCatalog := ⟨runtimeModels⟩

end CIL.Extraction
