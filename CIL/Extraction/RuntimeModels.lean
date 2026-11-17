import CIL.Extraction.ModelTable
import CIL.Extraction.ObjectConstruction
import CIL.Extraction.IntegerMath
import CIL.Extraction.VectorModels

/-!
# Runtime model resolution

`runtimeModel` resolves a call through the table of every modelled runtime method. A call of a
modelled method keeps its call and states no link (`callModelled`, which `ManagedCallsValid`
reads), and the checked interpreter runs the model its operand names. `RuntimeModelsAgree`,
part of `MethodEvidenceValid`, requires every other emission at a live call site to be the model
its method reference stands for. A runtime method enters `modelEntries` together with the
emissions its model stands for in `runtimeCatalog`.
-/

namespace CIL.Extraction

/-- The runtime methods with a model. -/
def modelEntries : List ModelEntry :=
  objectConstructorEntry :: vectorEntries ++ integerMathEntries

/-- The table of `modelEntries`. -/
def runtimeModels : ModelTable := model_table% modelEntries

/-- The runtime model a call under `opcode` to `method` stands for, if any. -/
def runtimeModel (environment : LayoutEnvironment) (opcode : CallOpcode) (method : MethodRef) :
    Option RuntimeModel :=
  runtimeModels.find environment opcode method

/-- Whether a runtime model stands for a `call` of `method` in `body`, which then states no
    link. -/
def callModelled (body : Method) (method : MethodRef) : Bool :=
  (runtimeModel body.environment .call method).isSome

/-- Every entry of the runtime table is one of `modelEntries`. -/
theorem runtimeModels_entries : ∀ group ∈ runtimeModels.toList, ∀ entry ∈ group.2,
    entry ∈ modelEntries := by
  simp [runtimeModels, SearchTree.toList, modelEntries, vectorEntries, integerMathEntries,
    mathOperations, mathIntegers, IntegerMath.signedOnly]

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

/-- The runtime models with the emissions they account for: none, since a call of a modelled
    method keeps its call. -/
def runtimeCatalog : ModelCatalog where
  table := runtimeModels
  lowered _ := none

/-- Each live call site of a method keeps its call or emits the runtime model its method
    reference stands for. -/
def RuntimeModelsAgree (closed : RawMethod) (reachable : List Bool) (method : Method) : Prop :=
  ModelsAgree runtimeCatalog method.environment method.profile closed reachable method.code

instance (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (RuntimeModelsAgree closed reachable method) :=
  inferInstanceAs (Decidable (ModelsAgree _ _ _ _ _ _))

end CIL.Extraction
