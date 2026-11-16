import CIL.Extraction.ModelTable
import CIL.Extraction.ObjectConstruction

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
def modelEntries : List ModelEntry := [objectConstructorEntry]

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

/-- The runtime table models only the `System.Object` constructor, so proofs about calls that
    run a model cover that one; an entry of another model must extend each of them. -/
theorem runtimeModel_objectConstructor {environment : LayoutEnvironment} {opcode : CallOpcode}
    {method : MethodRef} {model : RuntimeModel}
    (found : runtimeModel environment opcode method = some model) :
    model = .objectConstructor := by
  simp only [runtimeModel, runtimeModels, ModelTable.find, SearchTree.find?] at found
  split at found <;> try cases found
  simp only [objectConstructorEntry, ModelEntry.exact, bind, Option.bind, List.find?] at found
  split at found <;> try cases found
  rename_i selected
  split at selected <;> cases selected
  dsimp only at found
  split at found <;> cases found
  rfl

#print axioms runtimeModel_objectConstructor

/-- No model of the runtime table consults the profile, so `Instruction.ProfileAgreement` says
    nothing of calls; an entry whose model does must extend it. -/
theorem runtimeModel_readsProfile {environment : LayoutEnvironment} {opcode : CallOpcode}
    {method : MethodRef} {model : RuntimeModel}
    (found : runtimeModel environment opcode method = some model) :
    model.readsProfile = false := by
  rw [runtimeModel_objectConstructor found]
  rfl

#print axioms runtimeModel_readsProfile

/-- The runtime models with the emissions they account for: `pop` does what the
    `System.Object` constructor's model does, so it stands for no other call. -/
def runtimeCatalog : ModelCatalog where
  table := runtimeModels
  lowered
    | .pop => some .objectConstructor
    | _ => none

/-- Each live call site of a method keeps its call or emits the runtime model its method
    reference stands for. -/
def RuntimeModelsAgree (closed : RawMethod) (reachable : List Bool) (method : Method) : Prop :=
  ModelsAgree runtimeCatalog method.environment closed reachable method.code

instance (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (RuntimeModelsAgree closed reachable method) :=
  inferInstanceAs (Decidable (ModelsAgree _ _ _ _ _))

end CIL.Extraction
