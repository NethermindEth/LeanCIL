import CIL.Extraction.ModelTable

/-!
# Runtime model resolution

`runtimeModel` resolves a call through the table of every modelled runtime method, and
`RuntimeModelsAgree`, part of `MethodEvidenceValid`, requires each live call site of a method to
emit the model its method reference stands for. A runtime method enters `modelEntries` together
with the emissions its model stands for in `runtimeCatalog`.
-/

namespace CIL.Extraction

/-- The runtime methods with a model. -/
def modelEntries : List ModelEntry := []

/-- The table of `modelEntries`. -/
def runtimeModels : ModelTable := model_table% modelEntries

/-- The runtime model a call under `opcode` to `method` stands for, if any. -/
def runtimeModel (environment : LayoutEnvironment) (opcode : CallOpcode) (method : MethodRef) :
    Option RuntimeModel :=
  runtimeModels.find environment opcode method

/-- The runtime models with the emissions they account for. -/
def runtimeCatalog : ModelCatalog where
  table := runtimeModels
  lowered _ := none

/-- Each live call site of a method emits the runtime model its method reference stands for. -/
def RuntimeModelsAgree (closed : RawMethod) (reachable : List Bool) (method : Method) : Prop :=
  ModelsAgree runtimeCatalog method.environment closed reachable method.code

instance (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (RuntimeModelsAgree closed reachable method) :=
  inferInstanceAs (Decidable (ModelsAgree _ _ _ _ _))

end CIL.Extraction
