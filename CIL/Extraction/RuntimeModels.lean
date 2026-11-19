import CIL.Extraction.ModelTable
import CIL.Extraction.ObjectConstruction
import CIL.Extraction.WideArithmetic
import CIL.Extraction.VectorModels
import CIL.Extraction.VectorHelpers
import CIL.Extraction.PlatformModels
import CIL.Extraction.ReferenceContentModels
import CIL.Extraction.GuardModels
import CIL.Extraction.MarshalModels
import CIL.Extraction.BinaryModels
import CIL.Extraction.BitModels
import CIL.Extraction.UnsafeReinterpretations
import CIL.Extraction.UnsafeOffsets
import CIL.Extraction.UnsafeTransferModels
import CIL.Extraction.UnsafeBlocks
import CIL.Extraction.SpanModels

/-!
# Runtime model resolution

`runtimeModel` resolves a call through the table of every modelled runtime method. A call of a
modelled method keeps its call and states no link (`callModelled`, which `ManagedCallsValid`
reads), and the checked interpreter runs the model its operand names. At an unlinked
method-token call, the raw selector gives a resolving model priority over a lowered family.
-/

namespace CIL.Extraction

/-- The families registered in the runtime model table. -/
def modelFamilies : List (List ModelEntry) := [
  [objectConstructorEntry],
  vectorEntries,
  vectorHelperEntries,
  integerMathEntries,
  wideArithmeticEntries,
  binaryEntries,
  bitEntries,
  unsafeEntries,
  platformEntries,
  referenceContentEntries,
  guardEntries,
  marshalEntries,
  unsafeReinterpretEntries,
  unsafeReferenceEntries,
  unsafeOffsetEntries,
  unsafeTransferEntries,
  unsafeBlockEntries,
  spanEntries,
]

/-- The runtime methods with a model. -/
def modelEntries : List ModelEntry :=
  modelFamilies.flatten

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

open Lean Meta Elab Tactic in
/-- Each literal table entry occurs at its recorded index in the registered list. -/
private def proveEntryMembership : TacticM Unit := do
  let cells ← literalCells (mkConst ``modelEntries)
  let key (entry : Expr) := unsafe evalExpr Nat (mkConst ``Nat)
    (mkApp (mkConst ``ModelEntry.key) entry)
  let mut positions : Std.HashMap Nat (List Nat) := {}
  for index in [:cells.size] do
    let name ← key cells[index]!
    positions := positions.insert name (index :: positions.getD name [])
  for goal in ← getGoals do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isApp do throwError "expected entry membership: {target}"
    let entry := target.appArg!.consumeMData
    let candidates := positions.getD (← key entry) []
    let some index ← candidates.findM? (fun i => isDefEq cells[i]! entry)
      | throwError "unregistered model entry: {entry}"
    let value ← mkAppM ``Option.some #[entry]
    let proof ← mkAppOptM ``List.mem_of_getElem? #[none, some (mkConst ``modelEntries),
      some (mkNatLit index), some entry, some (← mkEqRefl value)]
    goal.assign proof
  setGoals []

/-- Every entry of the runtime table is one of `modelEntries`. -/
theorem runtimeModels_entries : ∀ group ∈ runtimeModels.toList, ∀ entry ∈ group.2,
    entry ∈ modelEntries := by
  simp only [runtimeModels, SearchTree.toList, List.forall_mem_append, List.forall_mem_cons,
    List.not_mem_nil, false_implies, implies_true, and_true, true_and]
  repeat' first | apply And.intro | exact True.intro
  run_tac proveEntryMembership

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
