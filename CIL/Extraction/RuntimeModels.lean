import CIL.Extraction.ModelTable
import CIL.Extraction.ObjectConstruction
import CIL.Extraction.WideArithmetic
import CIL.Extraction.VectorModels
import CIL.Extraction.HardwareModels
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
import CIL.Extraction.AsSpanModels
import CIL.Extraction.StaticSpanModel
import CIL.Extraction.SpanBulkModels
import CIL.Extraction.SpanConstructorModels

/-!
# Runtime model resolution

`runtimeModel` resolves calls and constructors by opcode and method. A modelled site keeps
its operand and has no link. The checked interpreter runs the model for that operand.
An unlinked method-token call that no model claims is refused.
-/

namespace CIL.Extraction

/-- The families registered in the runtime model table. -/
def modelFamilies : List (List ModelEntry) := [
  [objectConstructorEntry],
  vectorEntries,
  vectorHelperEntries,
  hardwareEntries,
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
  asSpanEntries,
  [staticSpanEntry],
  spanBulkEntries,
  spanConstructorEntries,
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

/-- Every hardware slot, exact or not, selects its own entry of the runtime table. -/
theorem runtimeModels_hardwareRegistered : HardwareRegistered runtimeModels := by
  hardware_registrations

#print axioms runtimeModels_hardwareRegistered

/-- Every hardware reference, DivRem among them, resolves through the rows of its own slot. -/
theorem runtimeModels_hardware (environment : LayoutEnvironment) (method : MethodRef)
    (member : hardwareCallFamily method = true) :
    runtimeModel environment .call method = hardwareModel environment method :=
  runtimeModels_hardwareRegistered.resolve environment method member

#print axioms runtimeModels_hardware

/-- Every exact hardware reference selects the operation of its own closed signature. -/
theorem runtimeModels_exactHardware (environment : LayoutEnvironment) (method : MethodRef)
    (member : exactCallFamily method = true) :
    runtimeModel environment .call method = exactIntrinsic method :=
  runtimeModels_hardwareRegistered.resolveExact environment method member

#print axioms runtimeModels_exactHardware

/-- The mechanism responsible for a method-token call site. -/
inductive SiteClaim where
  | link
  | model
  | refused
  deriving DecidableEq, Repr

/-- A link claims its pc first, followed by a model family or resolving overload. -/
def siteClaim (environment : LayoutEnvironment) (link : Option Link) (raw : RawInstruction)
    (claims : LayoutEnvironment → CallOpcode → MethodRef → Bool := runtimeModels.claims) :
    SiteClaim :=
  if !methodTokenCall raw.opcode then .refused else
  match raw.operand with
  | .call site =>
    if link.isSome then .link
    else if (callOpcode? raw.opcode).any (fun op => claims environment op site.method) then .model
    else .refused
  | _ => .refused

/-- A modelled opcode and method use the body's runtime environment and require no link. -/
def callModelled (body : Method) (site : CallOpcode × MethodRef) : Bool :=
  (runtimeModel body.environment site.1 site.2).isSome

open Lean Meta Elab Tactic in
/-- Each literal table entry occurs at its recorded index in the registered list. -/
private def proveEntryMembership : TacticM Unit := do
  let cells ← literalCells (mkConst ``modelEntries)
  let key (entry : Expr) := unsafe evalExpr Nat (mkConst ``Nat)
    (mkApp (mkConst ``ModelEntry.key) entry)
  let mut positions : Std.HashMap Expr Nat := {}
  let mut byName : Std.HashMap Nat (List Nat) := {}
  for index in [:cells.size] do
    positions := positions.insert cells[index]!.consumeMData index
    let name ← key cells[index]!
    byName := byName.insert name (index :: byName.getD name [])
  for goal in ← getGoals do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isApp do throwError "expected entry membership: {target}"
    let entry := target.appArg!.consumeMData
    let found ← match positions.get? entry with
      | some index => pure (some index)
      | none => (byName.getD (← key entry) []).findM? (fun i => isDefEq cells[i]! entry)
    let some index := found | throwError "unregistered model entry: {entry}"
    let type := mkConst ``ModelEntry
    let value := mkApp2 (mkConst ``Option.some [0]) type entry
    goal.assign (mkApp5 (mkConst ``List.mem_of_getElem? [0]) type (mkConst ``modelEntries)
      (mkNatLit index) entry (← mkEqRefl value))
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
