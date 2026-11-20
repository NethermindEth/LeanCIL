import CIL.InstructionEquations
import CIL.Extraction.DecodedDefinition
import CIL.Safety.Linking

/-!
# Code selection for decoded profile templates

A shared template takes its instructions from closed decoded methods. A flag selects an
instruction at each pc so the template has a fixed length even when the flags are variables.
-/

namespace CIL.Extraction
open Lean Meta Elab

/-- Give every method index in a template link table its caller's numbering, including the
    definition named by `ldftn`. Taking its address enters no callee during execution. -/
def _root_.CIL.Method.reindexLinks (body : Method) (index : Nat → Nat) : Method :=
  { body with links := body.links.map fun (pc, link) => (pc, match link with
    | .address target => .address (index target)
    | other => other.relocate index) }

/-- An unselected flag combination keeps the raw opcode at every position. -/
def templateHoles (sites : List RawInstruction) : List Instruction :=
  sites.map fun site => .unadmitted site.opcode

/-- Each conditional instruction compiles independently of the choices at later pcs. -/
@[noinline] private def templateCons (head : Unit → Instruction) (tail : List Instruction) :
    List Instruction := head () :: tail

/-- The instructions of a choice and whether it contains any selected input. -/
private partial def templateInstructions (choice : Expr) : MetaM (Array Expr × Bool) := do
  let (fn, args) := choice.getAppFnArgs
  if fn == ``ite then
    let #[_, condition, decision, enabled, disabled] := args
      | throwError "expected a complete conditional in a template"
    let (yes, selectedYes) ← templateInstructions enabled
    let (no, selectedNo) ← templateInstructions disabled
    unless yes.size == no.size do throwError "template alternatives have different lengths"
    let type := mkConst ``CIL.Instruction
    let instructions ← yes.zipWithM (fun left right => do
      if ← isDefEq left right then return if selectedYes then left else right
      return mkApp5 (mkConst ``ite [.succ .zero]) type condition decision left right) no
    return (instructions, selectedYes || selectedNo)
  let holes := fn == ``templateHoles
  let list := if holes then choice.appArg! else choice
  let (elements, complete) ← InstructionEquations.listElements list
  unless complete do throwError "a template alternative must have a closed instruction list"
  unless holes do return (elements, true)
  let instructions ← elements.mapM fun site => do
    let opcode ← DecodedDefinition.natValue (mkApp (mkConst ``RawInstruction.opcode) site)
    return mkApp (mkConst ``Instruction.unadmitted) (mkNatLit opcode)
  return (instructions, false)

/-- A fixed-length list with each position selected from the decoded alternatives. -/
elab "cil_template_code% " choice:term : term => do
  let type := mkConst ``CIL.Instruction
  let term ← Term.elabTermEnsuringType choice (mkApp (mkConst ``List [.zero]) type)
  Term.synthesizeSyntheticMVarsNoPostponing
  let term ← instantiateMVars term
  let (instructions, selected) ← templateInstructions term
  if selected && !term.isAppOf ``ite then return term
  let empty := mkApp (mkConst ``List.nil [.zero]) type
  let cons := mkApp (mkConst ``List.cons [.zero]) type
  return instructions.foldr (init := empty) fun instruction tail =>
    if instruction.isAppOf ``ite then
      mkApp2 (mkConst ``templateCons) (mkLambda `unit .default (mkConst ``Unit) instruction) tail
    else mkApp2 cons instruction tail

end CIL.Extraction
