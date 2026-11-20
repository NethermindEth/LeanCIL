import CIL.InstructionEquations
import CIL.Extraction.DecodedDefinition

/-!
# Instruction equations for decoded profile templates

A shared template takes its instructions from closed decoded methods. A flag selects an
instruction at each pc so the template has a fixed length even when the flags are variables.
-/

namespace CIL.Extraction
open Lean Meta Elab

/-- The instructions of a choice of decoded bodies. Equal branches share their instruction. -/
private partial def templateInstructions (choice : Expr) : MetaM (Array Expr) := do
  let (fn, args) := choice.getAppFnArgs
  if fn == ``ite then
    let #[_, condition, decision, enabled, disabled] := args
      | throwError "expected a complete conditional in a template"
    let yes ← templateInstructions enabled
    let no ← templateInstructions disabled
    unless yes.size == no.size do throwError "template alternatives have different lengths"
    let type := mkConst ``CIL.Instruction
    return ← yes.zipWithM (fun left right => do
      if ← isDefEq left right then return left
      return mkApp5 (mkConst ``ite [.succ .zero]) type condition decision left right) no
  let (code, complete) ← InstructionEquations.listElements choice
  unless complete do throwError "a template alternative must have a closed instruction list"
  return code

/-- A fixed-length list with each position selected from the decoded alternatives. -/
elab "cil_template_code% " choice:term : term => do
  let type := mkConst ``CIL.Instruction
  let term ← Term.elabTermEnsuringType choice (mkApp (mkConst ``List [.zero]) type)
  Term.synthesizeSyntheticMVarsNoPostponing
  let instructions ← templateInstructions (← instantiateMVars term)
  let empty := mkApp (mkConst ``List.nil [.zero]) type
  return InstructionEquations.listLiteral type instructions empty

end CIL.Extraction
