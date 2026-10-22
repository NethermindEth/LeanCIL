import CIL.MethodIdentity
import CIL.Embedding.Basic

/-!
Structural labels inside a method body. A loop head is the target of a branch at the
same or a later pc; a call site is a `.call` to a bound method. Both are read from the
body, so an edit elsewhere in the method moves the label with the code. A label that
matches several sites is an error listing them until `[k]` selects one. Each label is a
plain `Nat` pinned by a kernel-checked theorem; it locates and proves nothing more.
-/

namespace CIL.StructuralLabels

open Lean Meta Elab Term Command
open CIL.MethodIdentity
open CIL.DebugNames (visible)

/-- The literals of a closed `List Nat`, reduced one cell at a time. -/
partial def nats (list : Expr) (found : Array Nat := #[]) : MetaM (Array Nat) := do
  match (← whnf list).getAppFnArgs with
  | (``List.cons, #[_, head, tail]) =>
    let some value ← (evalNat (← whnf head)).run | throwError "code target is not a literal: {head}"
    nats tail (found.push value)
  | (``List.nil, _) => return found
  | _ => throwError "code targets are not a list literal"

/-- Each loop as `(head, latch)` in head order: `latch` is the last pc branching back to `head`. -/
def loops (method : Expr) : MetaM (Array (Nat × Nat)) := do
  let mut cell := mkApp (mkConst ``CIL.Method.code) method
  let mut pc := 0
  let mut latches : Std.HashMap Nat Nat := {}
  repeat
    match (← whnf cell).getAppFnArgs with
    | (``List.cons, #[_, op, tail]) =>
      for target in ← nats (mkApp (mkConst ``CIL.Op.targets) op) do
        if target ≤ pc then latches := latches.insert target pc
      cell := tail
      pc := pc + 1
    | _ => break
  return latches.toArray.qsort (·.1 < ·.1)

/-- `bind_loop head := body` names the only loop head of `body`, and `[k]` the `k`-th in pc
order. `head.latch` is the last back edge into it; `head.backEdge` checks both. -/
syntax (name := bindLoop) "bind_loop " ident " := " term:max (" [" num "]")? : command

elab_rules : command
  | `(bind_loop $head := $body $[[$occurrence]]?) => do
    let (pc, latch) ← liftTermElabM do
      let found ← loops (← instantiateMVars (← elabTermEnsuringType body (some (mkConst ``CIL.Method))))
      if found.isEmpty then throwError "{body} has no loops: no branch targets the same or an earlier pc"
      let chosen ← choose m!"{body} has {found.size} loops"
        (found.map fun (pc, latch) => s!"head pc {pc}, back edge from pc {latch}") (occurrence.map (·.getNat))
      return found[chosen]!
    let latchName := mkIdent (head.getId ++ `latch)
    elabCommand (← `(@[cil_code] def $head : Nat := $(quote pc)))
    elabCommand (← `(@[cil_code] def $latchName : Nat := $(quote latch)))
    elabCommand (← `(theorem $(mkIdent (head.getId ++ `backEdge)) :
      ($body).code[$latchName]?.map (fun op => op.targets.contains $head) = some true ∧ $head ≤ $latchName :=
      ⟨rfl, by decide⟩))

/-- `bind_call site := callee from parent` names the only call from `parent` to the bound
method `callee`, and `[k]` the `k`-th in pc order; `site.call` states its instruction. -/
syntax (name := bindCall) "bind_call " ident " := " term:max " from " term:max (" [" num "]")? : command

elab_rules : command
  | `(bind_call $site := $callee from $parent $[[$occurrence]]?) => do
    let (pc, argc) ← liftTermElabM do
      let some method ← (evalNat (← whnf (← elabTermEnsuringType callee (some (mkConst ``Nat))))).run
        | throwError "{callee} is not a closed method index"
      let table ← strings (mkConst (← visible `Extracted.signatures))
      callSite parent method (table[method]?.getD s!"method {method}") (occurrence.map (·.getNat))
    elabCommand (← `(@[cil_code] def $site : Nat := $(quote pc)))
    elabCommand (← `(@[cil_code] theorem $(mkIdent (site.getId ++ `call)) :
      ($parent).code[$site]? = some (CIL.Op.call $callee $(quote argc)) := rfl))

end CIL.StructuralLabels
