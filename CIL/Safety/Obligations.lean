import Lean

/-!
# Obligation tags

The tags LeanCIL tactics give the goals they leave for the author, so a proof selects each by
its purpose (`case invariant =>`), the infoview shows it, and a tactic that rejects its goal
names the obligation it was handed. A tag is goal metadata: setting one prints nothing and does
no proof work. The goal a tactic only continues, such as the loop path after
`cil_loop_advance`, keeps the tag it had.
-/

namespace CIL.Safety

open Lean Elab Tactic Meta

/-- The tags of the obligations LeanCIL tactics leave, the first component of every such tag:
    the loop head's `invariant` and the `measure`'s decrease at a back edge, a callee's
    `precondition` (refined by the callee, as `precondition.stamp`), the caller memory's
    `wellFormed` and `staticWorld` a call or construction needs, the callee's `raises` equation,
    and the `postcondition` at a return (`postcondition_2` for its second conjunct). -/
def obligationTags : List Name :=
  [`invariant, `measure, `precondition, `wellFormed, `staticWorld, `raises, `postcondition]

/-- The obligation `tag` names, as its first component, when it is one of `obligationTags`;
    a numbered conjunct such as `postcondition_2` is the `postcondition`. -/
def obligationOf? (tag : Name) : Option Name :=
  let first := tag.eraseMacroScopes.components.head?.getD .anonymous
  let base := match first with
    | .str .anonymous text => match text.splitOn "_" with
      | [stem, index] => if index.isNat then Name.mkSimple stem else first
      | _ => first
    | _ => first
  if obligationTags.contains base then some base else none

/-- The tag of the precondition of the callee a contract proof's type names: `precondition`
    refined by the callee's constant, such as `precondition.stamp`, or bare when the callee is
    a literal index. -/
def preconditionTag (holdsType : Expr) : Name :=
  match holdsType.consumeMData.getAppArgs.back?.bind (·.consumeMData.constName?) with
  | some callee => match callee.eraseMacroScopes with
    | .str _ last => `precondition ++ Name.mkSimple last
    | _ => `precondition
  | none => `precondition

/-- The `precondition` tag for `holds`, a contract proof elaborated in the main goal's context;
    bare when its type does not elaborate. -/
def preconditionTagOf (holds : Term) : TacticM Name := withMainContext do
  let saved ← saveState
  try
    let proof ← Term.withoutErrToSorry <| withoutRecover <| Term.elabTerm holds none
    let type ← whnfR (← instantiateMVars (← inferType proof))
    saved.restore
    return preconditionTag type
  catch _ =>
    saved.restore
    return `precondition

/-- Give each open goal whose tag is an obligation of `obligationTags` under macro scopes, as a
    hole `?precondition` a tactic's quotation leaves, that plain tag; a precondition takes
    `precondition`, the callee's refined tag. -/
def nameObligations (precondition : Name := `precondition) : TacticM Unit := do
  for goal in ← getGoals do
    let tag ← goal.getTag
    unless tag.hasMacroScopes do continue
    let plain := tag.eraseMacroScopes
    unless obligationTags.contains plain do continue
    goal.setTag (if plain == `precondition then precondition else plain)

/-- Name the obligation holes the preceding tactic left in a quotation by their purpose, the
    precondition refined by the callee of the optional contract proof (see `nameObligations`). -/
syntax "cil_name_obligations" (ppSpace term:max)? : tactic

elab_rules : tactic
  | `(tactic| cil_name_obligations $[$holds]?) => do
    let precondition ← match holds with
      | some holds => preconditionTagOf holds
      | none => pure `precondition
    nameObligations precondition

/-- Tag `goals`, the conjuncts of one obligation in order, `base` when there is one and
    `base_1`, `base_2`, ... when there are several. -/
def tagNumbered (base : Name) (goals : Array MVarId) : MetaM Unit := do
  if let #[goal] := goals then goal.setTag base; return
  for (goal, index) in goals.zipIdx do
    goal.setTag (base.appendIndexAfter (index + 1))

/-- Run `tactic` on the main goal, giving each goal it leaves that is not tagged as an obligation
    the main goal's tag: the goal a tactic continues keeps its name. -/
def keepingTag {α : Type} (tactic : TacticM α) : TacticM α := do
  let tag ← (← getMainGoal).getTag
  let siblings := (← getGoals).tail
  let result ← tactic
  for goal in ← getGoals do
    if siblings.contains goal then continue
    if (obligationOf? (← goal.getTag)).isSome then continue
    goal.setTag tag
  return result

/-- A note for a tactic that rejects its main goal, naming the obligation that goal's tag says
    it is, with the way forward; empty for a goal of no obligation. -/
def obligationNote : TacticM MessageData := do
  let goals ← getGoals
  let some goal := goals.head? | return m!""
  let tag ← goal.getTag
  let some _ := obligationOf? tag | return m!""
  return m!"\nThe main goal is the `{tag.eraseMacroScopes}` obligation; close it first, as \
    `case {tag.eraseMacroScopes} => ...`."

end CIL.Safety
