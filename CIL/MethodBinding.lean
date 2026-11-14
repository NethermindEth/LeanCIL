import Lean
import CIL.Instructions
import CIL.DebugNames
import CIL.TermAccess

/-!
# Method-body bindings

`cil_body` proves a method-body binding such as
`Extracted.program[2]? = some (Full.body Extracted.profile 9 5 7)` by `rfl`.
When `rfl` fails it evaluates both closed sides and reports the first difference
in each `Method` field. The diagnostic is computed only after `rfl` has failed and
never closes the goal.
-/

namespace CIL.MethodBinding

open Lean Meta Elab Tactic

-- Diagnostic comparison only; proofs never depend on these instances.
deriving instance BEq for MemoryOp
deriving instance BEq for Instruction

/-- The first index where two lists differ, with the element of each side there. -/
def firstDifference [BEq T] :
    List T -> List T -> Nat -> Option (Prod Nat (Prod (Option T) (Option T)))
  | [], [], _ => none
  | a :: as, b :: bs, index =>
    if a == b then firstDifference as bs (index + 1) else some (index, some a, some b)
  | a :: _, [], index => some (index, some a, none)
  | [], b :: _, index => some (index, none, some b)

/-- An element for a diagnostic, or a marker when one list has ended. -/
private def element [Repr T] : Option T -> String
  | some value => reprStr value
  | none => "(past the end)"

/-- The first difference in one list field, or `none` when both sides agree. -/
def listField [BEq T] [Repr T] (field : String) (left right : List T) : Option String :=
  (firstDifference left right 0).map fun (index, l, r) =>
    s!"field {field}: first difference at index {index} \
      (left length {left.length}, right length {right.length})\n" ++
    s!"  left:  {element l}\n  right: {element r}"

/-- The first difference in one scalar field, or `none` when both sides agree. -/
def valueField [BEq T] [Repr T] (field : String) (left right : T) : Option String :=
  if left == right then none
  else some s!"field {field}:\n  left:  {reprStr left}\n  right: {reprStr right}"

/-- The environment difference, without printing the layout tables. -/
def environmentField (left right : LayoutEnvironment) : Option String :=
  if left == right then none
  else some (s!"field environment: the layout tables differ\n" ++
    s!"  left:  {left.rawLayouts.length} raw layouts, {left.layouts.size} computed\n" ++
    s!"  right: {right.rawLayouts.length} raw layouts, {right.layouts.size} computed")

/-- What to do when a body's link table differs: a structure update copies the old table. -/
def linksHint : String :=
  "\n  a body written as `{ method with code := ... }` keeps the links of `method`, keyed by its \
    own pcs; build it with `Method.withCode` so its links follow its code"

/-- What to do when a body's static sites differ: `Method.withCode` resets them. -/
def staticSitesHint : String :=
  "\n  static sites are keyed by pc; `Method.withCode` resets them, so a body that reads statics \
    supplies its own after it: `{ body with staticSites := [(pc, descriptor), ...] }`, one entry \
    per static access at the body's pc, with the descriptor the extraction has for that access"

/-- One line per differing `Method` field, in declaration order. -/
def methodDifferences (left right : Method) : List String :=
  [ valueField "profile" left.profile right.profile,
    listField "code" left.code right.code,
    listField "locals" left.locals right.locals,
    listField "localKinds" left.localKinds right.localKinds,
    (listField "staticSites" left.staticSites right.staticSites).map (· ++ staticSitesHint),
    listField "parameterHomes" left.parameterHomes right.parameterHomes,
    valueField "declared" left.declared right.declared,
    environmentField left.environment right.environment,
    (listField "links" left.links right.links).map (· ++ linksHint),
    valueField "returnsValue" left.returnsValue right.returnsValue ].filterMap id

/-- The type `CIL.Method` as an expression, for evaluating a side. -/
private def methodType : Expr := mkConst ``CIL.Method
/-- The type `Option CIL.Method` as an expression, for evaluating a side. -/
private def optionMethodType : Expr := mkApp (mkConst ``Option [Level.zero]) methodType

/-- The implementation of `describe`, which must evaluate both sides. -/
private unsafe def describeUnsafe (goal : Expr) : MetaM MessageData := do
  let evaluate (T : Type) (type value : Expr) : MetaM T := evalExpr T type value
  let some (type, lhs, rhs) := goal.eq? | return m!"the goal is not an equality"
  let lhs <- instantiateMVars lhs
  let rhs <- instantiateMVars rhs
  if lhs.hasFVar || lhs.hasMVar || rhs.hasFVar || rhs.hasMVar then
    return m!"both sides must be closed terms to be compared"
  -- `program[i]?` elaborates to `getElem? program i`; name the method index when present.
  let (header, program) <- do
    match argumentsOf? lhs ``GetElem?.getElem? 7 with
    | some #[_, _, _, _, _, methods, position] =>
      let index : Nat <- evaluate Nat (mkConst ``Nat) position
      pure (m!"method index {index}\n", some (methods, index))
    | _ => pure (m!"", none)
  let pair <- if <- isDefEq type optionMethodType then
      pure (<- evaluate (Option Method) optionMethodType lhs,
        <- evaluate (Option Method) optionMethodType rhs)
    else if <- isDefEq type methodType then
      pure (some (<- evaluate Method methodType lhs), some (<- evaluate Method methodType rhs))
    else return m!"the equality is not between methods: {type}"
  match pair with
  | (some left, some right) =>
    match methodDifferences left right with
    | [] =>
      return header ++ m!"both sides evaluate to the same method; rfl failed for another reason"
    | lines =>
      let source <- match program, firstDifference left.code right.code 0 with
        | some (_, index), some (pc, _) => CIL.DebugNames.sourceLine index pc
        | _, _ => pure ""
      return header ++ m!"{"\n".intercalate lines}{source}"
  | (none, none) => return header ++ m!"both sides evaluate to none"
  | (none, some _) =>
    let count <- match program with
      | some (list, _) =>
        let methods <- evaluate (List Method) (mkApp (mkConst ``List [Level.zero]) methodType) list
        pure m!" (the program has {methods.length} methods)"
      | none => pure m!""
    return header ++ m!"left side is none{count}, right side is some method"
  | (some _, none) => return header ++ m!"left side is some method, right side is none"

/-- Describes how the two closed sides of a `Method` or `Option Method` equality differ. -/
@[implemented_by describeUnsafe]
opaque describe (goal : Expr) : MetaM MessageData

/-- Proves a method-body binding by `rfl`; on failure reports the first difference
    between the evaluated sides. Only `rfl` closes the goal. -/
syntax (name := cilBody) "cil_body" : tactic

/-- Runs `rfl`; on failure restores the state and throws the evaluated difference. -/
@[tactic cilBody] def evalCilBody : Tactic := fun _ => do
  let goal <- getMainGoal
  let state <- saveState
  try
    evalTactic (<- `(tactic| rfl))
  catch failure =>
    state.restore
    let report <- try describe (<- instantiateMVars (<- goal.getType))
      catch error => pure m!"could not evaluate both sides: {error.toMessageData}"
    throwError m!"cil_body: rfl could not prove the method-body binding\n{report}\n\n\
      rfl reported: {failure.toMessageData}"

end CIL.MethodBinding
