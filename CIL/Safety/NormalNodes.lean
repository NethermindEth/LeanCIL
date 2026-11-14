import Lean

/-!
# Normal-form record for stepping runs

A stepping run simplifies its goal after every instruction, and the goal holds every value the
run has built so far. Simplifying the whole goal each time makes the cost of a step grow with the
program counter. This module keeps, for each simplification that a step runs, the terms that
simp visited and left unchanged (the entries of its cache whose result is the key) in earlier
steps of the same run, and `cil_simp_only` and `cil_try_simp_only` return such a term without
visiting it again. The literal-operand and local-result passes record the terms below which
their detectors find nothing, which depends on the term alone. The record also keeps the
simplification contexts of the run, which every step would otherwise rebuild, and a
discrimination tree of the equation hypotheses by their left sides, which the lookups of every
step read.

Invariant for a tactic that reads the record: it runs inside `withNormalNodes`, on a goal whose
local context is the one the record was made for (`NormalNodes.usable` checks this), and the
result it records for a term depends only on the term, the simp set named by the call, the
configuration, and the facts that `withNormalNodes` keys the run on. The simplifications use
`steppingDischarge?`, which proves a side condition from the simp set and never from a
hypothesis, so the hypotheses outside the facts cannot change a result. A call with another
discharger, `contextual`, `+arith` or `at h`, and a call that follows a tactic of the same step
that adds, clears or reverts a hypothesis, must not use it. Every fact spliced into a
`cil_simp_only` call inside a step must be one of the facts `withNormalNodes` was given, because
the contexts the record caches are named by the call's text with macro scopes erased. The
options that change what simp does must stay fixed during a driver for the same reason.

At the start of each step `withNormalNodes` keeps each shelf whose local context the step's
context extends without changing a hypothesis, and drops the others, so a driver that rewrites,
renames or clears a hypothesis, as a snapshot or loop-frame store that clears the facts it
supersedes does, cannot reach a stale record while a step that only adds hypotheses, as a call
does, keeps it. The equation index outlives a cleared hypothesis and skips its entries. A step
in a longer context elaborates its facts again, since a name may now refer to a new hypothesis.
The record lives in the environment, so a backtracked step forgets what it recorded.
`withNormalRun` opens it for one driver and restores the earlier record when the driver ends,
however it ends, `withNormalNodes` drops it when a step fails, and a step outside a driver keeps
none. `cil.stepping.record` turns the record off; a lookup without an equation index scans the
local context instead.
-/

namespace CIL.Safety

open Lean Elab Tactic Meta

/-- The identity of a local context: its size and its last declaration. A step that adds,
    clears or replaces a hypothesis changes it. -/
def contextId (context : LocalContext) : Nat × Option FVarId :=
  (context.numIndices, context.lastDecl.map (·.fvarId))

/-- Whether two declarations state the same hypothesis: name, user name, type and value. -/
def sameDeclaration (left right : LocalDecl) : Bool :=
  left.fvarId == right.fvarId && left.userName == right.userName && left.type == right.type &&
    left.value? == right.value?

/-- Whether `earlier` and `current` are one object in memory, which makes them equal. -/
private unsafe def sameObjectUnsafe {α : Type} (earlier current : α) : Bool :=
  ptrAddrUnsafe earlier == ptrAddrUnsafe current

/-- Whether `earlier` and `current` are one object; `false` only means they must be compared. -/
@[implemented_by sameObjectUnsafe]
def sameObject {α : Type} (_earlier _current : α) : Bool := false

/-- How many context positions the comparisons of `contextExtendedBy` and `contextKeeps` have
    read. Tests read it to bound the whole-context comparisons of a step, which cost time but no
    heartbeats. It lives in the environment, so a backtracked attempt's reads are forgotten. -/
initialize contextReadsExtension : EnvExtension Nat ←
  registerEnvExtension (pure 0) (asyncMode := .local)

/-- The context positions compared so far in this environment. -/
def contextReads : CoreM Nat :=
  return contextReadsExtension.getState (← getEnv)

/-- Whether every position of `earlier` holds the same hypothesis in `current`, where `cleared`
    says whether a hypothesis `current` no longer holds is allowed. Two contexts that are one
    object are equal and read no position; other comparisons are counted in `contextReads`. -/
def compareContexts (cleared : Bool) (earlier current : LocalContext) : CoreM Bool := do
  if sameObject earlier current then return true
  if current.numIndices < earlier.numIndices then return false
  modifyEnv (contextReadsExtension.modifyState · (· + earlier.numIndices))
  for position in [:earlier.numIndices] do
    match earlier.decls[position]!, current.decls[position]! with
    | none, none => pure ()
    | some _, none => unless cleared do return false
    | some old, some new => unless sameObject old new || sameDeclaration old new do return false
    | none, some _ => return false
  return true

/-- Whether `current` holds every hypothesis of `earlier`, unchanged and in the same positions,
    followed by any number of others. A step that rewrites a hypothesis in place, renames it or
    clears it makes this false; a step that only adds hypotheses keeps it true. -/
def contextExtendedBy (earlier current : LocalContext) : CoreM Bool :=
  compareContexts false earlier current

/-- Whether every hypothesis of `earlier` that `current` still holds is unchanged and in the same
    position, so that an index of `earlier`'s equations is right for `current` once the entries of
    cleared hypotheses are skipped. A store that clears the facts it supersedes keeps it true. -/
def contextKeeps (earlier current : LocalContext) : CoreM Bool :=
  compareContexts true earlier current

/-- The left side of the equation `type` states, under any quantifiers, whose variables stay
    loose. -/
def equationLeft? : Expr → Option Expr
  | .forallE _ _ body _ => equationLeft? body
  | .mdata _ body => equationLeft? body
  | type => type.eq?.map fun (_, lhs, _) => lhs.consumeMData

/-- The head of the left side of the equation `type` states, under any quantifiers. -/
def equationHead? (type : Expr) : Option Expr :=
  (equationLeft? type).map (·.getAppFn)

/-- `equationHead?` of `type` with its metavariables instantiated, instantiating only those on
    the way to the head, so a lookup that reads every hypothesis does not rebuild their types. -/
partial def instantiatedEquationHead? (type : Expr) : MetaM (Option Expr) := do
  match type with
  | .forallE _ _ body _ | .mdata _ body => instantiatedEquationHead? body
  | _ =>
    if type.getAppFn.isMVar then return equationHead? (← instantiateMVars type)
    let some (_, left, _) := type.eq? | return none
    let head := left.consumeMData.getAppFn
    if head.isMVar then return some (← instantiateMVars left).consumeMData.getAppFn
    return some head

/-- Whether `head` is a definition that reducible unfolding replaces at the head of a term. -/
def headUnfolds (head : Expr) : CoreM Bool := do
  let .const name _ := head | return false
  if ← isReducible name then return !(← isProjectionFn name)
  return false

/-- Whether a hypothesis whose left side has head `found` may state a lookup whose left side has
    head `wanted`, where `wantedUnfolds` is `headUnfolds wanted`: unless both are constants,
    other ones, and neither is a definition that reducible unfolding replaces. -/
def headsMayMeet (wanted : Expr) (wantedUnfolds : Bool) (found : Expr) : CoreM Bool := do
  let (.const wantedName _, .const foundName _) := (wanted, found) | return true
  if wantedName == foundName || wantedUnfolds then return true
  headUnfolds found

/-- The functions on natural numbers that unification evaluates on literals. -/
def naturalEvaluations : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pow, ``Nat.succ, ``Nat.pred]

/-- The operator classes whose instances on natural numbers unification evaluates on literals. -/
def naturalOperators : List Name :=
  [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow, ``Add.add,
    ``Sub.sub, ``Mul.mul, ``Div.div, ``Mod.mod, ``Pow.pow, ``NatPow.pow, ``HomogeneousPow.pow]

/-- Whether `type` is `Nat` once reduced, as the tree decides it for offsets. -/
def naturalType (type : Expr) : MetaM Bool :=
  return (← whnf type).isConstOf ``Nat

/-- Whether `term` is headed by an arithmetic function or operator that unification may
    evaluate. -/
def arithmeticHead (term : Expr) : Bool :=
  match term.getAppFn with
  | .const name _ => naturalEvaluations.contains name || naturalOperators.contains name
  | _ => false

/-- `term` with each natural-number arithmetic on literals replaced by its value, which
    unification equates it with, so that the tree keys it as that literal. -/
def evaluateNaturals (term : Expr) : MetaM Expr := do
  unless (term.find? arithmeticHead).isSome do return term
  Meta.transform term (pre := fun part => do
    unless arithmeticHead part do return .continue
    let .const name _ := part.getAppFn | return .continue
    let onNatural ← if naturalOperators.contains name && part.getAppNumArgs > 0 then
        naturalType (part.getArg! 0)
      else pure true
    unless onNatural do return .continue
    match ← (evalNat part).run with
    | some value => return .done (mkNatLit value)
    | none => return .continue)

/-- Whether the tree keys `term` as a natural-number literal. -/
partial def treeNumeral (term : Expr) : Bool :=
  term.isRawNatLit || term.isConstOf ``Nat.zero ||
    (term.isAppOfArity ``Nat.succ 1 && treeNumeral term.appArg!) ||
    (term.isAppOfArity ``OfNat.ofNat 3 && treeNumeral (term.getArg! 1))

/-- Whether the tree keys `term`, below the root, as a wildcard: a successor, or a sum on natural
    numbers whose last operand is a numeral. -/
def treeOffset (term : Expr) : MetaM Bool := do
  if term.isAppOfArity ``Nat.succ 1 then return true
  if term.isAppOfArity ``Nat.add 2 then return treeNumeral term.appArg!
  if term.isAppOfArity ``Add.add 4 then
    return treeNumeral term.appArg! && (← naturalType (term.getArg! 0))
  if term.isAppOfArity ``HAdd.hAdd 6 then
    return treeNumeral term.appArg! && (← naturalType (term.getArg! 1))
  return false

/-- Whether unification at reducible transparency, which `cil_lookup_assumption` uses, can equate
    `term` only with terms whose discrimination-tree keys match its own, where `indexed` says
    whether the tree keys `term` as an entry or as a lookup. It reads `term` as the tree does,
    after the same reducible unfolding of let variables and definitions, and fails at what
    unification decides beyond the keys: natural-number arithmetic it evaluates, except a sum the
    tree keys as a wildcard in an entry, a structure constructor it matches against projections
    (structure eta), and a value of a type with one value. Instance arguments and proofs, which
    the tree does not key, are not read. -/
partial def keyedExactly (indexed root : Bool) (term : Expr) : MetaM Bool := withReducible do
  let term ← DiscrTree.reduceDT term root
  unless root do
    if treeNumeral term then return true
    if indexed then if ← treeOffset term then return true
  let type ← inferType term
  -- The tree does not key a proof below the root, and unification does not compare proofs.
  if !root then if ← isProp type then return true
  let oneValue ← matchConstNonRecStructure (← whnf type).getAppFn
    (fun _ => pure false) fun induct _ constructor =>
      return constructor.numFields == 0 && (← useEtaStruct induct.name)
  if oneValue then return false
  let function := term.getAppFn
  if let .const name _ := function then
    if naturalEvaluations.contains name then return false
    if naturalOperators.contains name && term.getAppNumArgs > 0 then
      if ← naturalType (term.getArg! 0) then return false
    if let some (.ctorInfo constructor) := (← getEnv).find? name then
      if isNonRecStructure (← getEnv) constructor.induct then return false
  match function with
  | .proj _ _ projected => unless ← keyedExactly indexed false projected do return false
  | .forallE _ domain _ _ => return ← keyedExactly indexed false domain
  | _ => pure ()
  let arguments := term.getAppArgs
  let parameters := (← getFunInfoNArgs function arguments.size).paramInfo
  for position in [:arguments.size] do
    let argument := arguments[position]!
    if parameters[position]?.any (·.isInstance) then continue
    unless ← keyedExactly indexed false argument do return false
  return true

/-- An equation hypothesis: its position in the context, its name, and the head of its left
    side. -/
structure EquationEntry where
  /-- Its position in the local context. -/
  position : Nat
  /-- The hypothesis. -/
  hypothesis : FVarId
  /-- The head of its left side, which `headsMayMeet` compares. -/
  head : Expr
  deriving Inhabited

/-- The hypotheses of a local context that state an equation, indexed by their left sides so that
    a lookup reads only those that may unify with it at reducible transparency, as
    `cil_lookup_assumption` unifies. Extending it for a longer context reads only the added
    hypotheses. -/
structure EquationIndex where
  /-- How many declarations of the context it covers. -/
  covered : Nat := 0
  /-- Every equation hypothesis, in context order. -/
  all : Array EquationEntry := #[]
  /-- The equation hypotheses whose left sides `keyedExactly` accepts, by their discrimination-tree
      keys. -/
  tree : DiscrTree (Nat × FVarId) := {}
  /-- The other equation hypotheses, which a lookup reads by the heads of their left sides. -/
  unkeyed : Array EquationEntry := #[]

instance : Inhabited EquationIndex := ⟨{}⟩

/-- The index extended to the hypotheses of `context` that it does not cover. A quantified
    variable of a hypothesis becomes a metavariable, which the tree keys as matching anything; a
    metavariable the hypothesis itself holds may be assigned later, so that hypothesis is
    unkeyed. -/
def EquationIndex.extend (index : EquationIndex) (context : LocalContext) :
    MetaM EquationIndex := do
  if index.covered == context.numIndices then return index
  withLCtx context (← getLocalInstances) do
  let mut index := index
  for position in [index.covered:context.numIndices] do
    let some declaration := context.decls[position]! | continue
    if declaration.isImplementationDetail then continue
    let type ← instantiateMVars declaration.type
    let some left := equationLeft? type | continue
    let entry : EquationEntry := ⟨declaration.index, declaration.fvarId, left.getAppFn⟩
    index := { index with all := index.all.push entry }
    let keyed? ← if left.hasExprMVar then pure none else withoutModifyingState do
      let (_, _, body) ← forallMetaTelescope type
      let some (_, left, _) := body.consumeMData.eq? | return none
      try
        let left ← evaluateNaturals left
        unless ← keyedExactly true true left do return none
        return some (← index.tree.insert left (entry.position, entry.hypothesis))
      catch _ => return none
    index := match keyed? with
      | some tree => { index with tree }
      | none => { index with unkeyed := index.unkeyed.push entry }
  return { index with covered := context.numIndices }

/-- The index rebuilt for `context` once more than half of its entries name hypotheses that
    `context` no longer holds, as after stores that clear the facts they supersede; the tree
    cannot drop an entry, so a walk would otherwise read every cleared one at each lookup. -/
def EquationIndex.prune (index : EquationIndex) (context : LocalContext) :
    MetaM EquationIndex := do
  let live := index.all.foldl (init := 0) fun count entry =>
    if context.contains entry.hypothesis then count + 1 else count
  if 2 * live >= index.all.size then return index
  ({} : EquationIndex).extend context

/-- The equation hypotheses that may state the goal `goal`, in context order: those the tree finds
    for its left side with the unkeyed ones whose head `headsMayMeet` the goal's, or every one
    whose head does when `keyedExactly` rejects the left side or the goal is quantified. -/
def EquationIndex.candidates (index : EquationIndex) (goal : Expr) : MetaM (Array FVarId) := do
  let some wanted := equationHead? goal | return #[]
  let wantedUnfolds ← headUnfolds wanted
  let meeting (entries : Array EquationEntry) : MetaM (Array (Nat × FVarId)) :=
    entries.filterMapM fun entry => do
      if ← headsMayMeet wanted wantedUnfolds entry.head then
        return some (entry.position, entry.hypothesis)
      return none
  let keyed? ← withoutModifyingState do
    let some (_, lookup, _) := goal.consumeMData.eq? | return none
    try
      let lookup ← evaluateNaturals lookup
      unless ← keyedExactly false true lookup do return none
      return some (← index.tree.getUnify lookup)
    catch _ => return none
  let some keyed := keyed? | return (← meeting index.all).map (·.2)
  return ((keyed ++ (← meeting index.unkeyed)).qsort (·.1 < ·.1)).map (·.2)

/-- What a stepping run has established for one local context and one set of facts. -/
structure NormalShelf where
  /-- The facts of the step that made the shelf, as elaborated; see `factsKey`. -/
  key : Option (Array Expr) := none
  /-- The identity of the local context the shelf was last used in. -/
  context : Nat × Option FVarId := (0, none)
  /-- The local context the shelf was last used in. -/
  locals : LocalContext := {}
  /-- The syntax of the facts that `key` was built from. -/
  factsSeen : Array Syntax := #[]
  /-- How many nodes are recorded. -/
  count : Nat := 0
  /-- For each simplification, by name, the terms it visited and left unchanged. -/
  nodes : PersistentHashMap String (PersistentHashSet Expr) := {}
  /-- The simplification contexts the run built, by the arguments that name them. -/
  contexts : Array (String × Simp.Context × Simp.SimprocsArray) := #[]

instance : Inhabited NormalShelf := ⟨{}⟩

/-- What a stepping driver has established: the shelf its current step reads and writes, and the
    shelves of other facts it used in the same local context, so a walk whose steps read
    different groups of facts keeps one shelf for each. -/
structure NormalNodes extends NormalShelf where
  /-- Whether a driver opened this record with `withNormalRun`; a step outside a driver keeps
      none, so a record never outlives its driver. -/
  driven : Bool := false
  /-- Whether a step is running, so the simplifications consult the record. -/
  active : Bool := false
  /-- How many steps the driver has run, counting those before the record is used. -/
  steps : Nat := 0
  /-- The shelves that are not current. -/
  others : Array NormalShelf := #[]
  /-- The equation hypotheses of `equationLocals`, which every shelf shares. -/
  equations : EquationIndex := {}
  /-- The local context `equations` was built for; none until a step of the driver builds it. -/
  equationLocals : Option LocalContext := none

instance : Inhabited NormalNodes := ⟨{}⟩

/-- Most shelves a driver keeps. -/
def normalShelfLimit : Nat := 8

/-- Holds the record of the running stepping driver. -/
initialize normalNodesExtension : EnvExtension NormalNodes ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- Most nodes the record keeps; a longer run starts a new record. -/
def normalNodeLimit : Nat := 2000000

/-- The record of the running stepping driver. -/
def getNormalNodes : CoreM NormalNodes :=
  return normalNodesExtension.getState (← getEnv)

/-- Replace the record of the running stepping driver. -/
def setNormalNodes (record : NormalNodes) : CoreM Unit :=
  modifyEnv fun env => normalNodesExtension.setState env record

/-- Whether `record` may be consulted for a goal with local context `context`: a step is running
    and the record was made for this context. A record from another goal or declaration is
    never used. -/
def NormalNodes.usable (record : NormalNodes) (context : LocalContext) : CoreM Bool := do
  if !record.active || record.context != contextId context then return false
  contextExtendedBy record.locals context

/-- The equation index of `record` for `context`: the one it holds, extended, when `context` still
    has every hypothesis it indexed unchanged, and built again otherwise. -/
def NormalNodes.equationsFor (record : NormalNodes) (context : LocalContext) :
    MetaM EquationIndex := do
  let known ← match record.equationLocals with
    | some locals => pure (if ← contextKeeps locals context then record.equations else {})
    | none => pure {}
  (← known.prune context).extend context

/-- Whether stepping drivers use the record. Turning it off makes every simplification visit the
    whole goal, which leaves the same goals and costs more per step the longer the run. -/
register_option cil.stepping.record : Bool := {
  defValue := true
  descr := "Let stepping tactics skip terms that earlier steps of the run left unchanged."
}

/-- How many steps of a driver run before the record is used. The goal of a short run is small, so
    the whole-goal simplification costs less than keeping the record. -/
register_option cil.stepping.warmup : Nat := {
  defValue := 12
  descr := "Steps of a stepping driver that run before it starts to use the record."
}

/-- The record, when it may be consulted for the current local context. -/
def usableNormalNodes : MetaM (Option NormalNodes) := do
  unless cil.stepping.record.get (← getOptions) do return none
  let record ← getNormalNodes
  return if ← record.usable (← getLCtx) then some record else none

/-- The terms the simplification `name` visited and left unchanged in earlier steps. -/
def NormalNodes.normalFor (record : NormalNodes) (name : String) : PersistentHashSet Expr :=
  (record.nodes.find? name).getD {}

/-- The terms the simplification `name` may skip now; none when the record is not usable. -/
def normalNodesFor (name : String) : MetaM (PersistentHashSet Expr) := do
  return (← usableNormalNodes).map (·.normalFor name) |>.getD {}

/-- Add `fresh` to the terms the simplification `name` leaves alone, when the record is usable.
    Terms with metavariables or loose bound variables are not recorded: a later assignment or
    binder instance would change what they mean. Neither are terms with a free variable outside
    the local context, such as the temporary variables simp opens under a binder, which can
    never occur again. -/
def recordNormalNodes (name : String) (fresh : Array Expr) : MetaM Unit := do
  let some record ← usableNormalNodes | return
  let context ← getLCtx
  let fresh := fresh.filter fun expr => !expr.hasMVar && !expr.hasLooseBVars &&
    !(expr.hasFVar && expr.hasAnyFVar fun free => !context.contains free)
  if fresh.isEmpty then return
  let known := fresh.foldl (fun nodes expr => nodes.insert expr) (record.normalFor name)
  let nodes := record.nodes.insert name known
  setNormalNodes { record with nodes, count := record.count + fresh.size }

/-- Walks `expr` as a DAG, each term once. Returns whether some term satisfies `flagged`, and
    records in the state every term below which none does. Terms in `known` are clean and are
    not entered. -/
partial def cleanWalk (flagged : Expr → Bool) (known : PersistentHashSet Expr) (expr : Expr) :
    StateM (Std.HashMap Expr Bool × Array Expr) Bool := do
  if known.contains expr then return false
  if let some seen := (← get).1[expr]? then return seen
  let children : List Expr := match expr with
    | .app function argument => [function, argument]
    | .mdata _ body | .proj _ _ body => [body]
    | .lam _ domain body _ | .forallE _ domain body _ => [domain, body]
    | .letE _ type value body _ => [type, value, body]
    | _ => []
  let mut found := flagged expr
  for child in children do
    if ← cleanWalk flagged known child then found := true
  modify fun (seen, clean) =>
    (seen.insert expr found, if found || expr.hasLooseBVars then clean else clean.push expr)
  return found

initialize registerTraceClass `CIL.record

/-- The key of the facts a step is given: what the facts state and prove, not how they are
    written, so two runs whose prepared facts print alike but differ are told apart. A fact
    that elaborates with metavariables, as a lemma with implicit arguments or universe
    parameters does, is keyed by its abstraction over them, which is the same term each time.
    `none` when a fact does not elaborate; the step then runs without the record and
    `trace.CIL.record` says which fact. -/
def factsKey (facts : Array Term) : TacticM (Option (Array Expr)) := do
  let mut key : Array Expr := #[]
  for fact in facts do
    -- A hypothesis named in the context is keyed by itself and its type, with no elaboration.
    if fact.raw.isIdent then
      if let some declaration := (← getLCtx).findFromUserName? fact.raw.getId then
        key := key.push declaration.toExpr |>.push (← abstractMVars declaration.type).expr
        continue
    let saved ← saveState
    let element? : Except MessageData Expr ← try
      let proof ← Term.withoutErrToSorry <| Term.elabTerm fact none
      Term.synthesizeSyntheticMVarsNoPostponing
      pure (.ok (← abstractMVars (← instantiateMVars proof)).expr)
    catch error => pure (.error error.toMessageData)
    saved.restore
    match element? with
    | .ok element => key := key.push element
    | .error message =>
      trace[CIL.record] "the step runs without the record, since fact {fact} does not \
        elaborate: {message}"
      return none
  return some key

/-- Starts a driver's record, empty, and returns the earlier record for `leaveNormalRun`. A driver
    that mutates its own variables calls these around a `try ... finally`; any other uses
    `withNormalRun`. -/
def enterNormalRun : TacticM NormalNodes := do
  let outer ← getNormalNodes
  setNormalNodes { driven := true }
  return outer

/-- Restores the record that was current before `enterNormalRun`. -/
def leaveNormalRun (outer : NormalNodes) : TacticM Unit :=
  setNormalNodes outer

/-- Runs a driver with an empty record and restores the earlier record when the driver ends,
    whether it succeeds or fails. -/
def withNormalRun {α : Type} (driver : TacticM α) : TacticM α := do
  let outer ← enterNormalRun
  try driver finally leaveNormalRun outer

/-- Runs the tactics with `withNormalRun`, so a driver written as a macro scopes the record. -/
elab "cil_normal_run " steps:tacticSeq : tactic => withNormalRun (evalTactic steps)

/-- Runs one stepping step so that its simplifications leave alone what earlier steps of the
    same driver visited and left unchanged. The record is kept while the facts and the local
    context stay the same and dropped when they change, and a driver that alternates between
    several facts keeps a shelf for each; a step that fails drops them, and the record is never
    left active. A step nested in another with different facts runs on its own shelf, and the
    outer record is restored after it. A step outside a driver, which `withNormalRun` has not
    opened, runs plainly. -/
def withNormalNodes {α : Type} (facts : Array Term) (step : TacticM α) : TacticM α := do
  let outer ← getNormalNodes
  if !outer.driven || !cil.stepping.record.get (← getOptions) then return ← step
  let noGoals := (← getGoals).isEmpty
  let localContext ← if noGoals then getLCtx else withMainContext getLCtx
  -- Looking the equation hypotheses up is a failed attempt's work, which a backtrack discards,
  -- so every step of a driver starts with them, those before the record is used included.
  let equations ← outer.equationsFor localContext
  if outer.steps < cil.stepping.warmup.get (← getOptions) then
    setNormalNodes { outer with
      steps := outer.steps + 1, equations, equationLocals := some localContext }
    return ← step
  let context := contextId localContext
  -- A shelf stays valid while the hypotheses it was made for are unchanged, so a step that only
  -- adds hypotheses keeps it; one that rewrites, renames or clears a hypothesis does not.
  let kept (shelf : NormalShelf) : TacticM Bool := contextExtendedBy shelf.locals localContext
  let currentKept ← kept outer.toNormalShelf
  let shelves := (if currentKept then #[outer.toNormalShelf] else #[]) ++
    (← outer.others.filterM kept)
  -- The same syntax in the same context states the same facts, so a walk elaborates them once;
  -- in a longer context a name may refer to a new hypothesis, so the facts are elaborated again.
  let raw := facts.map (·.raw)
  let mut index := shelves.findIdx? fun shelf =>
    shelf.key.isSome && shelf.factsSeen == raw && shelf.context == context
  let mut key := index.bind fun position => shelves[position]!.key
  if key.isNone then
    key ← if noGoals then factsKey facts else withMainContext (factsKey facts)
    let some elaborated := key | return ← step
    index := shelves.findIdx? (·.key == some elaborated)
  let fresh : NormalShelf := { key, context, locals := localContext, factsSeen := raw }
  let selected := match index with
    | some position => if shelves[position]!.count < normalNodeLimit then shelves[position]!
      else fresh
    | none => fresh
  let remaining := (shelves.eraseIdxIfInBounds (index.getD shelves.size)).extract 0
    (normalShelfLimit - 1)
  let shared := currentKept && index == some 0 && outer.count < normalNodeLimit
  let current : NormalNodes :=
    { selected with
      factsSeen := raw, driven := true, steps := outer.steps, others := remaining,
      context := context, locals := localContext, equations := equations,
      equationLocals := some localContext }
  setNormalNodes { current with active := true }
  -- The finalizer also runs for heartbeat and interrupt exceptions, which `catch` does not see.
  let (result, _) ← tryFinally' step fun result? => do
    if result?.isSome then
      let after ← getNormalNodes
      setNormalNodes (if outer.active && !shared then outer
        else { after with active := outer.active })
    else
      -- The equation index depends on the hypotheses alone, so it outlives a failed step.
      setNormalNodes (if outer.active then outer else
        { driven := true, steps := outer.steps, equations,
          equationLocals := some localContext })
  return result

/-- `simp only [arguments]` on the goal that leaves alone what the running stepping driver
    already visited and left unchanged. It discharges side conditions with `steppingDischarge?`,
    so a hypothesis outside `arguments` never proves one. -/
syntax (name := cilSimpOnly) "cil_simp_only " " ["
  withoutPosition((Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),*,?) "]" : tactic

/-- Simp's default discharger without its search of the hypotheses for a side condition of an
    equation theorem. Each hypothesis tried costs a unification, so the default cost grows with
    the hypotheses in scope; this one decides a side condition by the simp set alone, and the
    result of a simplification does not depend on the hypotheses outside it. -/
def steppingDischarge? (condition : Expr) : Simp.SimpM (Option Expr) := do
  let condition := condition.cleanupAnnotations
  if Simp.isEqnThmHypothesis condition then
    if let some proof ← Simp.dischargeEqnThmHypothesis? condition then return some proof
  let simplified ← Simp.simp condition
  if let some proof ← Simp.dischargeRfl simplified.expr then
    return some (mkApp4 (mkConst ``Eq.mpr [Level.zero]) condition simplified.expr
      (← simplified.getProof) proof)
  else if simplified.expr.isTrue then
    return some (← mkOfEqTrue (← simplified.getProof))
  else
    return none

/-- Simplify `target` with `ctx`. When the record is usable, a term the simplification `name`
    left unchanged in an earlier step is returned as it is, and the terms this call visited and
    left unchanged are recorded. -/
def simpLeavingAlone (name : String) (target : Expr) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) : MetaM Simp.Result := do
  let defaults := { Simp.mkDefaultMethodsCore simprocs with discharge? := steppingDischarge? }
  let some record ← usableNormalNodes
    | return (← Simp.mainCore target ctx {} defaults).1
  let known := record.normalFor name
  let methods : Simp.Methods := { defaults with
    pre := fun expr =>
      if known.contains expr then return .done { expr } else defaults.pre expr }
  let (result, state) ← Simp.mainCore target ctx {} methods
  let unchanged := state.cache.fold (init := #[]) fun found expr visit =>
    if visit.proof?.isNone && visit.cache && visit.expr == expr && !known.contains expr then
      found.push expr
    else found
  recordNormalNodes name unchanged
  return result

/-- The arguments of a simp call as text, ignoring the macro scopes that each expansion adds. -/
partial def simpArgumentsKey : Syntax → String
  | .atom _ value => value
  | .ident _ _ name _ => name.eraseMacroScopes.toString
  | .node _ kind arguments =>
    s!"({kind}{arguments.foldl (fun text part => text ++ " " ++ simpArgumentsKey part) ""})"
  | .missing => "_"

/-- The simplification context for `simp only [arguments]`, built once per record: the lemmas
    and facts are elaborated from syntax, which a step would otherwise repeat. -/
def simpOnlyContext (key : String)
    (arguments : Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
      `Lean.Parser.Tactic.simpLemma] ",") : TacticM (Simp.Context × Simp.SimprocsArray) := do
  let usable ← usableNormalNodes
  if let some record := usable then
    if let some (_, ctx, simprocs) := record.contexts.find? (·.1 == key) then
      return (ctx, simprocs)
  let { ctx, simprocs, .. } ←
    mkSimpContext (← `(tactic| simp only [$arguments,*])) (eraseLocal := false)
  if usable.isSome then
    let current ← getNormalNodes
    setNormalNodes { current with contexts := current.contexts.push (key, ctx, simprocs) }
  return (ctx, simprocs)

/-- Simplify the goal as `simp only [arguments]` does, leaving alone what the running stepping
    driver already visited and left unchanged. A simplification that changes nothing fails when
    `required` and otherwise succeeds, so the terms it visited are still recorded. Returns
    whether the goal changed. -/
def cilSimp (required : Bool)
    (arguments : Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
      `Lean.Parser.Tactic.simpLemma] ",") : TacticM Bool := withMainContext do
  -- The key names the call for the record; a plain call has no use for it.
  let key := if (← usableNormalNodes).isSome then
      simpArgumentsKey (mkNullNode arguments.elemsAndSeps)
    else ""
  let (ctx, simprocs) ← simpOnlyContext key arguments
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let result ← profileitM Exception "simp" (← getOptions) <|
    simpLeavingAlone key target ctx simprocs
  if result.expr.isTrue then
    goal.assign (← match result.proof? with
      | some proof => mkOfEqTrue proof
      | none => pure (mkConst ``True.intro))
    replaceMainGoal []
    return true
  else if result.proof?.isNone && result.expr == target then
    if required then throwError "`simp` made no progress"
    return false
  else
    replaceMainGoal [← applySimpResultToTarget goal target result]
    return true

/-- `cil_simp_only [arguments]` written as syntax, run so that it reports whether the goal
    changed instead of failing when it did not. A failure would restore the state and drop what
    the simplification visited, which the next step would visit again. -/
def cilSimpProgress (call : TSyntax `tactic) : TacticM Bool := do
  let `(tactic| cil_simp_only [$arguments,*]) := call | throwUnsupportedSyntax
  cilSimp false arguments

/-- Elaborates `cil_simp_only`. -/
@[tactic cilSimpOnly]
def evalCilSimpOnly : Tactic := fun stx => do
  let `(tactic| cil_simp_only [$arguments,*]) := stx | throwUnsupportedSyntax
  discard <| cilSimp true arguments

/-- `try cil_simp_only [arguments]`, which keeps what the simplification visited. -/
syntax (name := cilTrySimpOnly) "cil_try_simp_only " " ["
  withoutPosition((Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),*,?) "]" : tactic

/-- Elaborates `cil_try_simp_only`. -/
@[tactic cilTrySimpOnly]
def evalCilTrySimpOnly : Tactic := fun stx => do
  let `(tactic| cil_try_simp_only [$arguments,*]) := stx | throwUnsupportedSyntax
  let saved ← saveState
  try discard <| cilSimp false arguments catch _ => saved.restore

end CIL.Safety
