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
simplification contexts and the list of equation hypotheses of the run, which every step would
otherwise rebuild.

Invariant for a tactic that reads the record: it runs inside `withNormalNodes`, on a goal whose
local context is the one the record was made for (`NormalNodes.usable` checks this), and the
result it records for a term depends only on the term, the simp set named by the call, the
configuration, and the facts that `withNormalNodes` keys the run on. A call with a discharger,
`contextual`, `+arith` or `at h`, and a call that follows a tactic of the same step that adds,
clears or reverts a hypothesis, must not use it. Every fact spliced into a `cil_simp_only` call
inside a step must be one of the facts `withNormalNodes` was given, because the contexts the
record caches are named by the call's text with macro scopes erased. The options that change what
simp does must stay fixed during a driver for the same reason.

At the start of each step `withNormalNodes` compares the local context's hypotheses (names,
types, values, user names) and the elaborated facts with those of each shelf, and starts a new
shelf when none matches, so a driver that rewrites, renames or clears a hypothesis in place
cannot reach a stale record. The record lives in the environment, so a backtracked step forgets
what it recorded. `withNormalRun` opens it for one driver and restores the earlier record when
the driver ends, however it ends, `withNormalNodes` drops it when a step fails, and a step
outside a driver keeps none. `cil.stepping.record` turns the record off.
-/

namespace CIL.Safety

open Lean Elab Tactic Meta

/-- The identity of a local context: its size and its last declaration. A step that adds,
    clears or replaces a hypothesis changes it. -/
def contextId (context : LocalContext) : Nat × Option FVarId :=
  (context.numIndices, context.lastDecl.map (·.fvarId))

/-- A digest of every hypothesis of a local context: its name, type, value and user name. A step
    that rewrites a hypothesis in place or renames it changes the digest, which `contextId`
    does not. -/
def contextDigest (context : LocalContext) : UInt64 :=
  context.foldl (init := 11) fun digest declaration =>
    mixHash digest (mixHash (hash declaration.fvarId.name) (mixHash declaration.type.hash
      (mixHash (hash declaration.userName) ((declaration.value?.map Expr.hash).getD 0))))

/-- What a stepping run has established for one local context and one set of facts. -/
structure NormalShelf where
  /-- The facts of the step that made the shelf, as elaborated; see `factsKey`. -/
  key : Option (Array Expr) := none
  /-- The local context the shelf was made for. -/
  context : Nat × Option FVarId := (0, none)
  /-- The digest of that context's hypotheses. -/
  digest : UInt64 := 0
  /-- The syntax of the facts that `key` was built from. -/
  factsSeen : Array Syntax := #[]
  /-- How many nodes are recorded. -/
  count : Nat := 0
  /-- For each simplification, by name, the terms it visited and left unchanged. -/
  nodes : PersistentHashMap String (PersistentHashSet Expr) := {}
  /-- The hypotheses that state an equation, with the head of the left side. -/
  equations : Option (Array (FVarId × Expr)) := none
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
def NormalNodes.usable (record : NormalNodes) (context : LocalContext) : Bool :=
  record.active && record.context == contextId context

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
  return if record.usable (← getLCtx) then some record else none

/-- The terms the simplification `name` visited and left unchanged in earlier steps. -/
def NormalNodes.normalFor (record : NormalNodes) (name : String) : PersistentHashSet Expr :=
  (record.nodes.find? name).getD {}

/-- The terms the simplification `name` may skip now; none when the record is not usable. -/
def normalNodesFor (name : String) : MetaM (PersistentHashSet Expr) := do
  return (← usableNormalNodes).map (·.normalFor name) |>.getD {}

/-- Add `fresh` to the terms the simplification `name` leaves alone, when the record is usable.
    Terms with metavariables or loose bound variables are not recorded: a later assignment or
    binder instance would change what they mean. -/
def recordNormalNodes (name : String) (fresh : Array Expr) : MetaM Unit := do
  let some record ← usableNormalNodes | return
  let fresh := fresh.filter fun expr => !expr.hasMVar && !expr.hasLooseBVars
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
  if outer.steps < cil.stepping.warmup.get (← getOptions) then
    setNormalNodes { outer with steps := outer.steps + 1 }
    return ← step
  let noGoals := (← getGoals).isEmpty
  let localContext ← if noGoals then getLCtx else withMainContext getLCtx
  let context := contextId localContext
  let digest := contextDigest localContext
  let sameContext (shelf : NormalShelf) := shelf.context == context && shelf.digest == digest
  -- Shelves of an earlier context can never match again; the current shelf comes first.
  let currentKept := sameContext outer.toNormalShelf
  let shelves := (if currentKept then #[outer.toNormalShelf] else #[]) ++
    outer.others.filter sameContext
  -- The same syntax in the same context states the same facts, so a walk elaborates them once.
  let raw := facts.map (·.raw)
  let mut index := shelves.findIdx? fun shelf => shelf.key.isSome && shelf.factsSeen == raw
  let mut key := index.bind fun position => shelves[position]!.key
  if key.isNone then
    key ← if noGoals then factsKey facts else withMainContext (factsKey facts)
    let some elaborated := key | return ← step
    index := shelves.findIdx? (·.key == some elaborated)
  let fresh : NormalShelf := { key, context, digest, factsSeen := raw }
  let selected := match index with
    | some position => if shelves[position]!.count < normalNodeLimit then shelves[position]!
      else fresh
    | none => fresh
  let remaining := (shelves.eraseIdxIfInBounds (index.getD shelves.size)).extract 0
    (normalShelfLimit - 1)
  let shared := currentKept && index == some 0 && outer.count < normalNodeLimit
  let current : NormalNodes :=
    { selected with factsSeen := raw, driven := true, steps := outer.steps, others := remaining }
  setNormalNodes { current with active := true }
  -- The finalizer also runs for heartbeat and interrupt exceptions, which `catch` does not see.
  let (result, _) ← tryFinally' step fun result? => do
    if result?.isSome then
      let after ← getNormalNodes
      setNormalNodes (if outer.active && !shared then outer
        else { after with active := outer.active })
    else
      setNormalNodes (if outer.active then outer else { driven := true, steps := outer.steps })
  return result

/-- `simp only [arguments]` on the goal that leaves alone what the running stepping driver
    already visited and left unchanged. Outside a step it is `simp only`. -/
syntax (name := cilSimpOnly) "cil_simp_only " " ["
  withoutPosition((Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),*,?) "]" : tactic

/-- Simplify `target` with `ctx`. When the record is usable, a term the simplification `name`
    left unchanged in an earlier step is returned as it is, and the terms this call visited and
    left unchanged are recorded. -/
def simpLeavingAlone (name : String) (target : Expr) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) : MetaM Simp.Result := do
  let defaults := Simp.mkDefaultMethodsCore simprocs
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
