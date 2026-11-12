import Lean
import Lean.Linter.Basic
import CIL.DebugNames
import CIL.Safety.FailureRecords
import CIL.Safety.MissingFacts
import CIL.TermAccess

/-!
# Observing LeanCIL tactics

What each LeanCIL tactic did, read after each command from its info trees, so the tactics run
exactly the code they run unobserved. Importing this module registers a linter that does nothing
unless one of three options is set:

- `trace.CIL.step` logs, for each instruction a proof steps, its pc, instruction and source line,
  the lemma that took it, the hypotheses its step proof used, what it changed and the goals it
  left by obligation tag. Each line is read from the step's proof term: a step a LeanCIL tactic
  took is logged at that tactic, and one taken outside any is logged at its tactic block.
- `cil.diagnostics` logs a `FailureRecord` for each error a LeanCIL tactic raised and for each
  goal one left unsolved, read from the goal it failed or stopped on.
- `cil.goals` logs the goal at each `sorry` written in the source, at each tactic that raised an
  error and each goal a tactic block left unsolved, once each and in source order.

A proof that does not import this module elaborates as if it did not exist; `leancil verify`
imports it only for `--trace`, `--goals` and `--format json`.
-/

namespace CIL.Safety

open Lean Elab Command Meta

initialize registerTraceClass `CIL.step

/-- The text that starts each line of the step trace. -/
def stepTraceHeader : String := "[CIL.step] "

/-! ## Reading goals -/

/-- The parts of a stepping goal: the method it steps, its pc and the reached state, by name. -/
structure SteppingGoal where
  /-- The program the goal runs. -/
  program : Expr
  /-- The index of the method the goal steps. -/
  method : Expr
  /-- The pc it is at, when the goal runs a body rather than invoking one. -/
  pc : Option Expr
  /-- The method's arguments. -/
  args : Expr
  /-- The reached state's parts, by name, in `pcFrameStackMemory` order. -/
  parts : Array (String × Expr)
  /-- The target state of a `LoopReaches` goal, by part. -/
  target : Array (String × Expr) := #[]

/-- The names of a state's parts, in `LoopState.mk` order. -/
def statePartNames : Array String := #["pc", "frame", "stack", "memory"]

/-- The parts of `state` when it reduces to a literal `LoopState`. -/
def loopStateParts (state : Expr) : MetaM (Option (Array (String × Expr))) := do
  let state ← whnf (← instantiateMVars state)
  unless state.isAppOfArity `CIL.Safety.LoopState.mk 4 do return none
  return some (statePartNames.zip state.getAppArgs)

/-- `goal`'s type read as a stepping goal: a loop path, a `run` or `invoke` equation, or a
    `RunRaises` continuation, also as the first conjunct under the existentials of a contract's
    run, as `cil_contract_steps` leaves it. -/
partial def steppingGoal? (type : Expr) : MetaM (Option SteppingGoal) := do
  let type := (← instantiateMVars type).consumeMData
  -- The reached state never mentions the witnesses, so a placeholder stands for each.
  if let some #[_, predicate] := argumentsOf? type ``Exists 2 then
    let .lam _ binder body _ := predicate.consumeMData | return none
    return ← steppingGoal? (body.instantiate1 (← mkFreshExprMVar binder))
  if let some #[left, _] := argumentsOf? type ``And 2 then return ← steppingGoal? left
  if let some #[program, method, arguments, _, state] :=
      argumentsOf? type `CIL.Safety.LoopTerminates 5 then
    let some parts ← loopStateParts state | return none
    return some {
      program, method, pc := parts[0]?.map (·.2)
      args := arguments, parts }
  if let some #[program, method, arguments, state, targetState] :=
      argumentsOf? type `CIL.Safety.LoopReaches 5 then
    let some parts ← loopStateParts state | return none
    let target := (← loopStateParts targetState).getD #[]
    return some {
      program, method, pc := parts[0]?.map (·.2)
      args := arguments, parts, target }
  if let some #[program, method, pc, arguments, frame, stack, memory, _] :=
      argumentsOf? type `CIL.Safety.RunRaises 8 then
    return some {
      program, method, pc := some pc, args := arguments
      parts := statePartNames.zip #[pc, frame, stack, memory] }
  let some (_, current, _) := type.eq? | return none
  let current := current.consumeMData
  if let some #[program, _, method, pc, arguments, frame, stack, memory] :=
      argumentsOf? current `CIL.Safety.run 8 then
    return some {
      program, method, pc := some pc, args := arguments
      parts := statePartNames.zip #[pc, frame, stack, memory] }
  if let some #[program, _, method, arguments, memory] :=
      argumentsOf? current `CIL.Safety.invoke 5 then
    return some {
      program, method, pc := none, args := arguments
      parts := #[("memory", memory)] }
  return none

/-- `value` as a natural number literal, reducing arithmetic on literals. -/
def natLiteral? (value : Expr) : MetaM (Option Nat) := do
  let value ← instantiateMVars value
  if let some literal ← getNatValue? (← whnf value) then return literal
  if value.hasFVar || value.hasMVar then return none
  evalNat value |>.run

/-- The body of method `method` of `program`, by reducing the lookup. -/
def bodyOf? (program method : Expr) : MetaM (Option Expr) := do
  try
    let found ← whnfD (← mkAppM ``GetElem?.getElem? #[program, method])
    let some #[_, body] := argumentsOf? found ``Option.some 2 | return none
    return some body
  catch _ => return none

/-- The instruction at `pc` of `body`, by reducing the lookup. -/
def instructionOf? (body pc : Expr) : MetaM (Option Expr) := do
  try
    let code ← mkAppM `CIL.Method.code #[body]
    let found ← whnfD (← mkAppM ``GetElem?.getElem? #[code, pc])
    let some #[_, instruction] := argumentsOf? found ``Option.some 2 | return none
    return some (← instantiateMVars instruction)
  catch _ => return none

/-- The name a goal goes by in a trace or record: its obligation tag, `path` for the stepping goal
    a tactic continues, or `side condition`. -/
def goalName (goal : MVarId) : MetaM String := do
  let tag := (← goal.getTag).eraseMacroScopes
  if (obligationOf? tag).isSome then return tag.toString
  if (← steppingGoal? (← goal.getType)).isSome then return "path"
  return "side condition"

/-- The hypotheses in scope that state a checked operation's result, `_ = .ok _` or
    `_ = .error _`: the facts a step tactic is passed, read back from the goal it stopped on. -/
def resultFacts : MetaM (Array Expr) := do
  let mut facts := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, _, result) := (← instantiateMVars decl.type).consumeMData.eq? | continue
    if result.isAppOf ``Except.ok || result.isAppOf ``Except.error then
      facts := facts.push decl.toExpr
  return facts

/-- The step goal `step` rewritten as far as the step equations in the proof's environment and
    the result facts in scope go. -/
def residualOf (step : MVarId) : MetaM (Option (Array Expr)) := step.withContext do
  let facts ← resultFacts
  let result ← IO.mkRef none
  discard <| Term.TermElabM.run' <| Tactic.run step do
    result.set (← stepResidual step (← facts.mapM fun fact => Term.exprToSyntax fact))
  result.get

/-! ## Failure records -/

/-- The non-null object references among the literal arguments `args`. -/
def objectArguments (args : Expr) : MetaM (Array Expr) := do
  let some (_, values) := (← instantiateMVars args).listLit? | return #[]
  return values.toArray.filterMap fun value =>
    match argumentsOf? value.consumeMData `CIL.Safety.Value.object 1 with
    | some #[reference] =>
      if reference.consumeMData.isAppOf `CIL.Safety.ManagedReference.address then
        some reference else none
    | _ => none

/-- The record of a failure or stop of `tactic` on `goal`, handed `handed`: the reached state,
    the instruction there and what its step lacks. -/
def analyze (tactic : String) (goal : MVarId) (handed : Option MVarId) (error : Option Position)
    (stopped : Bool) : MetaM FailureRecord := goal.withContext do
  let obligation ← match handed with
    | some handed => do
      let tag := (← handed.getTag).eraseMacroScopes
      pure ((obligationOf? tag).map fun _ => tag)
    | none => pure none
  let base : FailureRecord := { tactic, error, stopped, obligation }
  let type ← instantiateMVars (← goal.getType)
  let sideCondition := "the goal is a side condition, not a step of a method"
  let some stepping ← steppingGoal? type
    | -- A side condition that names a checked operation, as an unfolded step does, lacks its fact.
      let record := { base with
        residual := #[type]
        unknown := #[("method", sideCondition), ("pc", sideCondition),
          ("instruction", sideCondition)] }
      match missingFactOf #[type] with
      | .frameOrStore =>
        let unknown := record.unknown.push
          ("missing", "the goal is a side condition: the residual is the goal itself")
        return { record with unknown }
      | fact => return { record with
          missing := fact.name, suggestions := #[m!"supply {missingFactHint #[type]}"] }
  let method ← natLiteral? stepping.method
  let record := { base with method, reached := stepping.parts }
  let entered := "the goal invokes the method; no instruction of it has run"
  let some pcTerm := stepping.pc
    | -- The entry checks each argument, and an object argument forms only from a fact about it.
      let objects ← objectArguments stepping.args
      let some memory := stepping.parts.find? (·.1 == "memory") | return record
      if objects.isEmpty then
        return { record with
          unknown := #[("pc", entered), ("instruction", entered), ("missing", entered)] }
      return { record with
        missing := MissingFact.objectForm.name,
        residual := ← objects.mapM (mkAppM `CIL.Safety.formObject #[memory.2, ·])
        suggestions := #[m!"supply, for each object argument, {MissingFact.objectForm.hint}"],
        unknown := #[("pc", entered), ("instruction", entered)] }
  let some pc ← natLiteral? pcTerm
    | return { record with
        missing := some "branchCondition",
        suggestions := #[m!"supply a fact deciding the branch condition"],
        unknown := #[("pc", "the pc is not a literal: a branch was not decided"),
          ("instruction", "the pc is not a literal: a branch was not decided")] }
  let record := { record with pc }
  -- At the target's pc, a walk that stopped differs from the target in some part.
  if let some targetPc := stepping.target[0]? then
    if (← natLiteral? targetPc.2) == some pc then
      let mut expected := #[]
      for (reached, target) in stepping.parts.zip stepping.target do
        unless ← withNewMCtxDepth (isDefEq reached.2 target.2) do expected := expected.push target
      return { record with
        reached := stepping.parts.filter fun part => expected.any (·.1 == part.1),
        expected, missing := some "targetState",
        suggestions := #[m!"state a fact in the reached form, or state the target in it"],
        unknown := #[
          ("instruction", "the walk is at the target's pc, so it steps no instruction")] }
  let some body ← bodyOf? stepping.program stepping.method
    | return { record with
        missing := some "instructionLookup",
        unknown := #[("instruction", "the method lookup does not reduce")] }
  let some op ← instructionOf? body pcTerm
    | return { record with
        missing := some "instructionLookup",
        unknown := #[("instruction", "the instruction lookup does not reduce")] }
  let record := { record with instruction := op }
  let calling := tactic.endsWith "_call"
  -- A receiver-checked call crosses into its callee as a direct call does.
  let isCall := (← whnfR op).isAppOf ``CIL.Instruction.call ||
    (← whnfR op).isAppOf ``CIL.Instruction.callInstance
  if isCall && !calling then
    return { record with
      missing := some "calleeContract",
      suggestions := #[m!"cross the call with the call tactic of its stepping family and the \
        callee's contract"] }
  if calling && !isCall then
    return { record with
      missing := some "callSite",
      suggestions := #[m!"step to the call first"] }
  let some frame := stepping.parts.find? (·.1 == "frame") | return record
  let some stack := stepping.parts.find? (·.1 == "stack") | return record
  let some memory := stepping.parts.find? (·.1 == "memory") | return record
  let stepTerm ← mkAppM `CIL.Safety.step #[body, op, pcTerm, stepping.args, frame.2, stack.2,
    memory.2]
  let resultType ← inferType stepTerm
  let step ← mkFreshExprMVar (← mkEq stepTerm (← mkFreshExprMVar resultType))
  let .mvar stepGoal := step
    | throwError "analyze: expected a fresh metavariable, but found{indentExpr step}"
  let residual := (← residualOf stepGoal).getD #[← instantiateMVars (← inferType step)]
  let missing := missingFactOf residual
  return { record with
    missing := missing.name, residual,
    suggestions := #[m!"supply {missingFactHint residual}"] }

/-! ## The step trace -/

/-- What a hypothesis's statement head says, for the facts a trace explains. A name here is
    checked against the environment by `Tests.Observe`. -/
def factMeanings : List (Name × String) := [
  (`CIL.Safety.SpanApart, "the footprints are disjoint"),
  (`CIL.Safety.Writable, "the range is writable"),
  (`CIL.Safety.Filled, "the buffer's contents are known"),
  (`CIL.Safety.CheckedSpan, "the span is valid at this memory")]

/-- The source line of `pc` in `method` from `ExtractedSymbols`, or why there is none. -/
def sourceOf (method pc : Option Nat) : MetaM String := do
  let (some method, some pc) := (method, pc) | return "unknown, since the pc is not a literal"
  match ← CIL.DebugNames.entries CIL.DebugNames.Point `points method with
  | none => return "unknown, since the proof does not import ExtractedSymbols"
  | some _ =>
    let found ← CIL.DebugNames.location? method pc
    return found.getD "unknown, since no sequence point precedes this pc"

/-- The parts of a state, named by `names`, that differ between `before` and `after`; a literal
    list part is compared entry by entry. -/
def stateChanges (before after : Array (String × Expr)) : MetaM (Array MessageData) := do
  let mut changes := #[]
  for ((name, old), (_, new)) in before.zip after do
    let old ← instantiateMVars old
    let new ← instantiateMVars new
    if old == new then continue
    match old.listLit?, new.listLit? with
    | some (_, olds), some (_, news) =>
      let (olds, news) := (olds.toArray, news.toArray)
      if olds.size == news.size then
        for slot in [:olds.size] do
          let (some oldEntry, some newEntry) := (olds[slot]?, news[slot]?) | continue
          unless oldEntry == newEntry do
            changes := changes.push m!"{name} {slot}: {oldEntry} ⟶ {newEntry}"
      else changes := changes.push m!"{name}: {old} ⟶ {new}"
    | _, _ => changes := changes.push m!"{name}: {old} ⟶ {new}"
  return changes

/-- What a step's result does to the state `before`: the parts it changed, or the return, call
    or fault it ends in. -/
def resultChanges (before : Array (String × Expr)) (result : Expr) :
    MetaM (Array MessageData) := do
  let result ← whnfR (← instantiateMVars result)
  if let some #[_, _, fault] := argumentsOf? result ``Except.error 3 then
    return #[m!"faults: {fault}"]
  -- A step stated with an unknown result, as an existential step does, changes nothing it names.
  let some #[_, _, value] := argumentsOf? result ``Except.ok 3 | return #[]
  let action ← whnfR value
  let args := action.getAppArgs
  if let some #[pc, stack, frame, memory] :=
      argumentsOf? action `CIL.Safety.FrameAction.next 4 then
    return ← stateChanges before (statePartNames.zip #[pc, frame, stack, memory])
  if let some #[returned, _] := argumentsOf? action `CIL.Safety.FrameAction.returned 2 then
    return #[m!"returns {returned}"]
  if action.isAppOf `CIL.Safety.FrameAction.call || action.isAppOf `CIL.Safety.FrameAction.tailCall
      || action.isAppOf `CIL.Safety.FrameAction.construct then
    if let (some callee, some arguments) := (args[0]?, args[1]?) then
      return #[m!"calls method {callee} with {arguments}"]
  return #[m!"ends in {action}"]

/-- A step found in a proof term: its tactic-independent key and its trace text. -/
structure TracedStep where
  /-- The goal whose assignment holds the step, and the step's position in it. -/
  key : MVarId × Nat
  /-- The trace text, in the step's context. -/
  text : MessageData

/-- The state of a walk over a proof term: the goals it visited and the steps it found. -/
structure StepWalk where
  /-- The goals whose assignments the walk has read. -/
  visited : Std.HashSet MVarId := {}
  /-- The steps found, in proof order. -/
  steps : Array TracedStep := #[]
  /-- The step count found so far in each goal's assignment. -/
  counts : Std.HashMap MVarId Nat := {}
  /-- The constants whose type mentions `step`, by whether it does. -/
  stepping : Std.HashMap Name Bool := {}

/-- The monad of a walk over a proof term. -/
abbrev StepWalkM := StateRefT StepWalk MetaM

/-- Whether constant `name`'s statement mentions `CIL.Safety.step`, so its applications may take
    a step. -/
def mentionsStep (name : Name) : StepWalkM Bool := do
  if let some known := (← get).stepping[name]? then return known
  let mentions := match (← getEnv).find? name with
    | some info => (info.type.find? (·.isConstOf `CIL.Safety.step)).isSome
    | none => false
  modify fun walk => { walk with stepping := walk.stepping.insert name mentions }
  return mentions

/-- The trace text of the step `proof` proves, taken by `lemma` with `siblings` as its other
    arguments: the step equation's pc, instruction, source, used facts, changes and the goals
    the application left. -/
def stepText (lemma : MessageData) (proof : Expr) (equation : Expr) (siblings : Array Expr) :
    MetaM MessageData := do
  let some (_, current, result) := equation.eq? | return m!""
  let #[body, op, pcTerm, _, frame, stack, memory] := current.getAppArgs | return m!""
  let pc ← natLiteral? pcTerm
  -- The method is the index whose lookup gave the step's body.
  let mut method : Option Nat := none
  for sibling in siblings do
    let some (_, lookup, found) := (← instantiateMVars (← inferType sibling)).consumeMData.eq?
      | continue
    let some candidate := lastArgument? found | continue
    if lookup.isAppOf ``GetElem?.getElem? && found.isAppOf ``Option.some &&
        (← isDefEq candidate body) then
      let some index := lastArgument? lookup | continue
      method ← natLiteral? index
  let before := statePartNames.zip #[pcTerm, frame, stack, memory]
  let mut used := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless ← isProp decl.type do continue
    unless proof.containsFVar decl.fvarId do continue
    let statement ← instantiateMVars decl.type
    let meaning := statement.consumeMData.getAppFn.constName?.bind (factMeanings.lookup ·)
    used := used.push m!"\n  used {mkFVar decl.fvarId} : {statement}\
      {(meaning.map (s!" ({·})")).getD ""}"
  let changes ← resultChanges before result
  let changed := if changes.isEmpty then m!"\n  changes nothing"
    else MessageData.joinSep (changes.toList.map (m!"\n  changes {·}")) ""
  let mut left := #[]
  for sibling in siblings do
    if let .mvar goal := (← instantiateMVars sibling) then
      unless ← goal.isAssigned do left := left.push (← goalName goal)
  let leaves := if left.isEmpty then m!"" else m!"\n  leaves: {", ".intercalate left.toList}"
  let via := proof.getAppFn.constName?.filter (·.getRoot == `CIL)
  let lemmaText := match via with
    | some via => m!"{lemma}, its step by {MessageData.ofConstName via}"
    | none => m!"{lemma}"
  addMessageContext m!"{stepTraceHeader}pc {(pc.map toString).getD "?"}: {← instantiateMVars op}\
    \n  source: {← sourceOf method pc}\n  by {lemmaText}{MessageData.joinSep used.toList ""}\
    {changed}{leaves}"

mutual
  /-- Walk the assignment of `goal`, unless already walked. -/
  partial def walkGoal (goal : MVarId) : StepWalkM Unit := do
    if (← get).visited.contains goal then return
    modify fun walk => { walk with visited := walk.visited.insert goal }
    if let some value ← getExprMVarAssignment? goal then
      let decl ← goal.getDecl
      withLCtx decl.lctx decl.localInstances (walkTerm goal value)
    else if let some delayed ← getDelayedMVarAssignment? goal then
      walkGoal delayed.mvarIdPending

  /-- Walk `term`, part of `owner`'s assignment, recording each step an application takes. -/
  partial def walkTerm (owner : MVarId) (term : Expr) : StepWalkM Unit := do
    match term with
    | .mvar goal => walkGoal goal
    | .mdata _ body => walkTerm owner body
    | .proj _ _ body => walkTerm owner body
    | .lam name type body info =>
      withLocalDecl name info type fun bound => walkTerm owner (body.instantiate1 bound)
    | .letE name type value body _ =>
      walkTerm owner value
      withLetDecl name type value fun bound => walkTerm owner (body.instantiate1 bound)
    | .app .. =>
      let head := term.getAppFn
      let args := term.getAppArgs
      if let .mvar goal := head then walkGoal goal
      if let some name := head.constName? then
        if ← mentionsStep name then
          for arg in args do
            let equation ← try instantiateMVars (← inferType arg) catch _ => continue
            let equation := equation.consumeMData
            let some (_, current, _) := equation.eq? | continue
            unless current.isAppOfArity `CIL.Safety.step 7 do continue
            let index := (← get).counts.getD owner 0
            let text ← stepText (.ofConstName name) arg equation args
            modify fun walk => { walk with
              counts := walk.counts.insert owner (index + 1),
              steps := walk.steps.push { key := (owner, index), text } }
      for arg in args do walkTerm owner arg
    | _ => pure ()
end

/-! ## The linter -/

/-- A tactic node of a command's info trees, with its context. -/
structure TacticNode where
  /-- The node's context. -/
  context : ContextInfo
  /-- The tactic's info. -/
  info : TacticInfo

/-- The LeanCIL tactic `stx` runs, by its own first atom, whether written in the source or built by
    another tactic's expansion. -/
def cilTactic? (stx : Syntax) : Option String :=
  -- A tactic sequence starts with its first tactic's atom, but is not that tactic.
  match stx[0] with
  | .atom _ value =>
    let value := String.ofList (value.toList.filter (· != ' '))
    if value.startsWith "cil_" then some value else none
  | _ => none

/-- Whether `stx` is written in the source rather than built by a macro or tactic. -/
def writtenInSource (stx : Syntax) : Bool :=
  match stx.getHeadInfo with
  | .original .. => true
  | _ => false

/-- The source range of `stx`, when it has one. -/
def sourceRange? (stx : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) := do
  let start ← stx.getPos?
  let stop ← stx.getTailPos?
  return (start, stop)

/-- Whether `position` lies in the source range of `stx`. -/
def inSource (stx : Syntax) (position : String.Pos.Raw) : Bool :=
  (sourceRange? stx).any fun (start, stop) => start ≤ position && position ≤ stop

/-- The LeanCIL tactic `stx` written in the source runs, by its first atom: none for
    syntax a tactic built. -/
def userTactic? (stx : Syntax) : Option String :=
  if writtenInSource stx then cilTactic? stx else none

/-- The tactic nodes of an info tree, in elaboration order. -/
structure TacticNodes where
  /-- The outermost tactic nodes, each a tactic block. -/
  blocks : Array TacticNode := #[]
  /-- The tactic nodes written in the source. -/
  written : Array TacticNode := #[]
  /-- Every LeanCIL tactic node, including those another tactic's expansion built. -/
  raisers : Array TacticNode := #[]
  deriving Inhabited

/-- The LeanCIL tactic nodes written in the source. -/
def TacticNodes.tactics (nodes : TacticNodes) : Array TacticNode :=
  nodes.written.filter fun node => (cilTactic? node.info.stx).isSome

instance : Append TacticNodes where
  append first second :=
    { blocks := first.blocks ++ second.blocks, written := first.written ++ second.written
      raisers := first.raisers ++ second.raisers }

/-- The tactic nodes of `tree`. -/
partial def tacticNodes (tree : InfoTree) (context : Option ContextInfo := none)
    (inBlock : Bool := false) : TacticNodes :=
  match tree with
  | .context part inner => tacticNodes inner (part.mergeIntoOuter? context) inBlock
  | .hole _ => {}
  | .node info children =>
    let (found, inBlock) : TacticNodes × Bool := match info, context with
      | .ofTacticInfo tactic, some context =>
        let node := { context, info := tactic }
        ({ blocks := if inBlock then #[] else #[node]
           written := if writtenInSource tactic.stx then #[node] else #[]
           raisers := if (cilTactic? tactic.stx).isSome then #[node] else #[] }, true)
      | _, _ => ({}, inBlock)
    children.foldl (init := found) fun found child => found ++ tacticNodes child context inBlock

/-- Run `action` in `node`'s context after the tactic ran. -/
def TacticNode.run (node : TacticNode) (action : MetaM α) : IO α :=
  { node.context with mctx := node.info.mctxAfter }.runMetaM {} action

/-- Whether `goal` is declared in the final metavariable context of one of `blocks`. Lean may
    elaborate a term more than once and keep the tactic nodes of each attempt, but it rolls back the
    metavariables of each attempt it discards. -/
def kept (blocks : Array TacticNode) (goal : MVarId) : Bool :=
  blocks.any fun block => (block.info.mctxAfter.findDecl? goal).isSome

/-- Log the steps of each LeanCIL tactic node, and then those of each tactic block that no LeanCIL
    tactic took. -/
def logSteps (blocks tactics : Array TacticNode) : CommandElabM Unit := do
  let mut seen : Std.HashSet (MVarId × Nat) := {}
  for node in tactics do
    let steps ← node.run do
      let ((), walk) ← (node.info.goalsBefore.forM walkGoal).run {}
      let left ← node.info.goalsAfter.mapM goalName
      return (walk.steps, left)
    let (steps, left) := steps
    for step in steps do
      seen := seen.insert step.key
      logInfoAt node.info.stx step.text
    let tactic := (userTactic? node.info.stx).getD "?"
    logInfoAt node.info.stx m!"{stepTraceHeader}{tactic} took {steps.size} steps; goals left: \
      {if left.isEmpty then "none" else ", ".intercalate left}"
  for block in blocks do
    let (steps, statesRun) ← block.run do
      let ((), walk) ← (block.info.goalsBefore.forM walkGoal).run {}
      let some goal := block.info.goalsBefore.head? | return (walk.steps, false)
      let type ← instantiateMVars (← goal.getType)
      return (walk.steps, (type.find? fun part =>
        part.isConstOf `CIL.Safety.invoke || part.isConstOf `CIL.Safety.run).isSome)
    for step in steps do
      unless seen.contains step.key do
        logInfoAt block.info.stx m!"{step.text}\n  taken outside a LeanCIL tactic"
    -- A proof by evaluation, such as `rfl` or `decide` on a run, takes no step the trace can show.
    if steps.isEmpty && statesRun then
      logInfoAt block.info.stx m!"{stepTraceHeader}this proof states a run of a method but \
        applies no step lemma, so the trace shows no step of it"

/-- The LeanCIL tactic nodes of a rerun of `node`, a macro, from the state before it ran, with
    its expansion evaluated directly: Lean drops the nodes of a failed expansion, including the
    goals the tactic inside it failed on, but keeps those of a tactic that fails on its own. -/
def rerunExpansion (node : TacticNode) : IO (Array TacticNode) := do
  let some goal := node.info.goalsBefore.head? | return #[]
  let trees ← { node.context with mctx := node.info.mctxBefore }.runMetaM {} do
    Term.TermElabM.run' do
      modifyInfoState fun state => { state with enabled := true, trees := {} }
      try
        discard <| Tactic.run goal do
          let some expanded ← liftMacroM (expandMacro? node.info.stx) | return
          Tactic.evalTactic expanded
      catch _ => pure ()
      return (← getInfoState).trees
  return trees.foldl (init := #[]) fun found tree =>
    found ++ (tacticNodes tree (some node.context) true).raisers

/-- The text of `message`. -/
def messageText (message : Message) : IO String := message.data.toString

/-- The errors logged so far. -/
def loggedErrors : CommandElabM (Array Message) := do
  let log := (← get).messages
  return (log.reported.toArray ++ log.unreported.toArray).filter (·.severity == .error)

/-- Whether `text` is Lean's error for the goals a tactic block leaves open. -/
def reportsUnsolvedGoals (text : String) : Bool := text.startsWith "unsolved goals"

/-- Log a failure record for each of `errors` a LeanCIL tactic raised, and for each goal a tactic
    block leaves unsolved after a LeanCIL tactic left it. -/
def logRecords (blocks tactics raisers : Array TacticNode) (errors : Array Message) :
    CommandElabM Unit := do
  let fileMap ← getFileMap
  for error in errors do
    -- A tactic's own error is reported where its syntax starts, so an error inside a term it
    -- elaborates is Lean's; a LeanCIL error names the tactic that raised it.
    let text ← messageText error
    let raised := raisers.filter fun node =>
      (node.info.stx.getPos?.map (fileMap.toPosition · == error.pos)).getD false
    let named := raised.filter fun node =>
      (cilTactic? node.info.stx).any fun name => text.startsWith s!"{name}:"
    let some outer := named.back? <|> raised.back? | continue
    -- The LeanCIL tactic the error names, which may run inside the expansion of `outer`.
    let name? := (text.splitOn ":")[0]?.filter fun name =>
      name.startsWith "cil_" && !name.contains ' '
    let inner ← match name?, named.isEmpty with
      | some name, true => do
        let rerun ← rerunExpansion outer
        pure (rerun.filter (cilTactic? ·.info.stx == some name)).back?
      | _, _ => pure none
    let node := inner.getD outer
    let some goal := node.info.goalsAfter.head? | continue
    let tactic := (cilTactic? node.info.stx).getD "?"
    let line ← node.run <| goal.withContext do
      (← analyze tactic goal node.info.goalsBefore.head? error.pos false).render
    logInfoAt node.info.stx m!"{failureMarker}{line}"
  for block in blocks do
    let unsolved := block.info.goalsAfter
    if unsolved.isEmpty then continue
    -- Lean reports the goals a block leaves at the block, so the record names that error.
    let reported ← errors.filterM fun error => do
      return reportsUnsolvedGoals (← messageText error) &&
        match block.info.stx.getPos? with
        | some start => fileMap.ofPosition error.pos ≤ start
        | none => false
    -- A block that raised an error keeps its goals but reports none of them as left open.
    let some errorAt := reported.back?.map (·.pos) | continue
    for goal in unsolved do
      let stoppers := tactics.filter (·.info.goalsAfter.contains goal)
      let some node := stoppers.back? | continue
      let tactic := (userTactic? node.info.stx).getD "?"
      let line ← block.run <| goal.withContext do
        (← analyze tactic goal node.info.goalsBefore.head? (some errorAt) true).render
      logInfoAt node.info.stx m!"{failureMarker}{line}"

/-! ## Open goals -/

/-- Whether the observer logs the goal at each `sorry` and each failing tactic of a proof. -/
register_option cil.goals : Bool := {
  defValue := false
  descr := "log the goal at each `sorry`, each failing tactic and each unsolved goal"
}

/-- The text that starts each goal the observer logs under `cil.goals`. -/
def goalMarker : String := "[LeanCIL goal v1] "

/-- Why a goal is open: a `sorry` stands for its proof, the tactic at it raised an error, or its
    tactic block ended without proving it. The marker's line names it by these words. -/
inductive OpenGoalKind where
  | hole
  | failed
  | unsolved

/-- The word naming `kind` after `goalMarker`. -/
def OpenGoalKind.word : OpenGoalKind → String
  | .hole => "sorry"
  | .failed => "error"
  | .unsolved => "unsolved"

/-- A goal a command leaves open, at the source range it is reported for. -/
structure OpenGoal where
  /-- Where the range starts. -/
  start : String.Pos.Raw
  /-- Where the range stops. -/
  stop : String.Pos.Raw
  /-- Why the goal is open. -/
  kind : OpenGoalKind
  /-- The goal: its case tag, hypotheses and target, as Lean prints a goal. -/
  text : Format

/-- The syntax kinds of the tactics that close a goal with `sorry`. -/
def sorryTacticKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Tactic.tacticSorry, ``Lean.Parser.Tactic.tacticAdmit]

/-- The goal of each `sorry` term and tactic written in the source of `tree`, in elaboration
    order: the goal a tactic `sorry` closes, or the type a term `sorry` stands for under the
    hypotheses in scope. Lean may elaborate a `sorry` more than once; each attempt is listed. -/
def sorryGoals (tree : InfoTree) : IO (Array OpenGoal) := do
  let nodes := tree.foldInfo (init := #[]) fun context info found => found.push (context, info)
  let mut goals := #[]
  for (context, info) in nodes do
    unless writtenInSource info.stx do continue
    let some (start, stop) := sourceRange? info.stx | continue
    match info with
    | .ofTacticInfo tactic =>
      unless sorryTacticKinds.contains tactic.stx.getKind do continue
      let some goal := tactic.goalsBefore.head? | continue
      let text ← { context with mctx := tactic.mctxBefore }.runMetaM {} (Meta.ppGoal goal)
      goals := goals.push { start, stop, kind := .hole, text }
    | .ofTermInfo term =>
      unless term.stx.getKind == ``Lean.Parser.Term.sorry do continue
      let some type := term.expectedType? | continue
      let text ← context.runMetaM term.lctx do
        let hole ← mkFreshExprMVar (← instantiateMVars type)
        let .mvar holeGoal := hole
          | throwError "sorryGoals: expected a fresh metavariable, but found{indentExpr hole}"
        Meta.ppGoal holeGoal
      goals := goals.push { start, stop, kind := .hole, text }
    | _ => pure ()
  return goals

/-- The goals of an `unsolved goals` error, as its text lists them: one per blank-line-separated
    part after the first line. -/
def unsolvedGoalTexts (text : String) : List String :=
  ((text.splitOn "\n").drop 1 |> "\n".intercalate).splitOn "\n\n"
    |>.map (·.trimAscii.toString) |>.filter (· != "")

/-- Log, under `goalMarker`, the goal at each `sorry` of `command`, the goal before each of its
    `tactics`, written in the source, that raised one of `errors`, and each goal a tactic block
    left unsolved, once each in source order. -/
def logGoals (command : Syntax) (tactics : Array TacticNode) (errors : Array Message) :
    CommandElabM Unit := do
  let within := inSource command
  let fileMap ← getFileMap
  -- Keyed by where each goal starts and its index there; a later attempt replaces an earlier one.
  let mut found : Std.HashMap (Nat × Nat) OpenGoal := {}
  for tree in (← get).infoState.trees do
    for goal in ← sorryGoals tree do
      if within goal.start then found := found.insert (goal.start.byteIdx, 0) goal
  for error in errors do
    let start := fileMap.ofPosition error.pos
    unless within start do continue
    let text ← messageText error
    if reportsUnsolvedGoals text then
      let stop := (error.endPos.map fileMap.ofPosition).getD start
      for goal in unsolvedGoalTexts text, index in List.range (unsolvedGoalTexts text).length do
        found := found.insert (start.byteIdx, index + 1)
          { start, stop, kind := .unsolved, text := Format.text goal }
      continue
    -- Attribute an error to the innermost tactic that raised it.
    let mut raiser : Option (TacticNode × String.Pos.Raw × String.Pos.Raw) := none
    for node in tactics do
      let some (nodeStart, nodeStop) := sourceRange? node.info.stx | continue
      unless nodeStart ≤ start && start ≤ nodeStop do continue
      let inner := match raiser with
        | some (_, outerStart, outerStop) =>
          outerStart < nodeStart || (outerStart == nodeStart && nodeStop ≤ outerStop)
        | none => true
      if inner then raiser := some (node, nodeStart, nodeStop)
    let some (node, nodeStart, nodeStop) := raiser | continue
    if found.contains (nodeStart.byteIdx, 0) then continue
    let some goal := node.info.goalsBefore.head? | continue
    let text ← { node.context with mctx := node.info.mctxBefore }.runMetaM {} (Meta.ppGoal goal)
    found := found.insert (nodeStart.byteIdx, 0)
      { start := nodeStart, stop := nodeStop, kind := .failed, text }
  let ordered := found.toArray.qsort fun first second =>
    first.1.1 < second.1.1 || (first.1.1 == second.1.1 && first.1.2 < second.1.2)
  for (_, goal) in ordered do
    let range := Syntax.atom (.synthetic goal.start goal.stop) ""
    logInfoAt range m!"{goalMarker}{goal.kind.word}\n{goal.text}"

/-- After each command, the step trace under `trace.CIL.step`, the failure records under
    `cil.diagnostics` and the open goals under `cil.goals`; nothing when none is set. -/
def observer : Linter where
  name := `CIL.Safety.observer
  run := withSetOptionIn fun command => do
    let options ← getOptions
    let tracing := options.getBool `trace.CIL.step
    let recording := cil.diagnostics.get options
    let showingGoals := cil.goals.get options
    unless tracing || recording || showingGoals do return
    let nodes := (← get).infoState.trees.foldl (init := ({} : TacticNodes)) fun found tree =>
      found ++ tacticNodes tree
    let errors ← loggedErrors
    -- Only the nodes of this command: a tree may hold earlier commands' nodes.
    let inCommand (node : TacticNode) : Bool := node.info.stx.getPos?.any (inSource command)
    if showingGoals then logGoals command (nodes.written.filter inCommand) errors
    unless tracing || recording do return
    let ownBlocks := nodes.blocks.filter inCommand
    -- Each node once, as the info trees may hold a node twice; with `live`, only the nodes of the
    -- elaboration Lean kept. A failed tactic's state is rolled back but its error is not, so the
    -- tactics an error may come from are not filtered by liveness.
    let ran (nodes : Array TacticNode) (live : Bool := true) : Array TacticNode := Id.run do
      let mut seen : Std.HashSet (Array MVarId × Option Nat × Name) := {}
      let mut found := #[]
      for node in nodes.filter inCommand do
        if live && !node.info.goalsBefore.all (kept ownBlocks) then continue
        -- A macro and the tactic it expands to share goals and position, but not their kind.
        let key := (node.info.goalsBefore.toArray, node.info.stx.getPos?.map (·.byteIdx),
          node.info.stx.getKind)
        if seen.contains key then continue
        seen := seen.insert key
        found := found.push node
      return found
    let ownTactics := ran nodes.tactics
    if tracing then logSteps ownBlocks ownTactics
    if recording then logRecords ownBlocks ownTactics (ran nodes.raisers (live := false)) errors

initialize addLinter observer

end CIL.Safety
