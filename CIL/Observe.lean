import Lean
import Lean.Linter.Basic
import CIL.DebugNames
import CIL.Safety.FailureRecords

/-!
# Observing LeanCIL tactics

What each LeanCIL tactic did, read after each command from its info trees, so the tactics run
exactly the code they run unobserved. Importing this module registers a linter that does nothing
unless one of two options is set:

- `trace.CIL.step` logs, for each instruction a proof steps, its pc, instruction and source line,
  the lemma that took it, the hypotheses its step proof used, what it changed and the goals it
  left by obligation tag. Each line is read from the step's proof term: a step a LeanCIL tactic
  took is logged at that tactic, and one taken outside any is logged at its tactic block.
- `cil.diagnostics` logs a `FailureRecord` for each error a LeanCIL tactic raised and for each
  goal one left unsolved, read from the goal it failed or stopped on.

A proof that does not import this module elaborates as if it did not exist; `leancil verify`
imports it only for `--trace` and `--format json`.
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
    `RunRaises` continuation. -/
def steppingGoal? (type : Expr) : MetaM (Option SteppingGoal) := do
  let type := (← instantiateMVars type).consumeMData
  if type.isAppOfArity `CIL.Safety.LoopTerminates 5 then
    let some parts ← loopStateParts (type.getArg! 4) | return none
    return some {
      program := type.getArg! 0, method := type.getArg! 1, pc := (parts[0]!).2
      args := type.getArg! 2, parts }
  if type.isAppOfArity `CIL.Safety.LoopReaches 5 then
    let some parts ← loopStateParts (type.getArg! 3) | return none
    let target := (← loopStateParts (type.getArg! 4)).getD #[]
    return some {
      program := type.getArg! 0, method := type.getArg! 1, pc := (parts[0]!).2
      args := type.getArg! 2, parts, target }
  if type.isAppOfArity `CIL.Safety.RunRaises 8 then
    let args := type.getAppArgs
    return some {
      program := args[0]!, method := args[1]!, pc := args[2]!, args := args[3]!
      parts := statePartNames.zip #[args[2]!, args[4]!, args[5]!, args[6]!] }
  let some (_, current, _) := type.eq? | return none
  let current := current.consumeMData
  if current.isAppOfArity `CIL.Safety.run 8 then
    let args := current.getAppArgs
    return some {
      program := args[0]!, method := args[2]!, pc := args[3]!, args := args[4]!
      parts := statePartNames.zip #[args[3]!, args[5]!, args[6]!, args[7]!] }
  if current.isAppOfArity `CIL.Safety.invoke 5 then
    let args := current.getAppArgs
    return some {
      program := args[0]!, method := args[2]!, pc := none, args := args[3]!
      parts := #[("memory", args[4]!)] }
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
    unless found.isAppOfArity ``Option.some 2 do return none
    return some found.appArg!
  catch _ => return none

/-- The instruction at `pc` of `body`, by reducing the lookup. -/
def instructionOf? (body pc : Expr) : MetaM (Option Expr) := do
  try
    let code ← mkAppM `CIL.Method.code #[body]
    let found ← whnfD (← mkAppM ``GetElem?.getElem? #[code, pc])
    unless found.isAppOfArity ``Option.some 2 do return none
    return some (← instantiateMVars found.appArg!)
  catch _ => return none

/-- The name a goal goes by in a trace or record: its obligation tag, `path` for the stepping goal
    a tactic continues, or `side condition`. -/
def goalName (goal : MVarId) : MetaM String := do
  let tag := (← goal.getTag).eraseMacroScopes
  if (obligationOf? tag).isSome then return tag.toString
  if (← steppingGoal? (← goal.getType)).isSome then return "path"
  return "side condition"

/-! ## The facts a missing step needs -/

/-- The kind of fact a stuck step lacks, read from the terms its residual mentions. -/
inductive MissingFact where
  /-- A span's validity at the step's memory. -/
  | spanValidity
  /-- A span slice. -/
  | spanSlice
  /-- A span element's address. -/
  | spanElement
  /-- An `Unsafe.Add` result. -/
  | unsafeAdd
  /-- That a reference forms. -/
  | referenceForm
  /-- What a load reads. -/
  | load
  /-- The step equation of a store. -/
  | storeStep
  /-- A local's frame fact, or a store's step equation, when the residual names neither. -/
  | frameOrStore

/-- The stable name of a missing fact's kind, as failure records report it. -/
def MissingFact.name : MissingFact → String
  | .spanValidity => "spanValidity"
  | .spanSlice => "spanSlice"
  | .spanElement => "spanElement"
  | .unsafeAdd => "unsafeAdd"
  | .referenceForm => "referenceForm"
  | .load => "load"
  | .storeStep => "storeStep"
  | .frameOrStore => "frameOrStore"

/-- What to supply for a missing fact of this kind, as `loopMissingHint` words it. -/
def MissingFact.hint : MissingFact → MessageData
  | .spanValidity => m!"the span's validity at this memory: a `CheckedSpan` of the caller's \
      memory, which the loop tactics read in every frame memory, or \
      `view.validate memory = .ok ()`"
  | .spanSlice => m!"the slice: `view.slice memory start length = .ok sliced`, such as from \
      `CheckedSpan.tail` at the caller's memory"
  | .spanElement => m!"the element's address: `view.element memory index = .ok item`, such as \
      from `CheckedSpan.head`"
  | .unsafeAdd => m!"the `Unsafe.Add` result: `add memory base width offset = .ok reference` at \
      this memory or the caller's, such as `Writable.add_int`"
  | .referenceForm => m!"that the reference forms: `form memory reference = .ok reference`, or \
      an `access` or `add` fact it follows from, at this memory or the caller's"
  | .load => m!"what the load reads: a `loadValue` fact at this memory, such as from \
      `(span.within wellFormed frame).head`"
  | .storeStep => m!"the step equation of a store with this stack"
  | .frameOrStore => m!"a `LoopFrame` at this memory for a local, or the step equation of a \
      store with this stack"

/-- The constants whose mention in a step's residual decides its `MissingFact`, in the order
    `loopMissingHint` tests them. A name here is checked against the environment by
    `Tests.Observe`. -/
def missingFactMentions : List (MissingFact × List Name) := [
  (.spanValidity, [`CIL.Safety.SpanView.validate]),
  (.spanSlice, [`CIL.Safety.SpanView.slice]),
  (.spanElement, [`CIL.Safety.SpanView.element]),
  (.unsafeAdd, [`CIL.Safety.add]),
  (.referenceForm, [`CIL.Safety.form, `CIL.Safety.formValue]),
  (.load, [`CIL.Safety.loadValue, `CIL.Safety.read]),
  (.storeStep, [`CIL.Safety.storeLocal, `CIL.Safety.storeValue, `CIL.Safety.write])]

/-- The kind of fact a stuck step needs, from the residual of that step: the same reading as
    `loopMissingHint`, which words the error the loop tactics raise. -/
def missingFactOf (residual : Array Expr) : MissingFact :=
  let mentions (name : Name) : Bool :=
    residual.any fun goal => (goal.find? fun term => term.isConstOf name).isSome
  let spanLocal := residual.any fun goal => (goal.find? fun term =>
    term.isAppOf `CIL.Safety.loadLocal && term.getAppNumArgs >= 2 &&
      (term.getArg! 1).isAppOf `CIL.Safety.LocalSlot.span).isSome
  if spanLocal then .spanValidity
  else match missingFactMentions.find? (·.2.any mentions) with
    | some (fact, _) => fact
    | none => .frameOrStore

/-- `CIL.Safety.loopStepResidual`, when the proof's environment has it: the step goal rewritten
    as far as the step equations go. -/
unsafe def stepResidualImpl (step : MVarId) : MetaM (Option (Array Expr)) := do
  let name := `CIL.Safety.loopStepResidual
  unless (← getEnv).contains name do return none
  let residual ←
    evalConst (MVarId → Array Syntax.Term → Tactic.TacticM (Option (Array Expr))) name
  let result ← IO.mkRef none
  discard <| Term.TermElabM.run' <| Tactic.run step do
    result.set (← residual step #[])
  result.get

@[implemented_by stepResidualImpl]
opaque stepResidual (step : MVarId) : MetaM (Option (Array Expr))

/-! ## Failure records -/

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
  let some stepping ← steppingGoal? type
    | return { base with
        residual := #[type],
        unknown := #[("method", "the goal is a side condition, not a step of a method"),
          ("pc", "the goal is a side condition, not a step of a method"),
          ("instruction", "the goal is a side condition, not a step of a method"),
          ("missing", "the goal is a side condition: the residual is the goal itself")] }
  let method ← natLiteral? stepping.method
  let record := { base with method, reached := stepping.parts }
  let some pcTerm := stepping.pc
    | return { record with
        unknown := #[("pc", "the goal invokes the method; no instruction of it has run"),
          ("instruction", "the goal invokes the method; no instruction of it has run"),
          ("missing", "the goal invokes the method; no instruction of it has run")] }
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
  let isCall := (← whnfR op).isAppOf `CIL.Op.call
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
  let residual := (← stepResidual step.mvarId!).getD #[← instantiateMVars (← inferType step)]
  let missing := missingFactOf residual
  return { record with
    missing := missing.name, residual,
    suggestions := #[m!"supply {missing.hint}"] }

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
          unless olds[slot]! == news[slot]! do
            changes := changes.push m!"{name} {slot}: {olds[slot]!} ⟶ {news[slot]!}"
      else changes := changes.push m!"{name}: {old} ⟶ {new}"
    | _, _ => changes := changes.push m!"{name}: {old} ⟶ {new}"
  return changes

/-- What a step's result does to the state `before`: the parts it changed, or the return, call
    or fault it ends in. -/
def resultChanges (before : Array (String × Expr)) (result : Expr) :
    MetaM (Array MessageData) := do
  let result ← whnfR (← instantiateMVars result)
  if result.isAppOfArity ``Except.error 3 then return #[m!"faults: {result.appArg!}"]
  -- A step stated with an unknown result, as an existential step does, changes nothing it names.
  unless result.isAppOfArity ``Except.ok 3 do return #[]
  let action ← whnfR result.appArg!
  let args := action.getAppArgs
  if action.isAppOfArity `CIL.Safety.FrameAction.next 4 then
    return ← stateChanges before (statePartNames.zip #[args[0]!, args[2]!, args[1]!, args[3]!])
  if action.isAppOfArity `CIL.Safety.FrameAction.returned 2 then
    return #[m!"returns {args[0]!}"]
  if action.isAppOf `CIL.Safety.FrameAction.call || action.isAppOf `CIL.Safety.FrameAction.tailCall
      || action.isAppOf `CIL.Safety.FrameAction.construct then
    return #[m!"calls method {args[0]!} with {args[1]!}"]
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
  let args := current.getAppArgs
  let (body, op, pcTerm) := (args[0]!, args[1]!, args[2]!)
  let pc ← natLiteral? pcTerm
  -- The method is the index whose lookup gave the step's body.
  let mut method : Option Nat := none
  for sibling in siblings do
    let some (_, lookup, found) := (← instantiateMVars (← inferType sibling)).consumeMData.eq?
      | continue
    if lookup.isAppOf ``GetElem?.getElem? && found.isAppOf ``Option.some &&
        (← isDefEq found.appArg! body) then
      method ← natLiteral? lookup.appArg!
  let before := statePartNames.zip #[pcTerm, args[4]!, args[5]!, args[6]!]
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

/-- The LeanCIL tactic `stx` written in the source runs, by its first atom: none for
    syntax a tactic built. -/
def userTactic? (stx : Syntax) : Option String :=
  match stx.getHeadInfo, stx.getHead? with
  | .original .., some (.atom _ value) =>
    let value := String.ofList (value.toList.filter (· != ' '))
    if value.startsWith "cil_" then some value else none
  | _, _ => none

/-- The LeanCIL tactic `stx` runs, by its first atom, whether written in the source or built by
    another tactic's expansion. -/
def cilTactic? (stx : Syntax) : Option String :=
  match stx.getHead? with
  | some (.atom _ value) =>
    let value := String.ofList (value.toList.filter (· != ' '))
    if value.startsWith "cil_" then some value else none
  | _ => none

/-- The tactic nodes of an info tree, in elaboration order. -/
structure TacticNodes where
  /-- The outermost tactic nodes, each a tactic block. -/
  blocks : Array TacticNode := #[]
  /-- The LeanCIL tactic nodes written in the source. -/
  tactics : Array TacticNode := #[]
  /-- Every LeanCIL tactic node, including those another tactic's expansion built. -/
  raisers : Array TacticNode := #[]
  deriving Inhabited

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
           tactics := if (userTactic? tactic.stx).isSome then #[node] else #[]
           raisers := if (cilTactic? tactic.stx).isSome then #[node] else #[] }, true)
      | _, _ => ({}, inBlock)
    children.foldl (init := found) fun found child =>
      let more := tacticNodes child context inBlock
      { blocks := found.blocks ++ more.blocks, tactics := found.tactics ++ more.tactics
        raisers := found.raisers ++ more.raisers }

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

/-- The text of `message`. -/
def messageText (message : Message) : IO String := message.data.toString

/-- Log a failure record for each error a LeanCIL tactic raised, and for each goal a tactic block
    leaves unsolved after a LeanCIL tactic left it. -/
def logRecords (blocks tactics raisers : Array TacticNode) : CommandElabM Unit := do
  let fileMap ← getFileMap
  let log := (← get).messages
  let errors := (log.reported.toArray ++ log.unreported.toArray).filter
    (·.severity == .error)
  for error in errors do
    -- A tactic's own error is reported where its syntax starts, so an error inside a term it
    -- elaborates is Lean's; a LeanCIL error names the tactic that raised it.
    let text ← messageText error
    let raised := raisers.filter fun node =>
      (node.info.stx.getPos?.map (fileMap.toPosition · == error.pos)).getD false
    let named := raised.filter fun node =>
      (cilTactic? node.info.stx).any fun name => text.startsWith s!"{name}:"
    let some node := named.back? <|> raised.back? | continue
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
      return (← messageText error).startsWith "unsolved goals" &&
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

/-- After each command, the step trace under `trace.CIL.step` and the failure records under
    `cil.diagnostics`; nothing when neither is set. -/
def observer : Linter where
  name := `CIL.Safety.observer
  run := withSetOptionIn fun command => do
    let options ← getOptions
    let tracing := options.getBool `trace.CIL.step
    let recording := cil.diagnostics.get options
    unless tracing || recording do return
    let mut blocks := #[]
    let mut tactics := #[]
    let mut raisers := #[]
    for tree in (← get).infoState.trees do
      let found := tacticNodes tree
      blocks := blocks ++ found.blocks
      tactics := tactics ++ found.tactics
      raisers := raisers ++ found.raisers
    -- Only the nodes of this command: a tree may hold earlier commands' nodes.
    let inCommand (node : TacticNode) : Bool :=
      match node.info.stx.getPos?, command.getPos?, command.getTailPos? with
      | some point, some start, some stop => start ≤ point && point ≤ stop
      | _, _, _ => false
    let ownBlocks := blocks.filter inCommand
    -- The nodes of the elaboration Lean kept, each once: the info trees may hold a node twice.
    let ran (nodes : Array TacticNode) : Array TacticNode := Id.run do
      let mut seen : Std.HashSet (Array MVarId × Option Nat) := {}
      let mut live := #[]
      for node in nodes.filter inCommand do
        unless node.info.goalsBefore.all (kept ownBlocks) do continue
        let key := (node.info.goalsBefore.toArray, node.info.stx.getPos?.map (·.byteIdx))
        if seen.contains key then continue
        seen := seen.insert key
        live := live.push node
      return live
    let ownTactics := ran tactics
    if tracing then logSteps ownBlocks ownTactics
    if recording then logRecords ownBlocks ownTactics (ran raisers)

initialize addLinter observer

end CIL.Safety
