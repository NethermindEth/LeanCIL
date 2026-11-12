import CIL.Safety.Loops
import CIL.Safety.SymbolicExecution
import CIL.Safety.LoopFacts
import CIL.Safety.NumericLocals
import CIL.Safety.Obligations
import CIL.Safety.MissingFacts
import CIL.TermAccess

/-!
# Loop path automation

Fuel-free reasoning about loops in the checked interpreter. `LoopReaches` is a checked path
between two loop states whose fuel cost is existential, so proofs compose fetched
instructions without counting steps. `cil_loop_steps` walks a goal to an invariant cutpoint, and
`loopSteps` is the walk the frame tactics of `CIL.Safety.LoopFrameSteps` share; each reuses the
symbolic stepping tactics and takes, besides an explicit list, the facts `gatherLoopFacts` finds
in the proof context.
-/

namespace CIL.Safety

/-- Locate an invariant cutpoint by instruction shape. Missing matches point past
    the body and cannot satisfy the checked fetch obligations below. -/
def instructionLocation (body : CIL.Method) (predicate : CIL.Instruction → Bool) : Nat :=
  body.code.findIdx predicate

/-- A finite checked path whose cost is inferred while composing its instructions. -/
def LoopReaches (program : CIL.Program) (method : Nat) (args : List Value)
    (source target : LoopState) : Prop :=
  WP (fun cost reached => LoopSegment program method args source reached cost)
    (fun reached => reached = target)

theorem loop_reaches_refl {program : CIL.Program} {method : Nat} {args : List Value}
    {state : LoopState} : LoopReaches program method args state state :=
  ⟨0, state, (fun _ => rfl), rfl⟩

/-- Prepends one fetched non-branching step to a loop path. -/
theorem loop_reaches_next {program : CIL.Program} {method pc next : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {target : LoopState}
    (found : program[method]? = some body)
    (instruction : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next next values nextFrame updated))
    (rest : LoopReaches program method args ⟨next, nextFrame, values, updated⟩ target) :
    LoopReaches program method args ⟨pc, frame, stack, memory⟩ target := by
  obtain ⟨cost, reached, segment, rfl⟩ := rest
  refine ⟨cost + 1, reached, ?_, rfl⟩
  intro fuel
  change run program (fuel + (cost + 1)) method pc args frame stack memory = _
  rw [← Nat.add_assoc, run_next found instruction stepped]
  exact segment fuel

/-- A state terminates if its fetched instruction steps to a state that terminates. -/
theorem loop_terminates_next {program : CIL.Program} {method pc next : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body)
    (instruction : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next next values nextFrame updated))
    (rest : LoopTerminates program method args post ⟨next, nextFrame, values, updated⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  WP.step found instruction stepped rest

/-- A fetched `ret` whose checked results satisfy `post` terminates. -/
theorem loop_terminates_return {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack values : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body)
    (instruction : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.returned values updated))
    (checked : values.mapM (checkedValue (leaveFrame frame updated)) = .ok values)
    (satisfied : post (leaveFrame frame updated) values) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  WP.returned found instruction stepped checked satisfied

theorem loop_reaches_terminates {program : CIL.Program} {method : Nat} {args : List Value}
    {source target : LoopState} {post : Memory → List Value → Prop}
    (path : LoopReaches program method args source target)
    (finished : LoopTerminates program method args post target) :
    LoopTerminates program method args post source := by
  obtain ⟨cost, reached, segment, rfl⟩ := path
  exact WP.of_prefix segment finished

#print axioms loop_reaches_next
#print axioms loop_terminates_return
#print axioms loop_reaches_terminates

/-- Where a loop stepping tactic takes its goal: to the target state of a `LoopReaches`, or along
    a `LoopTerminates` through its return, only up to a call or return, or up to the pc `target`
    and any struct store before it. -/
inductive LoopStepping where
  | reach
  | finish
  | advance
  | resume (target : Nat)
  deriving BEq

/-- The list lemmas that put a stepped stack in literal form. -/
def loopStackLemmas : Array Lean.Name :=
  #[``List.drop_succ_cons, ``List.drop_zero, ``List.drop_nil, ``List.take_succ_cons,
    ``List.take_zero, ``List.take_nil, ``List.reverse_cons, ``List.reverse_nil,
    ``List.nil_append, ``List.cons_append, ``List.append_nil]

open Lean Meta in
/-- The source state of a loop goal and, for `LoopReaches`, its target. -/
def loopGoalStates (target : Expr) : MetaM (Option (Expr × Option Expr)) := do
  let target := (← instantiateMVars target).consumeMData
  if let some #[_, _, _, source, reached] := argumentsOf? target ``LoopReaches 5 then
    return some (source, some reached)
  if let some #[_, _, _, _, source] := argumentsOf? target ``LoopTerminates 5 then
    return some (source, none)
  return none

open Lean Meta in
/-- The literal value of a natural-number expression, reducing definitions such as a cutpoint's
    generated `pc`. -/
def literalNat? (value : Expr) : MetaM (Option Nat) := do
  let value ← instantiateMVars value
  if let some literal ← getNatValue? (← whnf value) then return literal
  if value.hasFVar || value.hasMVar then return none
  (Meta.evalNat (← Meta.reduce value)).run

open Lean Meta in
/-- `term` with each sum of two natural-number literals, such as a stepped pc `17 + 1`, written
    as its literal value; the result is definitionally equal to `term`. -/
def loopLiteralSums (term : Expr) : Expr :=
  term.replace fun part =>
    if let some #[carrier, _, _, _, augend, addend] := argumentsOf? part ``HAdd.hAdd 6 then
      if carrier.isConstOf ``Nat then
        match augend.nat?, addend.nat? with
        | some left, some right => some (mkNatLit (left + right))
        | _, _ => none
      else none
    else none

open Lean Elab Tactic Meta in
/-- Write the main goal's literal sums, such as its pc, as literals (`loopLiteralSums`). -/
def loopLiteralGoal : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let literal := loopLiteralSums target
  unless literal == target do replaceMainGoal [← goal.replaceTargetDefEq literal]

open Lean Meta in
/-- The pc, frame, stack and memory of a loop state up to reduction. -/
def loopStateParts? (state : Expr) : MetaM (Option (Array Expr)) := do
  let state ← whnf (← instantiateMVars state)
  unless state.isAppOfArity ``LoopState.mk 4 do return none
  return some state.getAppArgs

/-- The instruction a loop goal's source state fetches, the proofs of its method and
    instruction lookups, and the step obligation taking it leaves. -/
structure LoopFetched where
  /-- The fetched instruction. -/
  op : Lean.Expr
  /-- A proof that the program holds the goal's method. -/
  found : Lean.Expr
  /-- A proof that the method's code holds `op` at the goal's pc. -/
  instruction : Lean.Expr
  /-- The obligation that `op` steps to a next state. -/
  step : Lean.MVarId

open Lean Elab Tactic Meta in
/-- The instruction a loop goal's source state fetches, with the lookups closed by
    `cil_lookup [facts]`. Fails when they do not close. -/
def loopFetch (facts : Array Term) : TacticM LoopFetched := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let lemma := if target.isAppOfArity ``LoopReaches 5 then ``loop_reaches_next
    else ``loop_terminates_next
  let (premises, _, conclusion) ←
    forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels lemma))
  unless ← isDefEq conclusion target do throwError "the goal is not a loop path at a literal state"
  let lookups := premises.size - 4
  let methodLookup ← entryAt "loopFetch" premises lookups
  let instructionLookup ← entryAt "loopFetch" premises (lookups + 1)
  let stepPremise ← entryAt "loopFetch" premises (lookups + 2)
  for proof in [methodLookup, instructionLookup] do
    let .mvar lookup := proof | throwError "loopFetch: expected a lookup premise, but found\
      {indentExpr proof}"
    let remaining ← Tactic.run lookup <| Term.withoutErrToSorry <| withoutRecover <|
      evalTactic (← `(tactic| cil_lookup [$facts,*]))
    unless remaining.isEmpty do throwError "the method or instruction lookup did not close"
  let fetched ← instantiateMVars (← inferType instructionLookup)
  let some (_, _, op) := fetched.eq? | throwError "unexpected instruction lookup"
  let found ← instantiateMVars methodLookup
  let instruction ← instantiateMVars instructionLookup
  let op ← lastArgument "loopFetch" op
  let .mvar step := stepPremise
    | throwError "loopFetch: expected a step premise, but found{indentExpr stepPremise}"
  return { op, found, instruction, step }

/-- Instructions that only move values, which no case split decides. -/
def loopMovesOnly : List Lean.Name :=
  [``CIL.Instruction.nop, ``CIL.Instruction.arg, ``CIL.Instruction.local,
    ``CIL.Instruction.localAddr, ``CIL.Instruction.setLocal, ``CIL.Instruction.const32,
    ``CIL.Instruction.const64, ``CIL.Instruction.branch, ``CIL.Instruction.skipInit,
    ``CIL.Instruction.initAggregate, ``CIL.Instruction.fieldAddress]

/-- Instructions that read no reference: they compare or compute on scalars, or move a value
    that `loopReadsReferences` shows is a scalar. -/
def loopScalarOnly : List Lean.Name :=
  [``CIL.Instruction.nop, ``CIL.Instruction.arg, ``CIL.Instruction.local,
    ``CIL.Instruction.localAddr, ``CIL.Instruction.setLocal, ``CIL.Instruction.const32,
    ``CIL.Instruction.const64, ``CIL.Instruction.branch, ``CIL.Instruction.nativeBinary,
    ``CIL.Instruction.divide, ``CIL.Instruction.checkedArithmetic,
    ``CIL.Instruction.checkedConvert, ``CIL.Instruction.convU2, ``CIL.Instruction.bxor,
    ``CIL.Instruction.pop, ``CIL.Instruction.gt, ``CIL.Instruction.bgt, ``CIL.Instruction.ble,
    ``CIL.Instruction.bleu, ``CIL.Instruction.switch, ``CIL.Instruction.brzero,
    ``CIL.Instruction.brnonzero, ``CIL.Instruction.bltu, ``CIL.Instruction.bgeu,
    ``CIL.Instruction.bgtu, ``CIL.Instruction.bge, ``CIL.Instruction.blt,
    ``CIL.Instruction.beq, ``CIL.Instruction.bne]

open Lean Meta in
/-- Whether the step obligation `step` of the fetched `op` can check a reference or span: any
    instruction but `loopScalarOnly`, an argument load or local store of a non-scalar, and a load
    of a local that is not a byte home. -/
def loopReadsReferences (op : Expr) (step : MVarId) : MetaM Bool := do
  let op ← whnfR op
  let some name := op.getAppFn.constName? | return true
  unless loopScalarOnly.contains name do return true
  let scalar (value : Expr) : MetaM Bool := return (← whnfR value).isAppOf ``Value.scalar
  let some (_, lhs, _) := (← instantiateMVars (← step.getType)).consumeMData.eq? | return true
  let some #[_, _, _, args, frame, stack, _] := argumentsOf? lhs ``step 7 | return true
  if name == ``CIL.Instruction.arg then
    -- An argument is checked as it is loaded, so a reference argument's `form` is read.
    let some indexTerm := argument? op 0 | return true
    let some index ← literalNat? indexTerm | return true
    let entries ← listEntries args
    let some (_, value) := entries.find? (·.1 == index) | return true
    return !(← scalar value)
  if name == ``CIL.Instruction.setLocal then
    let stack ← whnfR stack
    let some #[_, top, _] := argumentsOf? stack ``List.cons 3 | return true
    return !(← scalar top)
  if name == ``CIL.Instruction.local then
    -- Loading a span or reference local checks it.
    let some indexTerm := argument? op 0 | return true
    let some index ← literalNat? indexTerm | return true
    let frame ← whnfR frame
    let some #[_, locals, _, _] := argumentsOf? frame ``Frame.mk 4 | return true
    let some (_, slot) := (← listEntries locals).find? (·.1 == index) | return true
    let slot ← whnfR slot
    let some #[kind, _] := argumentsOf? slot ``LocalSlot.bytes 2 | return true
    return (← whnfR kind).isConstOf ``CIL.LocalKind.reference
  return false

open Lean Meta in
/-- Whether the store `op` with obligation `step` can step without the frame lemmas: it is not a
    byte home's local store or a struct field store or zeroing, or a hypothesis or one of `known`
    states a store or step at its memory, such as the frame lemmas produce. -/
def loopStoreKnown (op : Expr) (step : MVarId) (known : Array Expr) : MetaM Bool :=
    step.withContext do
  let op ← whnfR op
  let some (_, lhs, _) := (← instantiateMVars (← step.getType)).consumeMData.eq? | return true
  let some #[_, _, _, _, frame, _, memory] := argumentsOf? lhs ``CIL.Safety.step 7
    | return true
  if op.isAppOf ``CIL.Instruction.setLocal then
    -- A span or reference local's store reduces without a fact.
    let some indexTerm := argument? op 0 | return true
    let some index ← literalNat? indexTerm | return true
    let frame ← whnfR frame
    let some #[_, locals, _, _] := argumentsOf? frame ``Frame.mk 4 | return true
    let some (_, slot) := (← listEntries locals).find? (·.1 == index) | return true
    unless (← whnfR slot).isAppOf ``LocalSlot.bytes do return true
  else unless
      op.isAppOf ``CIL.Instruction.setFieldAt || op.isAppOf ``CIL.Instruction.initAggregate do
    return true
  let heads := [``storeLocal, ``storeValue, ``CIL.Safety.step]
  let states (type : Expr) : Bool := (type.find? fun part =>
    heads.any part.isAppOf && part.getAppArgs.contains memory).isSome
  if known.any states then return true
  (← getLCtx).anyM fun declaration => do
    if declaration.isImplementationDetail then return false
    return states (← instantiateMVars declaration.type)

/-- The groups of `facts` the instruction `op` reads besides its core: a return reads them all,
    since its postcondition may speak of anything the loop proved, and the reference facts only
    an instruction that `references` says can check a reference or span. -/
def LoopFacts.readBy (facts : LoopFacts) (op : Lean.Name) (references : Bool) :
    Array (Array Lean.Syntax.Term) :=
  if op == ``CIL.Instruction.ret then
    #[facts.addresses, facts.fields, facts.cases, facts.references] else
  #[if op == ``CIL.Instruction.localAddr then facts.addresses else #[],
    if op == ``CIL.Instruction.fieldAt then facts.fields else #[],
    if loopMovesOnly.contains op then #[] else facts.cases,
    if references then facts.references else #[]]

/-- A hint naming the fact a stuck step needs, from the residual of that step. -/
def loopMissingHint (residual : Array Lean.Expr) : Lean.MetaM Lean.MessageData :=
  return missingFactHint residual

open Lean Elab Tactic Meta in
/-- Fail, as `tactic`, naming why the loop goal cannot be stepped: an undecided branch, an
    instruction that cannot be fetched, a call, or the residual of the step at its pc. Returns
    instead when `stops` accepts the fetched opcode, as a call or return a later tactic takes. -/
def loopStuck (tactic : String) (facts prepared : Array Term)
    (stops : Lean.Name → Bool) : TacticM Unit := withMainContext do
  let saved ← saveState
  let some (source, _) ← loopGoalStates (← getMainTarget)
    | throwError "{tactic}: expected a `LoopReaches` or `LoopTerminates` goal{← obligationNote}"
  let some #[pc, _, _, memory] ← loopStateParts? source
    | throwError "{tactic}: the source state does not reduce to a literal state:\
        {indentExpr (loopLiteralSums source)}"
  let some position ← literalNat? pc
    | throwError "{tactic}: the pc is not a literal, so a branch was not decided; supply a fact \
        deciding its condition. The pc is{indentExpr pc}"
  let fetched ← try loopFetch facts catch error =>
    saved.restore
    throwError "{tactic}: cannot fetch the instruction at pc {position}: {error.toMessageData}"
  let op := fetched.op
  let stepGoal := fetched.step
  let opName := ((← whnfR op).getAppFn.constName?).getD Name.anonymous
  if stops opName then saved.restore; return
  if callsCallee opName then
    saved.restore
    throwError "{tactic}: pc {position} is a call ({op}); cross it with `cil_loop_call` and the \
      callee's contract"
  let obligation := loopLiteralSums (← instantiateMVars (← stepGoal.getType))
  -- The step rewritten as far as its equations and the facts go shows the term left unproved.
  let residual ← stepResidual stepGoal prepared
  saved.restore
  let shown := match residual with
    | some goals => MessageData.joinSep (goals.toList.map (m!"{loopLiteralSums ·}")) "\n"
    | none => m!"no step equation or fact rewrites it"
  let hint ← loopMissingHint (residual.getD #[obligation])
  throwError "{tactic}: cannot step pc {position} ({op}) at memory{indentExpr memory}\n\
    The step is{indentExpr obligation}\n\
    With the step equations and facts it reduces to{indentD shown}\n\
    Supply {hint}."

open Lean Elab Tactic Meta in
/-- Fail, as `tactic`, for a `LoopReaches` goal that has stepped back to its target's pc in
    another state, naming each differing part instead of stepping past the cutpoint. -/
def loopTargetMismatch (tactic : String) (position : Nat) (source target : Expr) :
    TacticM Unit := withMainContext do
  let some reached ← loopStateParts? source | return
  let some expected ← loopStateParts? target | return
  let names := #["pc", "frame", "stack", "memory"]
  let mut differing : MessageData := m!""
  for (name, reachedPart, expectedPart) in names.zip (reached.zip expected) do
    unless ← withNewMCtxDepth (isDefEq reachedPart expectedPart) do
      differing := differing ++ m!"\n{name}: reached\
        {indentExpr (loopLiteralSums reachedPart)}\n\
        but the target has{indentExpr (loopLiteralSums expectedPart)}"
  throwError "{tactic}: target state not matched at pc {position}:{differing}\nState a fact in \
    the reached form, or state the target in it."

open Lean Elab Tactic Meta in
/-- Whether a loop goal mentions a list operation that `loopStackLemmas` puts in literal form. -/
def loopMentionsStackOperations : TacticM Bool := withMainContext do
  let operations := [``List.drop, ``List.take, ``List.reverse, ``HAppend.hAppend]
  return ((← instantiateMVars (← getMainTarget)).find? fun term =>
    term.constName?.any operations.contains).isSome

open Lean Elab Tactic Meta in
/-- Step a loop goal through fetched instructions with the `facts` as `mode` directs, failing
    through `loopStuck` or `loopTargetMismatch` where it cannot go on. Each instruction steps with
    `prepared`, the normalised core, and the groups about it, each normalised once when first
    read. A resumed walk stops at its target pc once a step is taken, which `stepped` says
    happened before this call; any walk but `.reach` also stops at a struct store or zeroing no
    fact steps. A finishing walk takes its return through `finishReturn`, given the fetched
    return and the facts it reads, or else leaves a return the facts do not close as the goal.
    Returns the opcode the walk stopped at before stepping it, if any. -/
def loopSteps (tactic : String) (mode : LoopStepping) (facts : LoopFacts) (prepared : Array Term)
    (stepped : Bool := false)
    (finishReturn : Option (LoopFetched → Array Term → TacticM Unit) := none) :
    TacticM (Option Lean.Name) := do
  let stackLemmas : Array Term := loopStackLemmas.map fun name => mkIdent (`_root_ ++ name)
  let core := facts.core
  let withStack := core ++ stackLemmas
  let rewrite ← `(tactic| simp only [$[$core:term],*])
  let rewriteStack ← `(tactic| simp only [$[$withStack:term],*])
  let close ← `(tactic| exact CIL.Safety.loop_reaches_refl)
  -- Each group of `LoopFacts.readBy`, once normalised.
  let mut normalised : Array (Option (Array Term)) := #[none, none, none, none]
  let groupBases := #[`homeForm, `fieldRead, `caseSplit, `callerFact]
  let attempt (step : Syntax) : TacticM Bool := do
    let saved ← saveState
    -- Without recovery a failed alternative throws instead of logging an error and admitting.
    try Term.withoutErrToSorry <| withoutRecover <| evalTactic step; return true
    catch _ => saved.restore; return false
  let reachedPc : TacticM (Option (Nat × Expr × Expr)) := withMainContext do
    let some (source, some target) ← loopGoalStates (← getMainTarget) | return none
    let some #[pc, _, _, _] ← loopStateParts? source | return none
    let some #[targetPc, _, _, _] ← loopStateParts? target | return none
    let some position ← literalNat? pc | return none
    unless (← literalNat? targetPc) == some position do return none
    return some (position, source, target)
  let currentPc : TacticM (Option Nat) := withMainContext do
    let some (source, _) ← loopGoalStates (← getMainTarget) | return none
    let some #[pc, _, _, _] ← loopStateParts? source | return none
    literalNat? pc
  let stops : Lean.Name → Bool := match mode with
    | .reach => fun _ => false
    | .finish => (· == ``CIL.Instruction.ret)
    | .advance => fun op => callsCallee op || op == ``CIL.Instruction.ret
    | .resume _ => fun op =>
      op == ``CIL.Instruction.setFieldAt || op == ``CIL.Instruction.initAggregate
  -- A struct store no fact steps ends any walk but `.reach`, for the frame lemmas to take.
  let yields : Lean.Name → Bool := fun op => stops op || (mode != .reach &&
    (op == ``CIL.Instruction.setFieldAt || op == ``CIL.Instruction.initAggregate ||
      op == ``CIL.Instruction.setLocal))
  let mut taken := 0
  repeat
    if (← getGoals).isEmpty then return none
    let rewriting := if ← loopMentionsStackOperations then rewriteStack else rewrite
    if ← attempt rewriting then continue
    if let .resume target := mode then
      if taken > 0 || stepped then
        if (← currentPc) == some target then return none
    if mode == .reach then
      if ← attempt close then return none
      if taken > 0 then
        if let some (position, source, target) ← reachedPc then
          loopTargetMismatch tactic position source target
    -- Fetching unifies the goal with a step lemma; only its closed lookup proofs are kept.
    let saved ← saveState
    let fetched? ← observing? do
      let fetched ← loopFetch core
      let stores := [``CIL.Instruction.setLocal, ``CIL.Instruction.setFieldAt,
        ``CIL.Instruction.initAggregate]
      let unknownStore ← if stores.any (← whnfR fetched.op).isAppOf then
          pure !(← loopStoreKnown fetched.op fetched.step facts.known)
        else pure false
      return (fetched, ← loopReadsReferences fetched.op fetched.step, unknownStore)
    saved.restore
    let some (fetched, references, unknownStore) := fetched?
      | loopStuck tactic facts.all prepared stops; return none
    let op := ((← whnfR fetched.op).getAppFn.constName?).getD Name.anonymous
    let finishing := mode == .finish && op == ``CIL.Instruction.ret
    -- A call or return ends an advance before any step; a resumed walk tries the store first,
    -- since a store fact the frame lemmas just produced may step it.
    let resuming := match mode with | .resume _ => true | _ => false
    if stops op && !finishing && !resuming then return some op
    -- A store no fact states steps only through the frame lemmas.
    if mode != .reach && unknownStore then return some op
    -- The groups this instruction reads, normalised in the goal the first time one is read.
    let mut reading := prepared
    let read := facts.readBy op references
    for h : index in [:read.size] do
      if read[index].isEmpty then continue
      let cached ← entryAt tactic normalised index
      let base ← entryAt tactic groupBases index
      let ready ← match cached with
        | some ready => pure ready
        | none => do
          let asserted ← assertLoopFacts base read[index] facts.known
          normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|)) asserted
      normalised := normalised.set! index (some ready)
      reading := reading ++ ready
    let found ← Term.exprToSyntax fetched.found
    let instruction ← Term.exprToSyntax fetched.instruction
    if finishing then
      if let some take := finishReturn then take fetched reading; return none
      let finish ← `(tactic| (
          apply CIL.Safety.loop_terminates_return $found $instruction
          · cil_checked_step_normalized [$[$reading:term],*]
          · rfl
          · first
            | simp [$[$reading:term],*]; done
            -- Frame cleanup only after the facts fail, since unfolding `leaveFrame` first
            -- would hide it from a supplied fact about the exited frame's memory.
            | simp [CIL.Safety.leaveFrame, CIL.NarrowKind.extend, $[$reading:term],*]))
      if ← attempt finish then continue
      -- A return whose results or postcondition the facts do not prove is left as the goal.
      return some op
    let next ← match mode with
      | .reach => `(tactic| (
          apply CIL.Safety.loop_reaches_next $found $instruction
          · cil_checked_step_normalized [$[$reading:term],*]))
      | _ => `(tactic| (
          apply CIL.Safety.loop_terminates_next $found $instruction
          · cil_checked_step_normalized [$[$reading:term],*]))
    if ← attempt next then
      taken := taken + 1
      continue
    if yields op then return some op
    loopStuck tactic facts.all reading yields
    return none
  return none

/-- Compose actual fetched instructions until the requested invariant state.
    Fuel is inferred from the path, including NOPs and unconditional branches. The facts are
    the optional list and those `gatherLoopFacts` finds. Fails naming the pc, the instruction
    and the residual step where a step cannot be taken, and the differing parts where the path
    returns to the target's pc in another state. -/
syntax "cil_loop_steps" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cil_loop_steps $[[$facts:term,*]]?) => do
    let facts ← gatherLoopFactGroups (facts.map (·.getElems) |>.getD #[])
    let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
      (#[← `(CIL.truth)] ++ facts.core)
    discard <| loopSteps "cil_loop_steps" .reach facts prepared

end CIL.Safety
