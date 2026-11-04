import CIL.Safety.Loops
import CIL.Safety.SymbolicExecution
import CIL.Safety.LoopFacts

/-!
# Loop path automation

Fuel-free reasoning about loops in the checked interpreter. `LoopReaches` is a checked path
between two loop states whose fuel cost is existential, so proofs compose fetched
instructions without counting steps. `cil_loop_steps` walks a goal to an invariant cutpoint
and `cil_loop_finish` walks it to a return; both reuse the symbolic stepping tactics and take,
besides an explicit list, the facts `gatherLoopFacts` finds in the proof context.
-/

namespace CIL.Safety

/-- Locate an invariant cutpoint by instruction shape. Missing matches point past
    the body and cannot satisfy the checked fetch obligations below. -/
def instructionLocation (body : CIL.Method) (predicate : CIL.Op → Bool) : Nat :=
  body.code.findIdx predicate

/-- A finite checked path whose cost is inferred while composing its instructions. -/
def LoopReaches (program : CIL.Program) (method : Nat) (args : List Value)
    (source target : LoopState) : Prop :=
  ∃ cost, LoopSegment program method args source target cost

theorem loop_reaches_refl {program : CIL.Program} {method : Nat} {args : List Value}
    {state : LoopState} : LoopReaches program method args state state :=
  ⟨0, fun _ => rfl⟩

/-- Prepends one fetched non-branching step to a loop path. -/
theorem loop_reaches_next {program : CIL.Program} {method pc next : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {target : LoopState}
    (found : program[method]? = some body)
    (instruction : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next next values nextFrame updated))
    (rest : LoopReaches program method args ⟨next, nextFrame, values, updated⟩ target) :
    LoopReaches program method args ⟨pc, frame, stack, memory⟩ target := by
  obtain ⟨cost, segment⟩ := rest
  refine ⟨cost + 1, ?_⟩
  intro fuel
  change run program (fuel + (cost + 1)) method pc args frame stack memory = _
  rw [← Nat.add_assoc, run_next found instruction stepped]
  exact segment fuel

/-- A state terminates if its fetched instruction steps to a state that terminates. -/
theorem loop_terminates_next {program : CIL.Program} {method pc next : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body)
    (instruction : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next next values nextFrame updated))
    (rest : LoopTerminates program method args post ⟨next, nextFrame, values, updated⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  run_next_exists post found instruction stepped rest

/-- A fetched `ret` whose checked results satisfy `post` terminates. -/
theorem loop_terminates_return {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body)
    (instruction : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.returned values updated))
    (checked : values.mapM (checkedValue (leaveFrame frame updated)) = .ok values)
    (satisfied : post (leaveFrame frame updated) values) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  ⟨1, leaveFrame frame updated, values, run_return found instruction stepped checked, satisfied⟩

theorem loop_reaches_terminates {program : CIL.Program} {method : Nat} {args : List Value}
    {source target : LoopState} {post : Memory → List Value → Prop}
    (path : LoopReaches program method args source target)
    (finished : LoopTerminates program method args post target) :
    LoopTerminates program method args post source := by
  obtain ⟨cost, segment⟩ := path
  obtain ⟨fuel, final, values, executed, satisfied⟩ := finished
  exact ⟨fuel + cost, final, values, (segment fuel).trans executed, satisfied⟩

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
  if target.isAppOfArity ``LoopReaches 5 then
    return some (target.getArg! 3, some (target.getArg! 4))
  if target.isAppOfArity ``LoopTerminates 5 then return some (target.getArg! 4, none)
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
  for proof in [premises[lookups]!, premises[lookups + 1]!] do
    let remaining ← Tactic.run proof.mvarId! <| Term.withoutErrToSorry <| withoutRecover <|
      evalTactic (← `(tactic| cil_lookup [$facts,*]))
    unless remaining.isEmpty do throwError "the method or instruction lookup did not close"
  let fetched ← instantiateMVars (← inferType premises[lookups + 1]!)
  let some (_, _, op) := fetched.eq? | throwError "unexpected instruction lookup"
  let found ← instantiateMVars premises[lookups]!
  let instruction ← instantiateMVars premises[lookups + 1]!
  return { op := op.appArg!, found, instruction, step := premises[lookups + 2]!.mvarId! }

/-- Instructions that only move values, which no case split decides. -/
def loopMovesOnly : List Lean.Name :=
  [``CIL.Op.nop, ``CIL.Op.arg, ``CIL.Op.vectorArg, ``CIL.Op.vectorArgAddr, ``CIL.Op.local,
    ``CIL.Op.vectorLocal, ``CIL.Op.vectorLocalAddr, ``CIL.Op.setVectorLocal, ``CIL.Op.localAddr,
    ``CIL.Op.setLocal, ``CIL.Op.const32, ``CIL.Op.const64, ``CIL.Op.branch, ``CIL.Op.skipInit,
    ``CIL.Op.initAggregate, ``CIL.Op.fieldAddress]

/-- The groups of `facts` the instruction `op` reads besides its core: a return reads them all,
    since its postcondition may speak of anything the loop proved. -/
def LoopFacts.readBy (facts : LoopFacts) (op : Lean.Name) : Array (Array Lean.Syntax.Term) :=
  if op == ``CIL.Op.ret then #[facts.addresses, facts.fields, facts.cases] else
  #[if op == ``CIL.Op.localAddr || op == ``CIL.Op.vectorLocalAddr then facts.addresses else #[],
    if op == ``CIL.Op.fieldAt then facts.fields else #[],
    if loopMovesOnly.contains op then #[] else facts.cases]

open Lean Elab Tactic Meta in
/-- Fail, as `tactic`, naming why the loop goal cannot be stepped: an undecided branch, an
    instruction that cannot be fetched, a call, or the residual of the step at its pc. Returns
    instead when `stops` accepts the fetched opcode, as a call or return a later tactic takes. -/
def loopStuck (tactic : String) (facts prepared : Array Term)
    (stops : Lean.Name → Bool) : TacticM Unit := withMainContext do
  let saved ← saveState
  let some (source, _) ← loopGoalStates (← getMainTarget)
    | throwError "{tactic}: expected a `LoopReaches` or `LoopTerminates` goal"
  let some parts ← loopStateParts? source
    | throwError "{tactic}: the source state does not reduce to a literal state:\
        {indentExpr source}"
  let some position ← literalNat? parts[0]!
    | throwError "{tactic}: the pc is not a literal, so a branch was not decided; supply a fact \
        deciding its condition. The pc is{indentExpr parts[0]!}"
  let fetched ← try loopFetch facts catch error =>
    saved.restore
    throwError "{tactic}: cannot fetch the instruction at pc {position}: {error.toMessageData}"
  let op := fetched.op
  let stepGoal := fetched.step
  let opName := ((← whnfR op).getAppFn.constName?).getD Name.anonymous
  if stops opName then saved.restore; return
  if opName == ``CIL.Op.call then
    saved.restore
    throwError "{tactic}: pc {position} is a call ({op}); cross it with `cil_loop_call` and the \
      callee's contract"
  let obligation ← instantiateMVars (← stepGoal.getType)
  -- The step rewritten as far as its equations and the facts go shows the term left unproved.
  let residual ← try
      let remaining ← Tactic.run stepGoal <| Term.withoutErrToSorry <| withoutRecover <|
        evalTactic (← `(tactic| (
          simp only [cil_instruction_step, cil_step, cil_guard, CIL.Safety.instructionStep,
            $[$prepared:term],*]
          try simp [cil_guard, cil_checked, CIL.Safety.checkedValue, CIL.Safety.numericValue,
            CIL.Safety.scalars, CIL.Safety.formValue, CIL.Safety.checkedAt, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure, $[$prepared:term],*])))
      pure (MessageData.joinSep (← remaining.mapM fun goal => do
        return m!"{← instantiateMVars (← goal.getType)}") "\n")
    catch _ => pure m!"no step equation or fact rewrites it"
  saved.restore
  throwError "{tactic}: cannot step pc {position} ({op}) at memory{indentExpr parts[3]!}\n\
    The step is{indentExpr obligation}\n\
    With the step equations and facts it reduces to{indentD residual}\n\
    Supply a fact for what is left: a `LoopFrame` at this memory for a local, or the step \
    equation of a store with this stack."

open Lean Elab Tactic Meta in
/-- Fail, as `tactic`, for a `LoopReaches` goal that has stepped back to its target's pc in
    another state, naming each differing part instead of stepping past the cutpoint. -/
def loopTargetMismatch (tactic : String) (position : Nat) (source target : Expr) :
    TacticM Unit := withMainContext do
  let some reached ← loopStateParts? source | return
  let some expected ← loopStateParts? target | return
  let names := #["pc", "frame", "stack", "memory"]
  let mut differing : MessageData := m!""
  for index in [:4] do
    unless ← withNewMCtxDepth (isDefEq reached[index]! expected[index]!) do
      differing := differing ++ m!"\n{names[index]!}: reached{indentExpr reached[index]!}\n\
        but the target has{indentExpr expected[index]!}"
  throwError "{tactic}: target state not matched at pc {position}:{differing}\nState a fact in \
    the reached form, or state the target in it."

open Lean Elab Tactic Meta in
/-- Whether a loop goal mentions a list operation that `loopStackLemmas` puts in literal form. -/
def loopMentionsStackOperations : TacticM Bool := withMainContext do
  let operations := [``List.drop, ``List.take, ``List.reverse, ``HAppend.hAppend]
  return ((← instantiateMVars (← getMainTarget)).find? fun term =>
    term.isConst && operations.contains term.constName!).isSome

open Lean Elab Tactic Meta in
/-- Step a loop goal through fetched instructions with the `facts` as `mode` directs, failing
    through `loopStuck` or `loopTargetMismatch` where it cannot go on. Each instruction steps with
    `prepared`, the normalised core, and the groups about it, each normalised once when first
    read. A resumed walk stops at its target pc once a step is taken, which `stepped` says
    happened before this call. -/
def loopSteps (tactic : String) (mode : LoopStepping) (facts : LoopFacts) (prepared : Array Term)
    (stepped : Bool := false) : TacticM Unit := do
  let stackLemmas : Array Term := loopStackLemmas.map fun name => mkIdent (`_root_ ++ name)
  let core := facts.core
  let withStack := core ++ stackLemmas
  let rewrite ← `(tactic| simp only [$[$core:term],*])
  let rewriteStack ← `(tactic| simp only [$[$withStack:term],*])
  let close ← `(tactic| exact CIL.Safety.loop_reaches_refl)
  -- Each group of `LoopFacts.readBy`, once normalised.
  let mut normalised : Array (Option (Array Term)) := #[none, none, none]
  let groupBases := #[`homeForm, `fieldRead, `caseSplit]
  let attempt (step : Syntax) : TacticM Bool := do
    let saved ← saveState
    -- Without recovery a failed alternative throws instead of logging an error and admitting.
    try Term.withoutErrToSorry <| withoutRecover <| evalTactic step; return true
    catch _ => saved.restore; return false
  let reachedPc : TacticM (Option (Nat × Expr × Expr)) := withMainContext do
    let some (source, some target) ← loopGoalStates (← getMainTarget) | return none
    let some parts ← loopStateParts? source | return none
    let some targetParts ← loopStateParts? target | return none
    let some position ← literalNat? parts[0]! | return none
    unless (← literalNat? targetParts[0]!) == some position do return none
    return some (position, source, target)
  let currentPc : TacticM (Option Nat) := withMainContext do
    let some (source, _) ← loopGoalStates (← getMainTarget) | return none
    let some parts ← loopStateParts? source | return none
    literalNat? parts[0]!
  let stops : Lean.Name → Bool := match mode with
    | .reach => fun _ => false
    | .finish => (· == ``CIL.Op.ret)
    | .advance => fun op => op == ``CIL.Op.call || op == ``CIL.Op.ret
    | .resume _ => fun op => op == ``CIL.Op.setFieldAt || op == ``CIL.Op.initAggregate
  let mut taken := 0
  repeat
    if (← getGoals).isEmpty then return
    let rewriting := if ← loopMentionsStackOperations then rewriteStack else rewrite
    if ← attempt rewriting then continue
    if let .resume target := mode then
      if taken > 0 || stepped then
        if (← currentPc) == some target then return
    if mode == .reach then
      if ← attempt close then return
      if taken > 0 then
        if let some (position, source, target) ← reachedPc then
          loopTargetMismatch tactic position source target
    -- Fetching unifies the goal with a step lemma; only its closed lookup proofs are kept.
    let saved ← saveState
    let fetched? ← observing? (loopFetch core)
    saved.restore
    let some fetched := fetched? | loopStuck tactic facts.all prepared stops; return
    let op := ((← whnfR fetched.op).getAppFn.constName?).getD Name.anonymous
    let finishing := mode == .finish && op == ``CIL.Op.ret
    -- A call or return ends an advance before any step; a resumed walk tries the store first,
    -- since a store fact the frame lemmas just produced may step it.
    let resuming := match mode with | .resume _ => true | _ => false
    if stops op && !finishing && !resuming then return
    -- The groups this instruction reads, normalised in the goal the first time one is read.
    let mut reading := prepared
    let read := facts.readBy op
    for index in [:read.size] do
      if read[index]!.isEmpty then continue
      let ready ← match normalised[index]! with
        | some ready => pure ready
        | none => do
          let asserted ← assertLoopFacts groupBases[index]! read[index]!
          normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|)) asserted
      normalised := normalised.set! index (some ready)
      reading := reading ++ ready
    let found ← Term.exprToSyntax fetched.found
    let instruction ← Term.exprToSyntax fetched.instruction
    if finishing then
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
      return
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
    loopStuck tactic facts.all reading stops
    return

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
    loopSteps "cil_loop_steps" .reach facts prepared

/-- Establish an exit path and its postcondition without choosing a fuel bound. The facts are
    the optional list and those `gatherLoopFacts` finds. A return whose results or postcondition
    the facts do not prove is left as the goal; any other step that cannot be taken fails,
    naming the pc, the instruction and the residual step. -/
syntax "cil_loop_finish" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cil_loop_finish $[[$facts:term,*]]?) => do
    let facts ← gatherLoopFactGroups (facts.map (·.getElems) |>.getD #[])
    let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
      (#[← `(CIL.truth)] ++ facts.core)
    loopSteps "cil_loop_finish" .finish facts prepared

end CIL.Safety
