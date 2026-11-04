import CIL.Safety.LoopFrameFields
import CIL.Safety.LoopContract

/-!
# Loop tactics that carry frame facts

The tactics that walk a loop's `LoopTerminates` goals while keeping its `LoopFrame` current:
`cil_loop_advance` steps to a call or return, `cil_loop_finish` through a return,
`cil_loop_call` crosses a call through the callee's contract and continues with the frame after
it, and `cil_loop_recurse` steps to a loop head and applies the head's hypothesis there. Each walk
takes the struct zeroings and field stores on its way through the frame's lemmas. A memory a
store or call produces is named in the context with its frame, so the next step reads it like any
other fact.
-/

namespace CIL.Safety

open Lean Elab Tactic Meta

/-- The frame facts in scope, latest first, each as its proof and its `LoopFrame` type; an entry
    frame proved for every footprint is taken at `footprint`. -/
def loopFrameFacts (footprint : Expr) : TacticM (Array (Expr × Expr)) := withMainContext do
  let context ← getLCtx
  let mut found : Array (Expr × Expr) := #[]
  for declaration in context do
    if declaration.isImplementationDetail || declaration.userName.hasMacroScopes then continue
    unless (context.findFromUserName? declaration.userName).any
      (·.fvarId == declaration.fvarId) do continue
    let type := (← instantiateMVars declaration.type).consumeMData
    if type.isAppOfArity ``LoopFrame 6 then
      found := found.push (declaration.toExpr, type)
    else if let .forallE _ domain body _ := type then
      unless body.isAppOfArity ``LoopFrame 6 do continue
      unless ← isDefEq domain (← inferType footprint) do continue
      found := found.push (mkApp declaration.toExpr footprint, body.instantiate1 footprint)
  return found.reverse

/-- The frame fact at `memory` whose byte slot holds `home`: its proof, type and the slot's
    index. -/
def loopFrameHome? (footprint memory home : Expr) :
    TacticM (Option (Expr × Expr × Nat)) := withMainContext do
  for (proof, type) in ← loopFrameFacts footprint do
    unless ← withNewMCtxDepth (isDefEq type.getAppArgs[2]! memory) do continue
    for (index, slot) in ← listEntries type.getAppArgs[4]! do
      let slot ← whnf slot
      unless slot.isAppOfArity ``LocalSlot.bytes 2 do continue
      if ← withNewMCtxDepth (isDefEq slot.appArg! home) then return some (proof, type, index)
  return none

/-- The remembered value of slot `index` in a `LoopFrame` type over `knownLocals`. -/
def loopFrameEntry? (type : Expr) (index : Nat) : MetaM (Option Expr) := do
  let remembered := type.getAppArgs[5]!.consumeMData
  unless remembered.isAppOfArity ``knownLocals 1 do return none
  return (← listEntries remembered.appArg!)[index]?.map (·.2)

/-- The address a stack value refers to, `.reference (.address home)`. -/
def loopAddressOf? (value : Expr) : MetaM (Option Expr) := do
  let value ← whnf value
  unless value.isAppOfArity ``Value.reference 1 do return none
  let reference ← whnf value.appArg!
  unless reference.isAppOfArity ``ManagedReference.address 1 do return none
  return some reference.appArg!

/-- The layout's `AggregateLayout.zeros` as literal values, one per field, in the form a proof
    writes them, such as `.i32 0`; none when a field's kind does not reduce to a value. -/
def loopZeroFields? (layout : Expr) : TermElabM (Option (Array Term)) := do
  let mut zeros : Array Term := #[]
  for (_, field) in ← listEntries (mkApp (mkConst ``CIL.AggregateLayout.fields) layout) do
    let zero ← whnf (mkApp (mkConst ``CIL.FieldLayout.zero) field)
    unless zero.getAppFn.constName?.any (·.getPrefix == ``CIL.Value) do return none
    -- Projections of the literal field, such as its width in a nested zero, are reduced.
    let zero := (← dsimp zero (← Simp.mkContext)).1
    zeros := zeros.push (← Term.exprToSyntax zero)
  return some zeros

/-- The position of the field of `layout` at `offset`. -/
def loopFieldAt? (layout : Expr) (offset : Nat) : MetaM (Option Nat) := do
  for (index, field) in ← listEntries (mkApp (mkConst ``CIL.AggregateLayout.fields) layout) do
    if (← literalNat? (mkApp (mkConst ``CIL.FieldLayout.offset) field)) == some offset then
      return some index
  return none

/-- An unused hypothesis name starting with `base`. -/
def loopFreshName (base : Name) : TacticM Ident := withMainContext do
  return mkIdent ((← getLCtx).getUnusedName base)

/-- Take the struct zeroing or field store at the goal's pc through the frame fact of its home,
    naming the memory it produces, the step and the frame after it; `facts` fetch the instruction
    and `layouts` are the layouts a zeroed struct may have. Returns whether a store was taken. -/
def loopFrameStore (facts : Array Term) (layouts : Array Expr) (footprint : Expr) :
    TacticM Bool := withMainContext do
  let saved ← saveState
  let some (source, _) ← loopGoalStates (← getMainTarget) | return false
  let some parts ← loopStateParts? source | return false
  let fetched ← observing? (loopFetch facts)
  saved.restore
  let some { op, found, instruction, .. } := fetched | return false
  let op ← whnfR op
  let memory := parts[3]!
  let stack ← listEntries parts[2]!
  let after ← loopFreshName `stored
  let stepped ← loopFreshName `storing
  let framed ← loopFreshName `storedFrame
  let store ← if op.isAppOfArity ``CIL.Op.setFieldAt 2 then do
      let some offset ← literalNat? op.appFn!.appArg! | return false
      let some (_, top) := stack[0]? | return false
      let some (_, below) := stack[1]? | return false
      let top ← whnf top
      unless top.isAppOfArity ``Value.scalar 1 do return false
      let some home ← loopAddressOf? below | return false
      let some (proof, type, index) ← loopFrameHome? footprint memory home | return false
      let some entry ← loopFrameEntry? type index | return false
      let some (layout, _) ← encodedStruct? entry | return false
      let some field ← loopFieldAt? layout offset | return false
      let valid ← layoutValidity layout
      let frame ← Term.exprToSyntax proof
      let value ← Term.exprToSyntax top.appArg!
      `(tactic| obtain ⟨$after, $stepped, $framed, -⟩ := CIL.Safety.LoopFrame.store_field $frame
        $(quote index) $valid $(quote field) $value)
    else if op.isAppOfArity ``CIL.Op.initAggregate 1 then do
      let some width ← literalNat? op.appArg! | return false
      let some (_, top) := stack[0]? | return false
      let some home ← loopAddressOf? top | return false
      let some (proof, _, index) ← loopFrameHome? footprint memory home | return false
      let sized ← layouts.filterM fun layout => do
        return (← literalNat? (mkApp (mkConst ``CIL.AggregateLayout.size) layout)) == some width
      let some layout := sized[0]? | return false
      let some zeros ← loopZeroFields? layout | return false
      let valid ← layoutValidity layout
      let frame ← Term.exprToSyntax proof
      let layoutTerm ← Term.exprToSyntax layout
      `(tactic| obtain ⟨$after, $stepped, $framed, -⟩ := CIL.Safety.LoopFrame.zero_aggregate
        $frame $(quote index) $layoutTerm [$zeros,*] (valid := $valid))
    else return false
  try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic store
  catch _ =>
    saved.restore
    return false
  -- Taking the store's step puts its memory in the goal, so the regathered facts are about it.
  let taken ← saveState
  try
    let found ← Term.exprToSyntax found
    let instruction ← Term.exprToSyntax instruction
    Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic|
      refine CIL.Safety.loop_terminates_next $found $instruction ($stepped _ _ _ _ _) ?_))
  catch _ => taken.restore
  return true

/-- The layouts each `AggregateLayout.encode` in `expression` names. -/
partial def encodedLayouts (expression : Expr) (found : Array Expr := #[]) : Array Expr :=
  let found := if expression.isAppOfArity ``AggregateLayout.encode 2 &&
      !found.contains expression.appFn!.appArg! then found.push expression.appFn!.appArg!
    else found
  match expression with
  | .app function argument => encodedLayouts argument (encodedLayouts function found)
  | .lam _ domain body _ | .forallE _ domain body _ =>
    encodedLayouts body (encodedLayouts domain found)
  | .letE _ type value body _ =>
    encodedLayouts body (encodedLayouts value (encodedLayouts type found))
  | .mdata _ inner | .proj _ _ inner => encodedLayouts inner found
  | _ => found

/-- The layouts each `AggregateLayout.encode` in the goal or a hypothesis names. -/
def contextLayouts : TacticM (Array Expr) := withMainContext do
  let mut found := encodedLayouts (← instantiateMVars (← getMainTarget))
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    found := encodedLayouts (← instantiateMVars declaration.type) found
  return found

/-- Walk a `LoopTerminates` goal as `mode` directs, with the `explicit` facts and those
    `gatherLoopFacts` finds, taking each struct zeroing and field store no fact steps through the
    frame lemmas and regathering the facts after it; a zeroed struct takes the first of
    `layouts` of its size. Fails as `tactic` naming the pc where it cannot go on. -/
partial def loopWalk (tactic : String) (mode : LoopStepping) (explicit : Array Term)
    (layouts : Array Expr) (footprint : Expr) (stepped : Bool := false) : TacticM Unit := do
  let facts ← gatherLoopFactGroups explicit
  let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
    (#[← `(CIL.truth)] ++ facts.core)
  loopSteps tactic mode facts prepared stepped
  if (← getGoals).isEmpty then return
  let position ← withMainContext do
    let some (source, _) ← loopGoalStates (← getMainTarget) | return none
    let some parts ← loopStateParts? source | return none
    literalNat? parts[0]!
  match mode with
  | .resume target => if position == some target then return
  -- A finish leaves a postcondition its facts do not prove as the goal.
  | _ => if position.isNone then return
  if ← loopFrameStore facts.core layouts footprint then
    return ← loopWalk tactic mode explicit layouts footprint true
  -- Where the walk stopped is the mode's stop, or a store no frame lemma takes.
  let stops : Lean.Name → Bool := match mode with
    | .finish => (· == ``CIL.Op.ret)
    | .advance => fun op => op == ``CIL.Op.call || op == ``CIL.Op.ret
    | _ => fun _ => false
  loopStuck tactic facts.all prepared stops

/-- The empty footprint, at which an entry frame proved for every footprint is taken. -/
def noFootprint : MetaM Expr := do
  mkAppOptM ``List.nil #[← mkAppM ``Prod #[mkConst ``Reference, mkConst ``Nat]]

/-- Step a `LoopTerminates` goal through fetched instructions up to the next call or return,
    with the optional facts and those `gatherLoopFacts` finds, taking each struct zeroing and
    field store on the way through the frame lemmas. Any other instruction it cannot step fails,
    naming the pc, the instruction and the residual step. -/
syntax "cil_loop_advance" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cil_loop_advance $[[$facts:term,*]]?) => do
    loopWalk "cil_loop_advance" .advance (facts.map (·.getElems) |>.getD #[])
      (← contextLayouts) (← noFootprint)

/-- Establish an exit path and its postcondition without choosing a fuel bound, taking each
    struct zeroing and field store on the way through the frame lemmas. The facts are the
    optional list and those `gatherLoopFacts` finds. A return whose results or postcondition the
    facts do not prove is left as the goal; any other step that cannot be taken fails, naming
    the pc, the instruction and the residual step. -/
syntax "cil_loop_finish" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cil_loop_finish $[[$facts:term,*]]?) => do
    loopWalk "cil_loop_finish" .finish (facts.map (·.getElems) |>.getD #[])
      (← contextLayouts) (← noFootprint)

/-- Continue a call's `LoopTerminates` continuation with its results and the frame after it:
    names the returned memory and the contract's output, substitutes an output the
    postcondition states as an equation, and, when the call's memory has a frame fact and the
    callee's footprint lies inside its own, proves the frame at the returned memory. -/
def loopCallContinue (contract : Expr) (memory : Expr) : TacticM Unit := withMainContext do
  let called ← loopFreshName `called
  let results ← loopFreshName `results
  let invoked ← loopFreshName `invoked
  let confined ← loopFreshName `confined
  let returns ← loopFreshName `returns
  let output ← loopFreshName `output
  let returned ← loopFreshName `returned
  -- A hygienic `rfl` would bind a name instead of substituting the results.
  let substitute := mkIdent `rfl
  evalTactic (← `(tactic|
    rintro $called:ident $results:ident ⟨_, $invoked:ident⟩ $confined:ident
      ⟨$output:ident, $substitute:ident, $returned:ident⟩))
  let unfold : Array Ident := match contract.getAppFn.constName? with
    | some name => #[mkIdent (`_root_ ++ name)]
    | none => #[]
  unless unfold.isEmpty do
    evalTactic (← `(tactic| try dsimp only [$[$unfold:ident],*] at $returned:ident ⊢))
  evalTactic (← `(tactic| try subst $output:ident))
  let saved ← saveState
  try
    withMainContext do
      let footprint ← mkFreshExprMVar (some (← mkAppM ``List
        #[← mkAppM ``Prod #[mkConst ``Reference, mkConst ``Nat]]))
      let frames ← loopFrameFacts footprint
      let some (proof, _) ← frames.findM? fun (_, type) =>
          withNewMCtxDepth (isDefEq type.getAppArgs[2]! memory)
        | throw (.error .missing m!"no frame at the call")
      let frame ← Term.exprToSyntax (← instantiateMVars proof)
      let framed ← loopFreshName `calledFrame
      let [main] ← getGoals | throw (.error .missing m!"expected one continuation")
      let sides ← Tactic.run main <| Term.withoutErrToSorry <| withoutRecover <| evalTactic
        (← `(tactic| have $framed := CIL.Safety.LoopFrame.after_confined $frame $confined
          (CIL.Safety.invoke_preserves_wellFormed _ _ _ _ _ _ _ ($frame).wellFormed $invoked)
          ?_ ?_))
      let continued :: conditions := sides | throw (.error .missing m!"no continuation")
      -- The callee's footprint must lie inside the frame's, below its watermark.
      for side in conditions do
        let open_ ← Tactic.run side <| Term.withoutErrToSorry <| withoutRecover <|
          evalTactic (← `(tactic| simp [$[$unfold:ident],*]))
        unless open_.isEmpty do throw (.error .missing m!"footprint not covered")
      setGoals [continued]
  catch _ => saved.restore

/-- Apply `holds`, the callee's contract at `input`, at the fetched loop call or at a
    `bind_call` site, with the optional facts and those `gatherLoopFacts` finds. The
    precondition is left as a goal unless `trivial` proves it; the continuation follows the call
    with its results and the frame after it, as `loopCallContinue` names them. Fails naming the
    pc and instruction when the goal is not at a call, and the residual when the call's arguments
    are not the contract's. -/
syntax "cil_loop_call" term:max term:max (" at " ident)? (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cil_loop_call $holds $input $[at $site:ident]? $[[$facts:term,*]]?) => do
    let facts ← gatherLoopFacts (facts.map (·.getElems) |>.getD #[])
    let instruction : Term ← match site with
      | some site => pure ⟨(mkIdent (site.getId ++ `call)).raw⟩
      | none => `(by cil_lookup [$[$facts:term],*])
    let some (source, _) ← withMainContext do loopGoalStates (← getMainTarget)
      | throwError "cil_loop_call: expected a `LoopTerminates` goal"
    let some parts ← withMainContext do loopStateParts? source
      | throwError "cil_loop_call: the source state does not reduce to a literal state"
    let saved ← saveState
    try
      Term.withoutErrToSorry <| withoutRecover <|
        evalTactic (← `(tactic| refine CIL.Safety.loop_terminates_call $holds $input
          (by cil_lookup [$[$facts:term],*]) $instruction
          (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_))
    catch error =>
      saved.restore
      withMainContext do
        let some position ← literalNat? parts[0]! | throw error
        let fetched ← observing? (loopFetch facts)
        saved.restore
        let some { op, .. } := fetched
          | throwError "cil_loop_call: cannot fetch the instruction at pc {position}"
        unless (← whnfR op).isAppOf ``CIL.Op.call do
          throwError "cil_loop_call: pc {position} is {op}, not a call; step to the call first \
            with `cil_loop_advance`"
        throwError "cil_loop_call: the call at pc {position} ({op}) does not take the contract's \
          arguments for this input, or is not the named site:{indentD error.toMessageData}"
    let holdsType ← withMainContext do
      whnfR (← inferType (← Term.elabTerm holds none))
    let contract := if holdsType.isAppOf ``MethodContract.Holds then
      holdsType.getAppArgs[2]! else holdsType
    let [permitted, continuation] ← getGoals
      | throwError "cil_loop_call: expected the precondition and the continuation"
    setGoals [continuation]
    loopCallContinue contract parts[3]!
    let remaining ← getGoals
    let open_ ← Tactic.run permitted (evalTactic (← `(tactic| try trivial)))
    setGoals (open_ ++ remaining)

/-- Step a `LoopTerminates` goal to the loop head of `hypothesis`, a statement that every head
    state of the loop (meeting its conditions) terminates, taking each struct zeroing and field
    store on the way through the frame lemmas, and apply `hypothesis` at the state with loop
    values `values`, the reached memory and its frame. Leaves the hypothesis's conditions, such
    as the invariant and the measure's decrease. Fails naming the pc where it cannot step, and
    the reached state when it is not the head's at `values`. -/
syntax "cil_loop_recurse " term:max term:max : tactic

elab_rules : tactic
  | `(tactic| cil_loop_recurse $hypothesis $values) => do
    let (target, layouts, footprint, conditions) ← withMainContext do
      let type ← instantiateMVars (← inferType (← Term.elabTerm hypothesis none))
      let (premises, _, conclusion) ← forallMetaTelescopeReducing type
      let some (state, _) ← loopGoalStates conclusion
        | throwError "cil_loop_recurse: {hypothesis} does not conclude `LoopTerminates`"
      let some parts ← loopStateParts? state
        | throwError "cil_loop_recurse: the head state of {hypothesis} is not a literal state"
      let some target ← literalNat? parts[0]!
        | throwError "cil_loop_recurse: the head pc of {hypothesis} is not a literal"
      let some head := premises[0]? | throwError "cil_loop_recurse: {hypothesis} takes no state"
      let stateType ← whnf (← inferType head)
      let footprint ← if stateType.isAppOfArity ``FrameState 6 then
          pure stateType.getAppArgs[0]!
        else mkAppOptM ``List.nil #[← mkAppM ``Prod #[mkConst ``Reference, mkConst ``Nat]]
      let layouts := encodedLayouts (← instantiateMVars (← whnfR stateType)) ++
        encodedLayouts type
      return (target, layouts, footprint, premises.size - 1)
    loopWalk "cil_loop_recurse" (.resume target) #[] layouts footprint
    let holes : Array Term ← (List.range conditions).toArray.mapM fun _ => `(?_)
    let (reached, memory) ← withMainContext do
      let reached ← instantiateMVars (← getMainTarget)
      let some (source, _) ← loopGoalStates reached
        | throwError "cil_loop_recurse: expected a `LoopTerminates` goal"
      let some parts ← loopStateParts? source
        | throwError "cil_loop_recurse: the reached state is not a literal state"
      return (reached, parts[3]!)
    let mismatch (error : Exception) : TacticM Unit :=
      throwError "cil_loop_recurse: the reached state is not the head of {hypothesis} at \
        {values}:{indentExpr reached}\n{error.toMessageData}"
    let saved ← saveState
    let memoryTerm ← withMainContext do Term.exprToSyntax memory
    let framed ← `(?headFrame)
    let applied ← `(tactic| refine $hypothesis ⟨$values, $memoryTerm, $framed⟩ $holes*)
    try Term.withoutErrToSorry <| withoutRecover <| evalTactic applied
    catch error => saved.restore; mismatch error
    -- The head's frame is the frame fact at the reached memory, up to its remembered values.
    let goals ← getGoals
    let some frameGoal ← goals.findM? fun goal => do
        return (← goal.getTag).eraseMacroScopes == `headFrame
      | throwError "cil_loop_recurse: the head state of {hypothesis} carries no frame"
    let closed ← frameGoal.withContext do
      let wanted ← instantiateMVars (← frameGoal.getType)
      let footprint := wanted.consumeMData.getAppArgs[0]?.getD (mkConst ``List.nil)
      for (proof, _) in ← loopFrameFacts footprint do
        let attempt ← saveState
        if ← isDefEq (← inferType proof) wanted then
          frameGoal.assign proof
          return true
        attempt.restore
      return false
    unless closed do
      let wanted ← frameGoal.withContext do instantiateMVars (← frameGoal.getType)
      throwError "cil_loop_recurse: no frame fact at the reached memory is the head's frame:\
        {indentExpr wanted}"
    setGoals (goals.filter (· != frameGoal))

end CIL.Safety
