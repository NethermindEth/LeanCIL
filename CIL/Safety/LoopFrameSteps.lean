import CIL.Safety.LoopFrameFields
import CIL.Safety.LoopCallerFacts
import CIL.Safety.LoopContract

/-!
# Loop tactics that carry frame facts

The tactics that walk a loop's `LoopTerminates` goals while keeping its `LoopFrame` current:
`cil_loop_advance` steps to a call or return, `cil_loop_finish` through a return,
`cil_loop_call` crosses a call through the callee's contract and continues with the frame after
it, and `cil_loop_recurse` steps to a loop head and applies the head's hypothesis there. Each walk
takes the struct zeroings, field stores and numeric local stores on its way through the frame's
lemmas. A memory a store or call produces is named in the context with its frame, so the next
step reads it like any other fact, and the caller-buffer facts (`Contents`, `Filled`, `Writable`)
are re-stated at it under their names. At a return `cil_loop_finish` names what leaving the frame
keeps and closes the postcondition's conjuncts those facts prove.
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

/-- The caller-buffer predicates whose facts follow the walk from memory to memory, each taking
    the memory first, with their arities. -/
def loopCarriedHeads : List (Name × Nat) := [(``Contents, 4), (``Filled, 5), (``Writable, 5)]

/-- Re-state each named hypothesis about a caller buffer at `memory` through `carry`, a term from
    its predicate and name, under the same name; a fact `carry` gives nothing for, or whose term
    does not elaborate, stays as it is. -/
def loopCarryFacts (memory : Expr) (carry : Name → Ident → TacticM (Option Term)) :
    TacticM Unit := do
  let carried ← withMainContext do
    let context ← getLCtx
    let mut found : Array (Name × Name) := #[]
    for declaration in context do
      if declaration.isImplementationDetail || declaration.userName.hasMacroScopes then continue
      unless (context.findFromUserName? declaration.userName).any
        (·.fvarId == declaration.fvarId) do continue
      let type := (← instantiateMVars declaration.type).consumeMData
      let some head := type.getAppFn.constName? | continue
      unless loopCarriedHeads.contains (head, type.getAppNumArgs) do continue
      unless ← withNewMCtxDepth (isDefEq (type.getArg! 0) memory) do continue
      found := found.push (head, declaration.userName)
    return found
  for (head, name) in carried do
    let some term ← carry head (mkIdent name) | continue
    let saved ← saveState
    -- A failed side proof inside `term` is logged, not thrown; `cil_strict` makes it fail here.
    try evalTactic (← `(tactic| cil_strict have $(mkIdent name):ident := $term))
    catch _ => saved.restore

/-- Carry the caller-buffer facts at `memory` across `below`, a store that keeps everything below
    the caller's watermark. -/
def loopCarryBelow (memory : Expr) (below : Ident) : TacticM Unit :=
  loopCarryFacts memory fun _ fact =>
    return some (← `(($fact).after_below $below (by cil_caller_allocation)))

/-- Carry the caller-buffer facts at `memory` across `confined`, a call confined to a footprint
    that the `unfold` definitions spell out: write authority always, contents when `omega` shows
    them apart from the footprint. -/
def loopCarryConfined (memory : Expr) (confined formed : Term) (unfold : Array Ident) :
    TacticM Unit :=
  loopCarryFacts memory fun head fact => do
    if head == ``Writable then return some (← `(($fact).after_confined $confined $formed))
    return some (← `(($fact).after_confined $confined $formed (by
      simp only [$[$unfold:ident],*, List.forall_mem_cons, List.not_mem_nil, false_implies,
        implies_true, and_true, Apart, Reference.element_allocation, Reference.element_offset,
        ne_eq, not_true_eq_false, false_or] <;> (try and_intros) <;> omega)))

/-- Take the struct zeroing, field store or numeric local store at the goal's pc through the frame
    fact of its home, naming the memory it produces, the step and the frame after it, and carry
    the caller-buffer facts to that memory; `facts` fetch the instruction and `layouts` are the
    layouts a zeroed struct may have. Returns whether a store was taken. -/
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
  let below ← loopFreshName `storedBelow
  -- A local store is a `storeLocal` fact the next step reads; a struct store is a whole step.
  let mut takesStep := true
  let store ← if op.isAppOfArity ``CIL.Op.setFieldAt 2 then do
      let some offset ← literalNat? op.appFn!.appArg! | return false
      let some (_, top) := stack[0]? | return false
      let some (_, address) := stack[1]? | return false
      let top ← whnf top
      unless top.isAppOfArity ``Value.scalar 1 do return false
      let some home ← loopAddressOf? address | return false
      let some (proof, type, index) ← loopFrameHome? footprint memory home | return false
      let some entry ← loopFrameEntry? type index | return false
      let some (layout, _) ← encodedStruct? entry | return false
      let some field ← loopFieldAt? layout offset | return false
      let valid ← layoutValidity layout
      let frame ← Term.exprToSyntax proof
      let value ← Term.exprToSyntax top.appArg!
      `(tactic| obtain ⟨$after, $stepped, $framed, $below⟩ := CIL.Safety.LoopFrame.store_field
        $frame $(quote index) $valid $(quote field) $value)
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
      `(tactic| obtain ⟨$after, $stepped, $framed, $below⟩ := CIL.Safety.LoopFrame.zero_aggregate
        $frame $(quote index) $layoutTerm [$zeros,*] (valid := $valid))
    else if op.isAppOfArity ``CIL.Op.setLocal 2 then do
      -- A narrowing store changes the value, which `LoopFrame.store` does not model.
      unless (← whnf op.appArg!).isAppOf ``Option.none do return false
      let some index ← literalNat? op.appFn!.appArg! | return false
      let some (_, top) := stack[0]? | return false
      let top ← whnf top
      unless top.isAppOfArity ``Value.scalar 1 do return false
      let frames ← loopFrameFacts footprint
      let some (proof, _) ← frames.findM? fun (_, type) => do
          unless ← withNewMCtxDepth (isDefEq type.getAppArgs[2]! memory) do return false
          let some slot := (← listEntries type.getAppArgs[4]!)[index]? | return false
          return (← whnf slot.2).isAppOfArity ``LocalSlot.bytes 2
        | return false
      takesStep := false
      let frame ← Term.exprToSyntax proof
      let value ← Term.exprToSyntax top.appArg!
      `(tactic| obtain ⟨$after, $stepped, $framed, $below⟩ := CIL.Safety.LoopFrame.store
        $frame $(quote index) $value rfl)
    else return false
  try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic store
  catch _ =>
    saved.restore
    return false
  -- The slots stay literal, as the next step's frame states them, so the next gathering finds it.
  evalTactic (← `(tactic| try dsimp only at $framed:ident))
  loopCarryBelow memory below
  -- Facts still at the caller's memory, such as a buffer the entry was handed, follow the frame.
  let caller ← withMainContext do
    return (← instantiateMVars (← inferType (← Term.elabTerm framed none))).getAppArgs[1]?
  if let some caller := caller then
    unless caller == memory do
      loopCarryConfined caller (← `(($framed).confined)) (← `((by assumption))) #[]
  unless takesStep do return true
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

/-- A frame fact at `memory` for any footprint, with its type, latest first. -/
def loopFrameAt? (memory : Expr) : TacticM (Option (Expr × Expr)) := withMainContext do
  let footprint ← mkFreshExprMVar (some (← mkAppM ``List
    #[← mkAppM ``Prod #[mkConst ``Reference, mkConst ``Nat]]))
  let frames ← loopFrameFacts footprint
  let found ← frames.findM? fun (_, type) =>
    withNewMCtxDepth (isDefEq type.getAppArgs[2]! memory)
  found.mapM fun (proof, type) => return (← instantiateMVars proof, ← instantiateMVars type)

/-- The entry's `setup` equation for frames entered from `caller`, in scope by any name. -/
def loopEntrySetup? (caller : Expr) : TacticM (Option Expr) := withMainContext do
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type ← instantiateMVars declaration.type
    let some (_, entry, _) := type.consumeMData.eq? | continue
    if entry.isAppOfArity ``enterFrame 3 && entry.appArg! == caller then
      return some declaration.toExpr
  return none

/-- The conjuncts of `goal`, a conjunction split as its `And`s nest, in order. -/
partial def loopConjuncts (goal : MVarId) : MetaM (Array MVarId) := do
  let target ← whnfR (← instantiateMVars (← goal.getType))
  unless target.isAppOfArity ``And 2 do return #[goal]
  let [left, right] ← goal.apply (mkConst ``And.intro) | return #[goal]
  return (← loopConjuncts left) ++ (← loopConjuncts right)

/-- Split a postcondition goal into its conjuncts, closing each that `close` proves and leaving
    the rest in order, each tagged by its place among all the conjuncts: `postcondition` when
    there is one, else `postcondition.part2` for the second, whichever others close. -/
def loopCloseConjuncts (close : TacticM Unit) : TacticM Unit := do
  let conjuncts ← loopConjuncts (← getMainGoal)
  tagNumbered `postcondition conjuncts
  let mut open_ := #[]
  for conjunct in conjuncts do
    setGoals [conjunct]
    let saved ← saveState
    try
      Term.withoutErrToSorry <| withoutRecover close
      unless (← getGoals).isEmpty do throwError "open"
    catch _ => saved.restore
    open_ := open_ ++ (← getGoals)
  setGoals open_.toList

/-- Close a `Contents` goal with the contents of a `Filled` hypothesis stating them. -/
def loopFilledContents : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless (← instantiateMVars decl.type).isAppOfArity ``Filled 5 do continue
    let contents ← mkAppM ``And.left #[decl.toExpr]
    if ← isDefEq (← inferType contents) (← goal.getType) then
      goal.assign contents
      replaceMainGoal []
      return
  throwError "no `Filled` hypothesis states these contents"

/-- Take the `ret` a finishing walk fetched, stepping it with `reading`, the facts it reads. A
    postcondition those facts prove is closed. Otherwise, with a frame fact at the return's memory
    and the entry's `setup`, name what leaving the frame keeps (`exitConfined`, `exitBelow`), carry
    the caller-buffer facts to the exit memory, and close each conjunct that a hypothesis, a
    carried `Filled` fact or the facts prove; the rest is left as the goal. -/
def loopFinishReturn (fetched : LoopFetched) (reading : Array Term) : TacticM Unit := do
  let some (source, _) ← withMainContext do loopGoalStates (← getMainTarget) | return
  let some parts ← withMainContext do loopStateParts? source | return
  withMainContext do
  let found ← Term.exprToSyntax fetched.found
  let instruction ← Term.exprToSyntax fetched.instruction
  evalTactic (← `(tactic| (
    apply CIL.Safety.loop_terminates_return $found $instruction
    · cil_checked_step_normalized [$[$reading:term],*]
    · rfl)))
  if (← getGoals).isEmpty then return
  withMainContext do
  -- Frame cleanup only after the facts fail, since unfolding `leaveFrame` first would hide it
  -- from a supplied fact about the exited frame's memory.
  let closed ← `(tactic| first
    | (simp [$[$reading:term],*]; done)
    | (simp [CIL.Safety.leaveFrame, CIL.NarrowKind.extend, $[$reading:term],*]; done))
  let saved ← saveState
  try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic closed
    return
  catch _ => saved.restore
  evalTactic (← `(tactic| try dsimp only))
  let memory := parts[3]!
  let mut extra : Array Term := #[]
  if let some (frame, frameType) ← loopFrameAt? memory then
    if let some setup ← loopEntrySetup? frameType.getAppArgs[1]! then
      let exitConfined ← loopFreshName `exitConfined
      let exitBelow ← loopFreshName `exitBelow
      let frameTerm ← Term.exprToSyntax frame
      let setupTerm ← Term.exprToSyntax setup
      let exited ← Term.exprToSyntax parts[1]!
      let left ← saveState
      try
        Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic|
          obtain ⟨$exitConfined, $exitBelow⟩ :=
            CIL.Safety.LoopFrame.leave $frameTerm $setupTerm $exited))
        loopCarryBelow memory exitBelow
        extra := extra.push exitConfined
      catch _ => left.restore
  withMainContext do
  let simplified ← `(tactic| first
    | (simp [$[$extra:term],*, $[$reading:term],*]; done)
    | (simp [CIL.Safety.leaveFrame, CIL.NarrowKind.extend, $[$extra:term],*,
        $[$reading:term],*]; done))
  -- A carried `Filled` fact proves the contents it starts with.
  loopCloseConjuncts (evalTactic (← `(tactic| with_reducible assumption)) <|>
    loopFilledContents <|> evalTactic simplified)

/-- Walk a `LoopTerminates` goal as `mode` directs, with the `explicit` facts and those
    `gatherLoopFacts` finds, taking each struct zeroing, field store and numeric local store no
    fact steps through the frame lemmas and regathering the facts after it; a zeroed struct takes
    the first of `layouts` of its size. A finishing walk takes the return through
    `loopFinishReturn`. Fails as `tactic` naming the pc where it cannot go on. -/
partial def loopWalk (tactic : String) (mode : LoopStepping) (explicit : Array Term)
    (layouts : Array Expr) (footprint : Expr) (stepped : Bool := false) : TacticM Unit := do
  let facts ← gatherLoopFactGroups explicit
  let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
    (#[← `(CIL.truth)] ++ facts.core)
  let stopped ← loopSteps tactic mode facts prepared stepped
    (finishReturn := some loopFinishReturn)
  if (← getGoals).isEmpty then return
  let position ← withMainContext do
    let some (source, _) ← loopGoalStates (← getMainTarget) | return none
    let some parts ← loopStateParts? source | return none
    literalNat? parts[0]!
  -- A goal the walk hands back is not a loop path, or shows its pc as a literal.
  let some _ := position | return
  loopLiteralGoal
  if let .resume target := mode then
    if position == some target then return
  -- A call or return an advance stops at is left for the next tactic.
  if mode == .advance && stopped.any fun op => callsCallee op || op == ``CIL.Op.ret then
    return
  if ← loopFrameStore facts.core layouts footprint then
    return ← loopWalk tactic mode explicit layouts footprint true
  -- Where the walk stopped is the mode's stop, or a store no frame lemma takes.
  let stops : Lean.Name → Bool := match mode with
    | .finish => (· == ``CIL.Op.ret)
    | .advance => fun op => callsCallee op || op == ``CIL.Op.ret
    | _ => fun _ => false
  loopStuck tactic facts.all prepared stops

/-- The empty footprint, at which an entry frame proved for every footprint is taken. -/
def noFootprint : MetaM Expr := do
  mkAppOptM ``List.nil #[← mkAppM ``Prod #[mkConst ``Reference, mkConst ``Nat]]

/-- Step a `LoopTerminates` goal through fetched instructions up to the next call or return,
    with the optional facts and those `gatherLoopFacts` finds, taking each struct zeroing, field
    store and numeric local store on the way through the frame lemmas. Any other instruction it
    cannot step fails, naming the pc, the instruction, the residual step and the fact missing. -/
syntax "cil_loop_advance" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cil_loop_advance $[[$facts:term,*]]?) => keepingTag do
    loopWalk "cil_loop_advance" .advance (facts.map (·.getElems) |>.getD #[])
      (← contextLayouts) (← noFootprint)

/-- Establish an exit path and its postcondition without choosing a fuel bound, taking each
    struct zeroing, field store and numeric local store on the way through the frame lemmas. The
    facts are the optional list and those `gatherLoopFacts` finds. At the return it names what
    leaving the frame keeps, `exitConfined` and `exitBelow`, carries the caller-buffer facts to the
    exit memory, closes each conjunct of the postcondition those facts prove, and leaves the
    rest as goals; any other step that cannot be taken fails, naming the pc, the instruction and
    the residual step. -/
syntax "cil_loop_finish" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cil_loop_finish $[[$facts:term,*]]?) => keepingTag do
    loopWalk "cil_loop_finish" .finish (facts.map (·.getElems) |>.getD #[])
      (← contextLayouts) (← noFootprint)

/-- The tactic that proves a frame side condition after a call: that each callee footprint entry
    lies inside the frame's footprint, or below the caller's watermark, from the `unfold`
    definitions, `facts`, arithmetic and `form` facts of the caller's memory. -/
def loopCallSide (unfold : Array Ident) (facts : Array Term) : TacticM Unit := do
  evalTactic (← `(tactic| (
    simp only [$[$unfold:ident],*, List.forall_mem_cons, List.not_mem_nil, false_implies,
      implies_true, and_true, List.mem_cons, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp,
      forall_eq, Within,
      Reference.element_allocation, Reference.element_offset, true_and, or_false, $[$facts:term],*]
    all_goals first
      | done
      | (and_intros <;> omega)
      | omega
      | exact CIL.Safety.Memory.WellFormed.form_bound (by with_reducible assumption)
          (by with_reducible assumption)
      | cil_caller_allocation)))

/-- Continue a call's `LoopTerminates` continuation with its results and the frame after it:
    names the returned memory, the contract's output, the callee's `WellFormed` (`calledFormed`)
    and, when the call's memory has a frame fact, the frame at the returned memory
    (`calledFrame`), carrying the caller-buffer facts across the call. Fails naming the side
    condition when the callee's footprint is not shown inside the frame's. -/
def loopCallContinue (contract : Expr) (memory : Expr) (facts : Array Term) :
    TacticM Unit := withMainContext do
  let called ← loopFreshName `called
  let results ← loopFreshName `results
  let invoked ← loopFreshName `invoked
  let confined ← loopFreshName `confined
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
    evalTactic (← `(tactic|
      try dsimp only [$[$unfold:ident],*] at $returned:ident $confined:ident ⊢))
  evalTactic (← `(tactic| try subst $output:ident))
  let some (proof, _) ← loopFrameAt? memory | return
  let frame ← Term.exprToSyntax proof
  let formed ← loopFreshName `calledFormed
  evalTactic (← `(tactic| have $formed := CIL.Safety.invoke_preserves_wellFormed _ _ _ _ _ _ _
    ($frame).wellFormed $invoked))
  -- Facts about caller buffers at the call's memory follow it across the call.
  loopCarryConfined memory confined (← `(($frame).wellFormed)) unfold
  let framed ← loopFreshName `calledFrame
  let [main] ← getGoals | throwError "cil_loop_call: expected one continuation"
  let sides ← Tactic.run main <| Term.withoutErrToSorry <| withoutRecover <| evalTactic
    (← `(tactic| have $framed := CIL.Safety.LoopFrame.after_confined $frame $confined $formed
      ?_ ?_))
  let continued :: conditions := sides | throwError "cil_loop_call: no continuation"
  let names := #["inside the frame's footprint", "below the caller's watermark"]
  for (side, index) in conditions.zipIdx do
    let open_ ← try Tactic.run side <| Term.withoutErrToSorry <| withoutRecover <|
        loopCallSide unfold facts
      catch _ => pure [side]
    unless open_.isEmpty do
      let goal ← instantiateMVars (← side.getType)
      throwError "cil_loop_call: the frame after the call needs each callee footprint entry \
        {names[index]!}, which the facts do not prove:{indentExpr goal}\nState the arithmetic \
        it needs, or a `form` fact of the caller's memory for its reference, in the context or \
        the fact list."
  setGoals [continued]
  evalTactic (← `(tactic| try simp only [List.set, CIL.Safety.localResult] at $framed:ident))

/-- Apply `holds`, the callee's contract at `input`, at the fetched loop call or at a
    `bind_call` site, with the optional facts and those `gatherLoopFacts` finds. The
    precondition is left as a goal unless `trivial` or a hypothesis proves it; the continuation
    follows the call with its results and the frame after it, as `loopCallContinue` names them.
    Fails naming the pc and instruction when the goal is not at a call, the fact an argument
    check needs when the call does not step, the contract's arguments and the stack when they
    differ, and the side condition when the frame after the call cannot be proved. -/
syntax "cil_loop_call" term:max term:max (" at " ident)? (" [" term,* "]")? : tactic

/-- The contract a `MethodContract.Holds` proof's type names, and the tag of its callee's
    precondition (`preconditionTag`). -/
def loopHeldContract (holds : Term) : TacticM (Expr × Name) := withMainContext do
  let type ← whnfR (← inferType (← Term.elabTerm holds none))
  let contract := if type.isAppOf ``MethodContract.Holds then type.getAppArgs[2]! else type
  return (contract, preconditionTag type)

/-- Fail for a call `cil_loop_call` could not cross at `position`: naming the missing fact when
    the step's argument checks do not reduce, and otherwise the contract's arguments for `input`
    beside the stack. -/
def loopCallFailure (holds input : Term) (facts : Array Term) (position : Nat)
    (stack : Expr) : TacticM Unit := withMainContext do
  let saved ← saveState
  -- The facts are normalised first, so the fetched step's context has them.
  let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
    (#[← `(CIL.truth)] ++ facts)
  let fetched ← observing? (loopFetch facts)
  let some { op, step, .. } := fetched
    | saved.restore
      throwError "cil_loop_call: cannot fetch the instruction at pc {position}"
  unless ((← whnfR op).getAppFn.constName?.map callsCallee).getD false do
    saved.restore
    throwError "cil_loop_call: pc {position} is {op}, not a call; step to the call first with \
      `cil_loop_advance`"
  let residual ← stepResidual step prepared
  saved.restore
  -- A call whose step still mentions a check is stuck on a fact, not on the contract.
  if let some goals := residual then
    let checking := goals.any fun goal => (goal.find? fun term =>
      [``form, ``formValue, ``checkedValue, ``SpanView.validate, ``add, ``loadLocal].any
        term.isConstOf).isSome
    if checking then
      throwError "cil_loop_call: the call at pc {position} ({op}) does not step: its argument \
        checks reduce to\
        {indentD (MessageData.joinSep (goals.toList.map (m!"{loopLiteralSums ·}")) "\n")}\n\
        Supply {← loopMissingHint goals}."
  let (contract, _) ← loopHeldContract holds
  let wanted ← withMainContext do
    let inputExpr ← Term.elabTerm input none
    -- The contract's argument list, reduced as far as its definition goes.
    withTransparency .default <| reduce (skipTypes := true)
      (← instantiateMVars (← mkAppM ``MethodContract.args #[contract, inputExpr]))
  throwError "cil_loop_call: the call at pc {position} ({op}) does not take the contract's \
    arguments for this input, or is not the named site. The contract passes\
    {indentExpr (loopLiteralSums wanted)}\n\
    and the stack holds{indentExpr (loopLiteralSums stack)}"

elab_rules : tactic
  | `(tactic| cil_loop_call $holds $input $[at $site:ident]? $[[$facts:term,*]]?) =>
    keepingTag do
    let explicit := facts.map (·.getElems) |>.getD #[]
    let groups ← gatherLoopFactGroups explicit
    -- The call checks its arguments, so it reads the reference facts besides the core.
    let references ← assertLoopFacts `callerFact groups.references groups.known
    let facts := groups.core ++ references
    let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
      (#[← `(CIL.truth)] ++ facts)
    let instruction : Term ← match site with
      | some site => pure ⟨(mkIdent (site.getId ++ `call)).raw⟩
      | none => `(by cil_lookup [$[$facts:term],*])
    let some (source, _) ← withMainContext do loopGoalStates (← getMainTarget)
      | throwError "cil_loop_call: expected a `LoopTerminates` goal{← obligationNote}"
    let some parts ← withMainContext do loopStateParts? source
      | throwError "cil_loop_call: the source state does not reduce to a literal state"
    let saved ← saveState
    try
      Term.withoutErrToSorry <| withoutRecover <|
        evalTactic (← `(tactic| refine CIL.Safety.loop_terminates_call $holds $input
          (by cil_lookup [$[$facts:term],*]) $instruction
          (by cil_checked_step_normalized [$[$prepared:term],*]) (by rfl) ?_ ?_))
    catch error =>
      saved.restore
      let some position ← withMainContext do literalNat? parts[0]! | throw error
      loopCallFailure holds input groups.all position parts[2]!
    let (contract, precondition) ← loopHeldContract holds
    let [permitted, continuation] ← getGoals
      | throwError "cil_loop_call: expected the precondition and the continuation"
    setGoals [continuation]
    loopCallContinue contract parts[3]! explicit
    let remaining ← getGoals
    let unfold : Array Ident := match contract.getAppFn.constName? with
      | some name => #[mkIdent (`_root_ ++ name)]
      | none => #[]
    let open_ ← Tactic.run permitted (evalTactic (← `(tactic| (
      try dsimp only [$[$unfold:ident],*]
      try first | trivial | assumption))))
    for goal in open_ do goal.setTag precondition
    setGoals (open_ ++ remaining)

/-- Close `goal`, a head state's frame, with a frame fact at the reached memory: one of its type,
    or one whose span and reference slots differ from it, through `LoopFrame.set_local`. -/
def loopCloseHeadFrame (goal : MVarId) : TacticM Bool := goal.withContext do
  let wanted ← instantiateMVars (← goal.getType)
  let footprint := wanted.consumeMData.getAppArgs[0]?.getD (mkConst ``List.nil)
  let frames ← loopFrameFacts footprint
  for (proof, _) in frames do
    let attempt ← saveState
    if ← isDefEq (← inferType proof) wanted then
      goal.assign proof
      return true
    attempt.restore
  let wantedSlots := (← listEntries wanted.consumeMData.getAppArgs[4]!).map (·.2)
  if wantedSlots.isEmpty then return false
  for (proof, type) in frames do
    let haveSlots := (← listEntries type.getAppArgs[4]!).map (·.2)
    unless haveSlots.size == wantedSlots.size do continue
    let mut term ← Term.exprToSyntax proof
    let mut usable := true
    for index in [:wantedSlots.size] do
      let slot := wantedSlots[index]!
      let other := haveSlots[index]!
      if ← withNewMCtxDepth (isDefEq slot other) then continue
      if (← whnf slot).isAppOf ``LocalSlot.bytes || (← whnf other).isAppOf ``LocalSlot.bytes then
        usable := false
        break
      let slotTerm ← Term.exprToSyntax slot
      term ← `(CIL.Safety.LoopFrame.set_local $term $(quote index) $slotTerm)
    unless usable do continue
    let attempt ← saveState
    try
      let value ← Term.withoutErrToSorry <| Term.elabTermEnsuringType term wanted
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      if value.hasExprMVar then throwError "the frame is not closed"
      goal.assign value
      return true
    catch _ => attempt.restore
  return false

/-- Step a `LoopTerminates` goal to the loop head of `hypothesis`, a statement that every head
    state of the loop (meeting its conditions) terminates, with the optional facts and those
    `gatherLoopFacts` finds, taking each struct zeroing, field store and numeric local store on
    the way through the frame lemmas, and apply `hypothesis` at the state with loop values
    `values`, the reached memory and its frame. Leaves the hypothesis's conditions, tagged by
    `recurseConditionTags`, such as `invariant` and `measure`. Fails naming the pc where it
    cannot step, and the reached state when it is not the head's at `values`. -/
syntax "cil_loop_recurse " term:max term:max (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cil_loop_recurse $hypothesis $values $[[$facts:term,*]]?) => do
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
    loopWalk "cil_loop_recurse" (.resume target) (facts.map (·.getElems) |>.getD #[]) layouts
      footprint
    let tags := recurseConditionTags conditions
    let holeNames ← (List.range tags.size).toArray.mapM fun index =>
      MonadQuotation.addMacroScope (Name.mkSimple s!"condition{index}")
    let holes : Array Term ← holeNames.mapM fun name => `(?$(mkIdent name))
    let (reached, memory) ← withMainContext do
      let reached ← instantiateMVars (← getMainTarget)
      let some (source, _) ← loopGoalStates reached
        | throwError "cil_loop_recurse: expected a `LoopTerminates` goal{← obligationNote}"
      let some parts ← loopStateParts? source
        | throwError "cil_loop_recurse: the reached state is not a literal state"
      return (reached, parts[3]!)
    let mismatch (error : Exception) : TacticM Unit :=
      throwError "cil_loop_recurse: the reached state is not the head of {hypothesis} at \
        {values}:{indentExpr (loopLiteralSums reached)}\n{error.toMessageData}"
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
    unless ← loopCloseHeadFrame frameGoal do
      let wanted ← frameGoal.withContext do instantiateMVars (← frameGoal.getType)
      throwError "cil_loop_recurse: no frame fact at the reached memory is the head's frame:\
        {indentExpr (loopLiteralSums wanted)}"
    setGoals (goals.filter (· != frameGoal))
    for goal in goals do
      if let some index := holeNames.idxOf? (← goal.getTag) then goal.setTag tags[index]!

end CIL.Safety
