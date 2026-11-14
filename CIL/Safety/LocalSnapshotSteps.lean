import CIL.Safety.LocalSnapshots
import CIL.Safety.LoopFrameSteps
import CIL.Safety.CallingTransport
import CIL.TermAccess

/-!
# Checked stepping with remembered locals

The optional snapshot forms of `cil_checked_steps` and `cil_contract_steps` carry
`LocalSnapshots` through numeric local stores and use them for loads. Importing this module
enables these forms without requiring snapshot support in the ordinary tactics' dependencies.
A store names the memory it produces and the evidence about it, and the contract form restates
the caller facts of the context at that memory, as the loop tactics of
`CIL.Safety.LoopFrameSteps` do, and prepares its step facts again there. The contract form also
stops after a step count.
-/

namespace CIL.Safety

/-- Writing bytes keeps every declared local's writable home and slot identity. -/
theorem CompleteWritableHomes.after_write {before after : Memory} {lower : Nat} {kinds slots}
    (homes : CompleteWritableHomes before lower kinds slots)
    {reference : Reference} {bytes : List (BitVec 8)} {alignment : Nat}
    (written : write before reference bytes alignment = .ok after) :
    CompleteWritableHomes after lower kinds slots :=
  ⟨homes.writable.after_write written, homes.complete⟩

#print axioms CompleteWritableHomes.after_write

/-- A successful write preserves every previously justified access, including another home. -/
theorem snapshot_access_after_write {before after : Memory} {target reference : Reference}
    {bytes : List (BitVec 8)} {writeAlignment width alignment : Nat} {writing : Bool}
    (ready : access before reference width alignment writing = .ok ())
    (written : write before target bytes writeAlignment = .ok after) :
    access after reference width alignment writing = .ok () := by
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  exact (requirements.after_write written).access

#print axioms snapshot_access_after_write

/-- Leading slots without a byte home keep the homes after them writable above the same
    bound; each such slot is declared as a reference. -/
theorem WritableHomes.after_skipped {memory : Memory} {lower : Nat} {kinds slots}
    (homes : WritableHomes memory lower kinds slots) (skipped : List LocalSlot)
    (notHomes : ∀ slot ∈ skipped, ∀ stored reference, slot ≠ .bytes stored reference) :
    WritableHomes memory lower
      (skipped.map (fun _ => CIL.LocalKind.reference) ++ kinds) (skipped ++ slots) := by
  induction skipped with
  | nil => exact homes
  | cons slot rest continued =>
    exact .skip (notHomes slot (by simp))
      (continued fun other member => notHomes other (by simp [member]))

#print axioms WritableHomes.after_skipped

/-- A declared local's home stays writable in a later memory that retains the access of the
    memory the homes were stated in, and is found past `skipped` leading slots. -/
theorem CompleteWritableHomes.home_retained {entered current : Memory} {lower watermark : Nat}
    {kinds slots} (homes : CompleteWritableHomes entered lower kinds slots)
    (formed : entered.WellFormed) (retained : AccessBelow watermark entered current)
    (old : entered.nextIdentity ≤ watermark) (skipped : List LocalSlot) (index : Nat)
    (kind : CIL.LocalKind) (specified : kinds[index]? = some kind) :
    ∃ reference, (skipped ++ slots)[skipped.length + index]? = some (.bytes kind reference) ∧
      lower ≤ reference.allocation ∧
      access current reference (localWidth kind) 1 true = .ok () := by
  obtain ⟨reference, slot, bound, ready⟩ := homes.home_at index kind specified
  refine ⟨reference, ?_, bound,
    retained.access ready (Nat.lt_of_lt_of_le (formed.access_bound ready) old)⟩
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact slot

#print axioms CompleteWritableHomes.home_retained

/-- A numeric store whose step is already known, to the memory `after`, gives the evidence of
    `LocalSnapshots.store` about that memory. -/
theorem LocalSnapshots.store_at {body : CIL.Method} {pc index target : Nat}
    {args stack values : List Value} {frame nextFrame : Frame} {entered memory after : Memory}
    {boundary : Nat} {kinds} {known : Nat → Option CIL.Value}
    (snapshots : LocalSnapshots memory frame.locals known)
    (homes : WritableHomes entered boundary kinds frame.locals) (formed : memory.WellFormed)
    (kind : CIL.LocalKind) (home : Reference) (value : CIL.Value) (number : Nat)
    (fits : localNumber kind value = .ok number)
    (slot : frame.locals[index]? = some (.bytes kind home))
    (ready : access memory home (localWidth kind) 1 true = .ok ())
    (stored : step body (.stloc index) pc args frame (.scalar value :: stack) memory =
      .ok (.next target values nextFrame after)) :
    LocalSnapshots after frame.locals (rememberLocal known index (localResult kind value)) ∧
      after.WellFormed ∧ MemoryBelow boundary memory after ∧
      AccessBelow memory.nextIdentity memory after ∧
      write memory home (numberBytes number (localWidth kind)) 1 = .ok after := by
  obtain ⟨result, stepped, remembered, wellFormed, below, retained, written⟩ :=
    snapshots.store (body := body) (pc := pc) (args := args) (stack := stack) homes formed
      kind home value number fits slot ready
  rw [stepped] at stored
  cases stored
  exact ⟨remembered, wellFormed, below, retained, written⟩

#print axioms LocalSnapshots.store_at

open Lean Elab Tactic Meta

initialize Lean.registerTraceClass `CIL.snapshots

/-- The reader the snapshot forms name when a term does not have the shape they read. -/
private def snapshotReader : String := "snapshot stepping (cil_checked_steps, cil_contract_steps)"

/-- Close an existing snapshot obligation using checked facts and concrete local encodings. -/
private def solveSnapshotPremise (goal : MVarId) (facts : Array Term) : TacticM Unit := do
  let remaining ← Tactic.run goal <| evalTactic (← `(tactic| cil_strict
    (first
      | assumption
      | (apply CompleteWritableHomes.writable; assumption)
      | (apply NumericHomes.writable; assumption)
      | rfl
      | cil_lookup [$facts,*]
      | (simp [localNumber, localResult, rememberLocal, $[$facts:term],*]; done))))
  unless remaining.isEmpty do throwError "A local snapshot premise was not established"

/-- Assert a proved fact in the current continuation and return its local name: fresh, or
    with `named` the accessible name `base` itself, which then refers to this fact. -/
private def assertSnapshotFact (base : Name) (proof : Expr) (named := false) :
    TacticM Term := withMainContext do
  let type ← inferType proof
  let named := named && !base.hasMacroScopes
  unless named do
    for declaration in ← getLCtx do
      if declaration.type == type then return ← Term.exprToSyntax declaration.toExpr
  let name ← if named then pure base else mkFreshUserName base
  let (_, goal) ← (← (← getMainGoal).assert name type proof).intro1P
  replaceMainGoal [goal]
  return mkIdent name

/-- Carry access facts through a proved write; byte-value facts are deliberately not carried. -/
private def preserveSnapshotAccess (written : Term) : TacticM Unit := withMainContext do
  let writeProof ← Term.elabTerm written none
  let declarations := (← getLCtx).decls.toArray.filterMap id
  for declaration in declarations do
    let some (_, accessTerm, _) := (← instantiateMVars declaration.type).consumeMData.eq?
      | continue
    unless accessTerm.isAppOf ``access do continue
    let saved ← saveState
    try
      let proof ← mkAppM ``snapshot_access_after_write #[declaration.toExpr, writeProof]
      discard <| assertSnapshotFact `snapshotAccess proof
    catch _ => saved.restore

/-- The names of the memory a store produces, its step and the evidence about that memory. -/
private def snapshotStoreBases : Array String :=
  #["storedLocal", "storingLocal", "localSnapshots", "localFormed", "localBelow", "localAccess",
    "localWrite"]

/-- Whether `name` is one a store gives its own evidence, with or without a numeric suffix. -/
private def isSnapshotStoreName : Name → Bool
  | .str .anonymous text =>
    snapshotStoreBases.any fun base => text == base || text.startsWith (base ++ "_")
  | _ => false

/-- Retain only generic facts whose exact current memory is the source of this write, each
    restated after the write under the name it has. One store's own evidence keeps its name
    for that store, and reaches later memories under a fresh name. -/
private def preserveSnapshotFacts (written below : Term) : TacticM Unit := withMainContext do
  let writeProof ← Term.elabTerm written none
  let belowProof ← Term.elabTerm below none
  let declarations := (← getLCtx).decls.toArray.filterMap id
  for declaration in declarations do
    let saved ← saveState
    try
      let type := (← instantiateMVars declaration.type).consumeMData
      let proof ← if type.isAppOfArity ``CompleteWritableHomes 4 then
          mkAppM ``CompleteWritableHomes.after_write #[declaration.toExpr, writeProof]
        else if type.isAppOfArity ``ValidCall 3 then
          mkAppM ``ValidCall.after_write #[declaration.toExpr, writeProof]
        else if type.isAppOfArity ``MemoryBelow 3 then
          mkAppM ``MemoryBelow.trans #[declaration.toExpr, belowProof]
        else if type.isAppOfArity ``AccessBelow 3 then do
          let watermark ← argumentAt snapshotReader type 0
          let next ← mkAppM ``write_preserves_access_below #[writeProof, watermark]
          mkAppM ``AccessBelow.trans #[declaration.toExpr, next]
        else continue
      discard <| assertSnapshotFact declaration.userName proof
        (named := !isSnapshotStoreName declaration.userName)
    catch error =>
      saved.restore
      trace[CIL.snapshots] "{declaration.userName}: {error.toMessageData}"

/-- The transport of `fact`, a `read` or `form` equation of `memory`, across `below`, a store
    that keeps that memory below its watermark; none for any other statement. -/
private def snapshotCarried? (memory : Expr) (below : Ident) (fact : Term) (type : Expr) :
    TacticM (Option Term) := do
  let some (_, operation, _) := type.consumeMData.eq? | return none
  let reads := operation.isAppOfArity ``read 4
  unless reads || operation.isAppOfArity ``form 2 do return none
  let some stated := argument? operation 0 | return none
  unless ← withNewMCtxDepth (isDefEq stated memory) do return none
  if reads then
    return some (← `((MemoryBelow.read $below _ (by cil_caller_allocation) _ _).trans $fact))
  return some (← `((MemoryBelow.form $below _ (by cil_caller_allocation)).trans $fact))

/-- Restate each named read or formed reference of `memory` below the watermark of `below`, a
    store that keeps that memory, at the memory after it and under the same name. A fact
    whose reference is not shown older than the watermark stays as it is. -/
private def carrySnapshotReads (memory : Expr) (below : Ident) : TacticM Unit := do
  let carried ← withMainContext do
    let context ← getLCtx
    let mut found : Array (Ident × Term) := #[]
    for declaration in context do
      if declaration.isImplementationDetail || declaration.userName.hasMacroScopes then continue
      unless (context.findFromUserName? declaration.userName).any
        (·.fvarId == declaration.fvarId) do continue
      let fact := mkIdent declaration.userName
      let type ← instantiateMVars declaration.type
      if let some transport ← snapshotCarried? memory below fact type then
        found := found.push (fact, transport)
    return found
  for (fact, transport) in carried do
    let saved ← saveState
    try evalTactic (← `(tactic| cil_strict have $fact:ident := $transport))
    catch _ => saved.restore

/-- The slots a frame's locals list before `slots`, with the layout equation that states
    them when the list itself does not reduce to them. -/
private def snapshotLeadingSlots (locals slots : Expr) :
    TacticM (Array Expr × Option Expr) := withMainContext do
  let leading (layout : Expr) : MetaM (Option (Array Expr)) := do
    let mut skipped := #[]
    let mut rest := layout
    for _ in [:64] do
      if ← withNewMCtxDepth (isDefEq rest slots) then return some skipped
      let exposed ← whnf rest
      let some #[_, slot, following] := argumentsOf? exposed ``List.cons 3 | return none
      skipped := skipped.push slot
      rest := following
    return none
  if let some skipped ← leading locals then return (skipped, none)
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let some (_, stated, layout) := (← instantiateMVars declaration.type).consumeMData.eq?
      | continue
    unless ← withNewMCtxDepth (isDefEq stated locals) do continue
    if let some skipped ← leading layout then return (skipped, some declaration.toExpr)
  throwError "The homes cover no suffix of the frame's locals"

/-- Evidence in scope that `current` retains the access of `entered`, as `AccessBelow`. -/
private def snapshotRetainedAccess (entered current : Expr) : TacticM Term := withMainContext do
  let declarations := (← getLCtx).decls.toArray.filterMap id
  let linked (head : Name) : MetaM (Option Expr) := do
    for declaration in declarations.reverse do
      let type := (← instantiateMVars declaration.type).consumeMData
      let some #[_, source, target] := argumentsOf? type head 3 | continue
      unless ← withNewMCtxDepth (isDefEq source entered) do continue
      unless ← withNewMCtxDepth (isDefEq target current) do continue
      return some declaration.toExpr
    return none
  if let some retained ← linked ``AccessBelow then return ← Term.exprToSyntax retained
  let some preserved ← linked ``MemoryBelow
    | throwError "No evidence that the current memory retains the homes' access"
  -- Stated as `AccessBelow`, the link follows each later store under one watermark.
  assertSnapshotFact `snapshotRetained (← mkAppM ``MemoryBelow.accessBelow #[preserved])

/-- Close a home's kind lookup `kinds[index]? = some _` with a supplied fact that states it, or
    that states the numeric spec at that index. -/
syntax "cil_snapshot_kind" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| cil_snapshot_kind [$facts:term,*]) => do
    for fact in facts.getElems do
      let saved ← saveState
      try
        evalTactic (← `(tactic| cil_strict first
          | exact $fact
          | exact numericKinds_getElem? $fact))
        return
      catch _ => saved.restore
    throwError "No supplied fact states the local's kind at this index"

/-- Discover a selected writable home without exposing the concrete frame's slot list. Homes
    stated at an earlier memory, or after leading slots without byte homes, are used when the
    context shows that the current memory retains their access. A kind lookup that does not
    compute, over opaque kinds or at a symbolic index, is closed from `facts`; a symbolic index
    is taken only when no leading slot is skipped. -/
private def prepareSnapshotHome (memory frame index : Expr) (facts : Array Term) :
    TacticM Unit := withMainContext do
  let locals ← mkAppM ``Frame.locals #[frame]
  let declarations := (← getLCtx).decls.toArray.filterMap id
  for declaration in declarations.reverse do
    let saved ← saveState
    try
      let type := (← instantiateMVars declaration.type).consumeMData
      let proof ← if type.isAppOfArity ``NumericHomes 4 then
          mkAppM ``NumericHomes.complete #[declaration.toExpr]
        else if type.isAppOfArity ``CompleteWritableHomes 4 then pure declaration.toExpr
        else continue
      -- An untyped `have` declares its fact at an assigned metavariable, which has no arguments.
      let type := (← instantiateMVars (← inferType proof)).consumeMData
      let some #[entered, _, _, slots] := argumentsOf? type ``CompleteWritableHomes 4
        | throwError "{snapshotReader}: expected complete writable homes, but found\
            {indentExpr type}"
      let home := mkIdent (← mkFreshUserName `snapshotHome)
      let slot := mkIdent (← mkFreshUserName `snapshotSlot)
      let bound := mkIdent (← mkFreshUserName `snapshotBound)
      let ready := mkIdent (← mkFreshUserName `snapshotReady)
      let current ← withNewMCtxDepth (isDefEq entered memory)
      if current && (← withNewMCtxDepth (isDefEq slots locals)) then
        let homes ← assertSnapshotFact `snapshotHomes proof
        let index ← Term.exprToSyntax index
        evalTactic (← `(tactic| obtain ⟨$home, $slot, $bound, $ready⟩ :=
          CompleteWritableHomes.home_at $homes $index _
            (by first | rfl | cil_snapshot_kind [$facts,*])))
        return
      let (skipped, layout) ← snapshotLeadingSlots locals slots
      let position ← getNatValue? (← whnfR index)
      if position.isNone && !skipped.isEmpty then
        throwError "The local index is not a numeral and leading slots are skipped"
      unless position.all (skipped.size ≤ ·) do throwError "The local precedes the homes"
      let indexTerm ← Term.exprToSyntax index
      -- A symbolic index is its own position among the homes, which then skip no slot.
      let inner : Term := match position with
        | some position => Syntax.mkNumLit (toString (position - skipped.size))
        | none => indexTerm
      let outer : Term := match position with
        | some position => Syntax.mkNumLit (toString position)
        | none => indexTerm
      let retained ← if current then
          `(term| (MemoryBelow.refl (Memory.nextIdentity $(← Term.exprToSyntax entered))
            $(← Term.exprToSyntax entered)).accessBelow)
        else snapshotRetainedAccess entered memory
      let homes ← Term.exprToSyntax proof
      let skippedTerms ← skipped.mapM (Term.exprToSyntax ·)
      let layoutTerm ← layout.mapM (Term.exprToSyntax ·)
      -- A statement over the leading slots is restated over the frame's own locals.
      let restate (statement : Term) : TacticM (TSyntax `tactic) := do
        -- The position `[].length + index` of a symbolic index is `index` only by rewriting.
        let stated ← if position.isSome then `(tactic| exact $statement) else
          `(tactic| simpa only [List.nil_append, List.length_nil, Nat.zero_add] using $statement)
        match layoutTerm with
        | some layout => `(tactic| first
            | $stated:tactic
            | (rw [$layout:term]; $stated:tactic))
        | none => pure stated
      let localsTerm ← Term.exprToSyntax locals
      let raw := mkIdent (← mkFreshUserName `snapshotSlot)
      evalTactic (← `(tactic| cil_strict obtain ⟨$home, $raw, $bound, $ready⟩ :=
        CompleteWritableHomes.home_retained $homes (by assumption) $retained
          (by first | exact Nat.le_refl _ | assumption | omega) [$skippedTerms,*] $inner _
          (by first | rfl | cil_snapshot_kind [$facts,*])))
      let kind ← withMainContext do
        let found ← instantiateMVars (← inferType (← Term.elabTerm raw none))
        let some (_, _, selected) := found.eq? | throwError "Unexpected home lookup"
        let some kind := (lastArgument? selected).bind (argument? · 0)
          | throwError "{snapshotReader}: expected a byte slot, but found{indentExpr selected}"
        Term.exprToSyntax (← whnf kind)
      evalTactic (← `(tactic| cil_strict have $slot :
          ($localsTerm)[$outer]? = some (LocalSlot.bytes $kind $home) := by
            $(← restate raw):tactic))
      unless skipped.isEmpty do
        let (covered, statement) ← withMainContext do
          let covered ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm
            (← `(term| WritableHomes.after_skipped
              (CompleteWritableHomes.writable $homes) [$skippedTerms,*]
              (by first
                | (simp; done)
                | (simp only [List.mem_singleton, forall_eq]; assumption)))) none
          let stated ← instantiateMVars (← inferType covered)
          pure (← Term.exprToSyntax covered, ← Term.exprToSyntax
            (mkAppN stated.getAppFn (stated.getAppArgs.set! 3 locals)))
        let writable := mkIdent (← mkFreshUserName `snapshotHomes)
        evalTactic (← `(tactic| cil_strict have $writable : $statement := by
          $(← restate covered):tactic))
      return
    catch error =>
      saved.restore
      trace[CIL.snapshots] "{error.toMessageData}"

/-- The names a store takes for the memory it produces, its step, the snapshots, formation,
    `MemoryBelow`, `AccessBelow` and write about that memory: `storedLocal`, `storingLocal`,
    `localSnapshots`, `localFormed`, `localBelow`, `localAccess` and `localWrite`, or all
    seven with the first suffix `_1`, `_2` that leaves each unused. -/
private def snapshotStoreNames : TacticM (Array Ident) := withMainContext do
  let index := firstUnusedSuffix (← getLCtx) snapshotStoreBases
  return snapshotStoreBases.map fun base => mkIdent (suffixedName index base)

/-- What a numeric local store leaves for the walk that took it. -/
private structure SnapshotStored where
  /-- The snapshots about the memory the store produced. -/
  snapshots : Term
  /-- The store's proved step. -/
  stepped : Term
  /-- The memory the store wrote to. -/
  source : Expr
  /-- The name of the store's `MemoryBelow` evidence from `source`. -/
  below : Ident

/-- Store one numeric local and return its updated snapshot collection with the step taken.
    With `supplied`, the step is the one `facts` prove, to the memory they state, and the
    snapshots are about that memory. -/
private def snapshotStore (snapshot methodFound instructionFound : Term)
    (facts : Array Term) (automatic := false) (supplied := false) :
    TacticM SnapshotStored := withMainContext do
  let some runTerm := (← getMainTarget).find? (·.isAppOf ``run)
    | throwError "Expected a checked run equality"
  let some #[_, _, _, runPc, runArgs, runFrame, runStack, memory] := argumentsOf? runTerm ``run 8
    | throwError "Expected a checked run"
  let methodProof ← Term.elabTerm methodFound none
  let some (_, _, found) := (← instantiateMVars (← inferType methodProof)).eq?
    | throwError "Expected a method lookup"
  let body ← Term.exprToSyntax (← lastArgument snapshotReader found)
  let pc ← Term.exprToSyntax runPc
  let args ← Term.exprToSyntax runArgs
  let frame ← Term.exprToSyntax runFrame
  let stack ← whnf runStack
  let some #[_, operand, remaining] := argumentsOf? stack ``List.cons 3
    | throwError "The local store has no operand"
  let value ← whnf operand
  let some #[scalar] := argumentsOf? value ``Value.scalar 1
    | throwError "The local store is not numeric"
  let value ← Term.exprToSyntax scalar
  let rest ← Term.exprToSyntax remaining
  let instructionProof ← Term.elabTerm instructionFound none
  let some (_, _, instruction) := (← instantiateMVars (← inferType instructionProof)).eq?
    | throwError "Expected an instruction lookup"
  let some operation ← cilReducedOp? (← lastArgument snapshotReader instruction)
    | throwError "The local store instruction is not concrete"
  let storedIndex ← argumentAt snapshotReader operation 0
  let known ← if supplied then
      let operationTerm ← Term.exprToSyntax operation
      let stackTerm ← Term.exprToSyntax runStack
      let memoryTerm ← Term.exprToSyntax memory
      let known ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm (← `(term|
        (by cil_strict cil_checked_step_normalized [$facts,*] :
          step $body $operationTerm $pc $args $frame $stackTerm $memoryTerm =
            Except.ok (FrameAction.next _ _ _ _)))) none
      let known ← instantiateMVars known
      if known.hasMVar then throwError "The supplied store does not determine its result"
      pure (some (← Term.exprToSyntax known))
    else pure none
  if automatic then prepareSnapshotHome memory runFrame storedIndex facts
  let index ← Term.exprToSyntax storedIndex
  let evidence ← match known with
    | some known => `(term| LocalSnapshots.store_at
        (body := $body) (pc := $pc) (args := $args) (frame := $frame)
        (stack := $rest) (index := $index)
        $snapshot ?_ ?_ ?_ ?_ $value ?_ ?_ ?_ ?_ $known)
    | none => `(term| LocalSnapshots.store
        (body := $body) (pc := $pc) (args := $args) (frame := $frame)
        (stack := $rest) (index := $index)
        $snapshot ?_ ?_ ?_ ?_ $value ?_ ?_ ?_ ?_)
  let proof ← withMainContext <| Term.withoutErrToSorry <| Term.elabTerm evidence none
  let pending ← getMVars proof
  -- The home lookup determines its kind before the numeric encoding can be checked.
  for pendingGoal in pending do
    unless ← pendingGoal.isAssigned do
      let type ← instantiateMVars (← pendingGoal.getType)
      if let some (_, left, _) := type.eq? then
        if left.isAppOf ``getElem? then solveSnapshotPremise pendingGoal facts
  for pendingGoal in pending do
    unless ← pendingGoal.isAssigned do
      if ← isProp (← pendingGoal.getType) then solveSnapshotPremise pendingGoal facts
  let proof ← instantiateMVars proof
  if proof.hasMVar then throwError "The local store has unresolved snapshot premises"
  let proofTerm ← Term.exprToSyntax proof
  let names ← snapshotStoreNames
  let #[after, taken, updated, formed, below, retained, written] := names
    | throwError "{snapshotReader}: expected seven store names, but there are {names.size}"
  let stepped ← match known with
    | some known =>
      evalTactic (← `(tactic| obtain
        ⟨$updated, $formed, $below, $retained, $written⟩ := $proofTerm))
      pure known
    | none =>
      evalTactic (← `(tactic| obtain
        ⟨$after, $taken, $updated, $formed, $below, $retained, $written⟩ := $proofTerm))
      pure (taken : Term)
  -- The remembered value is stated as the value a load pushes, not as its `localResult`.
  withMainContext do
    if let some declaration := (← getLCtx).findFromUserName? updated.getId then
      let stated ← instantiateMVars declaration.type
      let reduced ← reduceLocalResults stated
      unless reduced == stated do
        replaceMainGoal [← (← getMainGoal).replaceLocalDeclDefEq declaration.fvarId reduced]
  preserveSnapshotAccess written
  if automatic then
    preserveSnapshotFacts written below
    -- Caller buffers and reads below the homes' watermark hold unchanged after the store.
    loopCarryBelow memory below
    carrySnapshotReads memory below
  return { snapshots := updated, stepped, source := memory, below }

/-- Read the remembered value at the current run's exact frame and stack. -/
private def snapshotLoad (snapshot methodFound instructionFound : Term)
    (facts : Array Term) : TacticM Term := withMainContext do
  let some runTerm := (← getMainTarget).find? (·.isAppOf ``run)
    | throwError "Expected a checked run"
  let some #[_, _, _, runPc, runArgs, runFrame, runStack, _] := argumentsOf? runTerm ``run 8
    | throwError "Expected a checked run"
  let methodProof ← Term.elabTerm methodFound none
  let some (_, _, found) := (← instantiateMVars (← inferType methodProof)).eq?
    | throwError "Expected a method lookup"
  let body ← Term.exprToSyntax (← lastArgument snapshotReader found)
  let pc ← Term.exprToSyntax runPc
  let args ← Term.exprToSyntax runArgs
  let frame ← Term.exprToSyntax runFrame
  let stack ← Term.exprToSyntax runStack
  let instructionProof ← Term.elabTerm instructionFound none
  let some (_, _, instruction) := (← instantiateMVars (← inferType instructionProof)).eq?
    | throwError "Expected an instruction lookup"
  let some operation ← cilReducedOp? (← lastArgument snapshotReader instruction)
    | throwError "The local load instruction is not concrete"
  let loadedIndex ← argumentAt snapshotReader operation 0
  let snapshotProof ← Term.withoutErrToSorry <| Term.elabTerm snapshot none
  let snapshotType ← instantiateMVars (← inferType snapshotProof)
  let some #[_, _, known] := argumentsOf? snapshotType ``LocalSnapshots 3
    | throwError "Expected local snapshots at the current memory"
  let selected := mkApp known loadedIndex
  if (← whnfD selected).isAppOf ``Option.none then
    throwError "The snapshots do not establish a value at this local index"
  let { ctx, simprocs, .. } ← mkSimpContext (← `(tactic| simp only
    [rememberLocal, localResult, ite_true, ite_false, dite_true, dite_false, true_and, and_true,
      Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
      Nat.sub_self, Nat.add_sub_add_left, Nat.add_sub_cancel_left,
      Nat.le_add_right, Nat.add_le_add_iff_left, Nat.add_le_add_iff_right,
      Nat.add_left_cancel_iff, Nat.add_left_inj, Fin.isValue,
      $[$facts:term],*])) (eraseLocal := false)
  let (remembered, _) ← simp selected ctx simprocs
  let result ← whnfD remembered.expr
  let some #[_, loaded] := argumentsOf? result ``Option.some 2
    | throwError "The snapshots do not establish a value at this local index"
  let value ← Term.exprToSyntax loaded
  let checked ← Term.exprToSyntax (← remembered.getProof)
  let index ← Term.exprToSyntax loadedIndex
  `(term| LocalSnapshots.load (body := $body) (pc := $pc) (args := $args) (frame := $frame)
      (stack := $stack) (index := $index) $snapshot $value $checked)

/-- The memory of the goal's run, when the goal has one. -/
private def snapshotRunMemory : TacticM (Option Expr) := do
  if (← getGoals).isEmpty then return none
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    return (target.find? (·.isAppOfArity ``run 8)).bind (argument? · 7)

/-- State the program counter of the goal's run as a numeral when it is closed arithmetic,
    such as the `22 + 1` a snapshot load leaves, so the next lookup meets a numeral. -/
private def foldRunPc : TacticM Unit := do
  if (← getGoals).isEmpty then return
  withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let some execution := target.find? (·.isAppOfArity ``run 8) | return
    let some counter := argument? execution 3 | return
    if counter.hasLooseBVars || (← getNatValue? counter).isSome then return
    let some value ← (Lean.Meta.evalNat counter).run | return
    let folded := mkAppN execution.getAppFn (execution.getAppArgs.set! 3 (mkNatLit value))
    replaceMainGoal [← goal.replaceTargetDefEq
      (target.replace fun term => if term == execution then some folded else none)]

/-- Step with explicit numeric snapshots, introducing each store's memory and new snapshots
    under the names `cil_contract_steps (snapshots := ..)` gives them. -/
syntax "cil_checked_steps" "(" &"snapshots" ":=" term ")" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| cil_checked_steps (snapshots := $snapshot) [$facts:term,*]) => focus do
    let prepared ← prepareStepFacts facts.getElems
    let progressed ← withNormalRun do
      let mut snapshot := snapshot
      let mut progressed := false
      repeat
        if (← getGoals).isEmpty then break
        let saved ← saveState
        try
          let updated ← withNormalNodes prepared <| withMainContext do
            let (methodFound, instructionFound, operation) ←
              cilFetchedOp ``run_next (fun target => target.find? (·.isAppOf ``run)) 3 prepared
            if operation == ``CIL.Instruction.stloc then
              let stored ← snapshotStore snapshot methodFound instructionFound prepared
              evalTactic (← `(tactic| cil_strict rw
                [run_next $methodFound $instructionFound $(stored.stepped)]))
              pure stored.snapshots
            else if operation == ``CIL.Instruction.local then
              let loaded ← snapshotLoad snapshot methodFound instructionFound prepared
              evalTactic (← `(tactic| cil_strict rw
                [run_next $methodFound $instructionFound $loaded]))
              pure snapshot
            else if operation == ``CIL.Instruction.ret then
              evalTactic (← `(tactic| cil_strict
                (rw [run_return $methodFound $instructionFound
                  (by cil_checked_step_normalized [$[$prepared:term],*])
                  (by first | rfl | (simp [$[$prepared:term],*]; rfl))]
                 try exact ⟨_, rfl⟩)))
              pure snapshot
            else
              evalTactic (← `(tactic| cil_strict rw [run_next $methodFound $instructionFound
                (by cil_checked_step_normalized [$[$prepared:term],*])]))
              pure snapshot
          snapshot := updated
          progressed := true
        catch error =>
          saved.restore
          trace[CIL.snapshots] "{error.toMessageData}"
          break
      return progressed
    unless progressed do throwError "Snapshot stepping took no step; justify the local premises"

/-- Restate each supplied read or formed reference of `memory` that its name did not carry,
    such as a projection or an applied lemma, at the memory after `below`, a store that keeps
    `memory` below its watermark. The restated fact replaces the supplied one; a fact whose
    reference is not shown older than the watermark stays as supplied. -/
private def carrySuppliedReads (memory : Expr) (below : Ident) (facts : Array Term) :
    TacticM (Array Term) := do
  let mut carried : Array Term := #[]
  for fact in facts do
    let transport ← withMainContext do
      let saved ← saveState
      try
        let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm fact none
        snapshotCarried? memory below fact (← instantiateMVars (← inferType proof))
      catch _ => pure none
      finally saved.restore
    let some transport := transport | carried := carried.push fact; continue
    let name := mkIdent (← mkFreshUserName `snapshotRead)
    let saved ← saveState
    try
      evalTactic (← `(tactic| cil_strict have $name:ident := $transport))
      carried := carried.push name
    catch _ =>
      saved.restore
      carried := carried.push fact
  return carried

/-- Whether the context or a supplied fact states caller evidence at `memory`, from which step
    facts are derived: a `ValidCall`, object evidence, or a supplied hypothesis about it. -/
private def snapshotEvidenceAt (memory : Expr) (facts : Array Term) : TacticM Bool :=
  withMainContext do
    let mentions (type : Expr) : Bool := (type.find? (· == memory)).isSome
    let context ← getLCtx
    for declaration in context do
      if declaration.isImplementationDetail then continue
      let type := (← instantiateMVars declaration.type).consumeMData
      unless mentions type do continue
      if type.isAppOfArity ``ValidCall 3 || !(objectEvidenceIn type).isEmpty then return true
    for fact in facts do
      unless fact.raw.isIdent do continue
      let some declaration := context.findFromUserName? fact.raw.getId | continue
      if mentions (← instantiateMVars declaration.type) then return true
    return false

/-- Walk a contract goal with numeric local snapshots: ordinary contract steps, and the numeric
    local loads and stores they do not take, through `initial` and each store's snapshots. The
    walk ends when `continuation` closes the goal, after `limit` steps, or at the first step
    that fails. After each store it crosses, the step facts are prepared again from `facts`
    at the store's memory, where the store restated the caller facts they name. Returns
    whether a step was taken. -/
private def snapshotContractWalkSteps (initial : Term) (facts : Array Term)
    (continuation : Option Term) (limit : Option Nat) : TacticM Bool := do
  let mut facts := facts
  let mut prepared ← prepareStepFacts facts
  let finish ← continuation.mapM fun term => do
    return (← cilContractContinuation term).2
  evalTactic (← `(tactic| cil_contract_prepare [$[$prepared:term],*]))
  let mut snapshot := initial
  let mut taken := 0
  let mut progressed := false
  repeat
    if (← getGoals).isEmpty then break
    if let some finish := finish then
      let saved ← saveState
      try
        evalTactic (← `(tactic| cil_strict $finish))
        progressed := true
        break
      catch _ => saved.restore
    if limit.any (taken ≥ ·) then break
    let saved ← saveState
    let stepFacts := prepared
    -- A numeric local's step through the snapshots; a store's step may be `supplied`.
    let remembered (supplied : Bool) : TacticM (Term × Option SnapshotStored) :=
      withNormalNodes stepFacts <| withMainContext do
        let (found, instruction, operation) ←
          cilFetchedOp ``run_next_exists some 4 stepFacts
        let (updated, checked, stored) ← if operation == ``CIL.Instruction.stloc then do
            let stored ← snapshotStore snapshot found instruction stepFacts true supplied
            pure (stored.snapshots, stored.stepped, some stored)
          else if supplied then throwError "The instruction is not a numeric store"
          else if operation == ``CIL.Instruction.local then do
            pure (snapshot, ← snapshotLoad snapshot found instruction stepFacts, none)
          else throwError "The instruction is not a numeric local"
        evalTactic (← `(tactic| (
          cil_strict refine run_next_exists (post := _) $found $instruction $checked ?_
          cil_stack_cleanup)))
        foldRunPc
        return (updated, stored)
    let before ← snapshotRunMemory
    let ordinary ← try
        evalTactic (← `(tactic| cil_contract_step_normalized [$[$prepared:term],*]))
        pure true
      catch _ =>
        saved.restore
        pure false
    let mut crossed : Option SnapshotStored := none
    if ordinary then
      -- A step that changed memory may be a supplied store, whose snapshots follow it.
      let after ← snapshotRunMemory
      if before.isSome && after.isSome && before != after then
        let stepped ← saveState
        saved.restore
        try
          let (updated, stored) ← remembered true
          snapshot := updated
          crossed := stored
        catch error =>
          stepped.restore
          trace[CIL.snapshots] "{error.toMessageData}"
    else
      try
        let (updated, stored) ← remembered false
        snapshot := updated
        crossed := stored
      catch error =>
        saved.restore
        trace[CIL.snapshots] "{error.toMessageData}"
        break
    progressed := true
    taken := taken + 1
    -- Facts prepared before the store are about the memory it wrote to.
    if let some stored := crossed then
      let carried ← carrySuppliedReads stored.source stored.below facts
      let some current ← snapshotRunMemory | continue
      if carried != facts || (← snapshotEvidenceAt current carried) then
        facts := carried
        prepared ← prepareStepFacts facts
  return progressed

/-- `snapshotContractWalkSteps` on the record of normal-form nodes of this walk. -/
private def snapshotContractWalk (initial : Term) (facts : Array Term)
    (continuation : Option Term) (limit : Option Nat) : TacticM Bool :=
  withNormalRun (snapshotContractWalkSteps initial facts continuation limit)

/-- Compose a finite checked execution while retaining numeric local snapshots. Supplied
    step facts take priority over generated stores, and the snapshots follow a supplied store
    to its memory when the store's premises hold. Homes stated at an earlier memory, or after
    leading slots without byte homes, justify a store once the context shows the current
    memory retains their access. Each store names its memory `storedLocal`, its step
    `storingLocal` and `localSnapshots`, `localFormed`, `localBelow`, `localAccess` and
    `localWrite` about that memory, with a shared suffix `_1`, `_2` once a name is taken, and
    restates the named caller facts of the context there; the step facts are then prepared
    again at that memory, so argument and caller reads continue in the same walk. The optional
    continuation stops the walk. -/
syntax "cil_contract_steps" "(" &"snapshots" ":=" term ")" "[" term,* "]"
  (" until " term)? : tactic
/-- As `cil_contract_steps (snapshots := ..)`, but stop silently after at most `count` steps. -/
syntax "cil_contract_steps" "(" &"snapshots" ":=" term ")" num "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| cil_contract_steps (snapshots := $initial) [$facts:term,*]
      $[until $continuation]?) => focus do
    unless ← snapshotContractWalk initial facts.getElems continuation none do
      throwError "Snapshot contract stepping took no step"
  | `(tactic| cil_contract_steps (snapshots := $initial) $count:num [$facts:term,*]) =>
    focus do
      discard <| snapshotContractWalk initial facts.getElems none (some count.getNat)

end CIL.Safety
