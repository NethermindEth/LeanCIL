import CIL.Safety.LocalSnapshots
import CIL.Safety.LoopFrameSteps
import CIL.Safety.CallingTransport

/-!
# Checked stepping with remembered locals

The optional snapshot forms of `cil_checked_steps` and `cil_contract_steps` carry
`LocalSnapshots` through numeric local stores and use them for loads. Importing this module
enables these forms without requiring snapshot support in the ordinary tactics' dependencies.
A store names the memory it produces and the evidence about it, and the contract form restates
the caller facts of the context at that memory, as the loop tactics of
`CIL.Safety.LoopFrameSteps` do.
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
    (stored : step body (.setLocal index) pc args frame (.scalar value :: stack) memory =
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
          let next ← mkAppM ``write_preserves_access_below #[writeProof, type.getArg! 0]
          mkAppM ``AccessBelow.trans #[declaration.toExpr, next]
        else continue
      discard <| assertSnapshotFact declaration.userName proof
        (named := !isSnapshotStoreName declaration.userName)
    catch error =>
      saved.restore
      trace[CIL.snapshots] "{declaration.userName}: {error.toMessageData}"

/-- Restate each named read of `memory` below the watermark of `below`, a store that keeps
    that memory, at the memory after it and under the same name. A read whose reference is
    not shown older than the watermark stays as it is. -/
private def carrySnapshotReads (memory : Expr) (below : Ident) : TacticM Unit := do
  let carried ← withMainContext do
    let context ← getLCtx
    let mut found : Array Name := #[]
    for declaration in context do
      if declaration.isImplementationDetail || declaration.userName.hasMacroScopes then continue
      unless (context.findFromUserName? declaration.userName).any
        (·.fvarId == declaration.fvarId) do continue
      let type := (← instantiateMVars declaration.type).consumeMData
      let some (_, operation, _) := type.eq? | continue
      unless operation.isAppOfArity ``read 4 do continue
      unless ← withNewMCtxDepth (isDefEq operation.getAppArgs[0]! memory) do continue
      found := found.push declaration.userName
    return found
  for name in carried do
    let fact := mkIdent name
    let saved ← saveState
    try evalTactic (← `(tactic| cil_strict have $fact:ident :=
      (MemoryBelow.read $below _ (by cil_caller_allocation) _ _).trans $fact))
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
      unless exposed.isAppOfArity ``List.cons 3 do return none
      skipped := skipped.push exposed.getAppArgs[1]!
      rest := exposed.getAppArgs[2]!
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
      unless type.isAppOfArity head 3 do continue
      unless ← withNewMCtxDepth (isDefEq type.getAppArgs[1]! entered) do continue
      unless ← withNewMCtxDepth (isDefEq type.getAppArgs[2]! current) do continue
      return some declaration.toExpr
    return none
  if let some retained ← linked ``AccessBelow then return ← Term.exprToSyntax retained
  let some preserved ← linked ``MemoryBelow
    | throwError "No evidence that the current memory retains the homes' access"
  -- Stated as `AccessBelow`, the link follows each later store under one watermark.
  assertSnapshotFact `snapshotRetained (← mkAppM ``MemoryBelow.accessBelow #[preserved])

/-- Discover a selected writable home without exposing the concrete frame's slot list. Homes
    stated at an earlier memory, or after leading slots without byte homes, are used when the
    context shows that the current memory retains their access. -/
private def prepareSnapshotHome (memory frame index : Expr) : TacticM Unit := withMainContext do
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
      let type ← inferType proof
      let entered := type.getAppArgs[0]!
      let slots := type.getAppArgs[3]!
      let home := mkIdent (← mkFreshUserName `snapshotHome)
      let slot := mkIdent (← mkFreshUserName `snapshotSlot)
      let bound := mkIdent (← mkFreshUserName `snapshotBound)
      let ready := mkIdent (← mkFreshUserName `snapshotReady)
      let current ← withNewMCtxDepth (isDefEq entered memory)
      if current && (← withNewMCtxDepth (isDefEq slots locals)) then
        let homes ← assertSnapshotFact `snapshotHomes proof
        let index ← Term.exprToSyntax index
        evalTactic (← `(tactic| obtain ⟨$home, $slot, $bound, $ready⟩ :=
          CompleteWritableHomes.home_at $homes $index _ (by rfl)))
        return
      let (skipped, layout) ← snapshotLeadingSlots locals slots
      let some position ← getNatValue? (← whnfR index)
        | throwError "The local index is not a numeral"
      unless skipped.size ≤ position do throwError "The local precedes the homes"
      let retained ← if current then
          `(term| (MemoryBelow.refl (Memory.nextIdentity $(← Term.exprToSyntax entered))
            $(← Term.exprToSyntax entered)).accessBelow)
        else snapshotRetainedAccess entered memory
      let homes ← Term.exprToSyntax proof
      let skippedTerms ← skipped.mapM (Term.exprToSyntax ·)
      let layoutTerm ← layout.mapM (Term.exprToSyntax ·)
      -- A statement over the leading slots is restated over the frame's own locals.
      let restate (statement : Term) : TacticM (TSyntax `tactic) :=
        match layoutTerm with
        | some layout => `(tactic| first
            | exact $statement
            | (rw [$layout:term]; exact $statement))
        | none => `(tactic| exact $statement)
      let localsTerm ← Term.exprToSyntax locals
      let raw := mkIdent (← mkFreshUserName `snapshotSlot)
      let inner := Syntax.mkNumLit (toString (position - skipped.size))
      evalTactic (← `(tactic| cil_strict obtain ⟨$home, $raw, $bound, $ready⟩ :=
        CompleteWritableHomes.home_retained $homes (by assumption) $retained
          (by first | exact Nat.le_refl _ | assumption | omega) [$skippedTerms,*] $inner _
          (by rfl)))
      let outer := Syntax.mkNumLit (toString position)
      let kind ← withMainContext do
        let found ← instantiateMVars (← inferType (← Term.elabTerm raw none))
        let some (_, _, selected) := found.eq? | throwError "Unexpected home lookup"
        Term.exprToSyntax (← whnf selected.appArg!.getAppArgs[0]!)
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
  let context ← getLCtx
  let named (index : Nat) (base : String) : Name :=
    Name.mkSimple (if index == 0 then base else s!"{base}_{index}")
  let mut index := 0
  while snapshotStoreBases.any fun base => context.usesUserName (named index base) do
    index := index + 1
  return snapshotStoreBases.map fun base => mkIdent (named index base)

/-- Store one numeric local and return the name of its updated snapshot collection with the
    step taken. With `supplied`, the step is the one `facts` prove, to the memory they state,
    and the snapshots are about that memory. -/
private def snapshotStore (snapshot methodFound instructionFound : Term)
    (facts : Array Term) (automatic := false) (supplied := false) :
    TacticM (Term × Term) := withMainContext do
  let some runTerm := (← getMainTarget).find? (·.isAppOf ``run)
    | throwError "Expected a checked run equality"
  let arguments := runTerm.getAppArgs
  unless runTerm.isAppOf ``run && arguments.size == 8 do
    throwError "Expected a checked run"
  let methodProof ← Term.elabTerm methodFound none
  let some (_, _, found) := (← instantiateMVars (← inferType methodProof)).eq?
    | throwError "Expected a method lookup"
  let body ← Term.exprToSyntax found.appArg!
  let pc ← Term.exprToSyntax arguments[3]!
  let args ← Term.exprToSyntax arguments[4]!
  let frame ← Term.exprToSyntax arguments[5]!
  let stack ← whnf arguments[6]!
  unless stack.isAppOfArity ``List.cons 3 do throwError "The local store has no operand"
  let value ← whnf stack.getAppArgs[1]!
  unless value.isAppOfArity ``Value.scalar 1 do throwError "The local store is not numeric"
  let value ← Term.exprToSyntax value.appArg!
  let rest ← Term.exprToSyntax stack.appArg!
  let instructionProof ← Term.elabTerm instructionFound none
  let some (_, _, instruction) := (← instantiateMVars (← inferType instructionProof)).eq?
    | throwError "Expected an instruction lookup"
  let some operation ← cilReducedOp? instruction.appArg!
    | throwError "The local store instruction is not concrete"
  let memory := arguments[7]!
  let known ← if supplied then
      let operationTerm ← Term.exprToSyntax operation
      let stackTerm ← Term.exprToSyntax arguments[6]!
      let memoryTerm ← Term.exprToSyntax memory
      let known ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm (← `(term|
        (by cil_strict cil_checked_step_normalized [$facts,*] :
          step $body $operationTerm $pc $args $frame $stackTerm $memoryTerm =
            Except.ok (FrameAction.next _ _ _ _)))) none
      let known ← instantiateMVars known
      if known.hasMVar then throwError "The supplied store does not determine its result"
      pure (some (← Term.exprToSyntax known))
    else pure none
  if automatic then prepareSnapshotHome memory arguments[5]! operation.getAppArgs[0]!
  let index ← Term.exprToSyntax operation.getAppArgs[0]!
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
  let after := names[0]!
  let updated := names[2]!
  let formed := names[3]!
  let below := names[4]!
  let retained := names[5]!
  let written := names[6]!
  let stepped ← match known with
    | some known =>
      evalTactic (← `(tactic| obtain
        ⟨$updated, $formed, $below, $retained, $written⟩ := $proofTerm))
      pure known
    | none =>
      let taken := names[1]!
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
  return (updated, stepped)

/-- Read the remembered value at the current run's exact frame and stack. -/
private def snapshotLoad (snapshot methodFound instructionFound : Term)
    (facts : Array Term) : TacticM Term := withMainContext do
  let some runTerm := (← getMainTarget).find? (·.isAppOf ``run)
    | throwError "Expected a checked run"
  let arguments := runTerm.getAppArgs
  let methodProof ← Term.elabTerm methodFound none
  let some (_, _, found) := (← instantiateMVars (← inferType methodProof)).eq?
    | throwError "Expected a method lookup"
  let body ← Term.exprToSyntax found.appArg!
  let pc ← Term.exprToSyntax arguments[3]!
  let args ← Term.exprToSyntax arguments[4]!
  let frame ← Term.exprToSyntax arguments[5]!
  let stack ← Term.exprToSyntax arguments[6]!
  let instructionProof ← Term.elabTerm instructionFound none
  let some (_, _, instruction) := (← instantiateMVars (← inferType instructionProof)).eq?
    | throwError "Expected an instruction lookup"
  let some operation ← cilReducedOp? instruction.appArg!
    | throwError "The local load instruction is not concrete"
  let snapshotProof ← Term.withoutErrToSorry <| Term.elabTerm snapshot none
  let snapshotType ← instantiateMVars (← inferType snapshotProof)
  unless snapshotType.isAppOfArity ``LocalSnapshots 3 do
    throwError "Expected local snapshots at the current memory"
  let selected := mkApp snapshotType.getAppArgs[2]! operation.getAppArgs[0]!
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
  unless result.isAppOfArity ``Option.some 2 do
    throwError "The snapshots do not establish a value at this local index"
  let value ← Term.exprToSyntax result.appArg!
  let checked ← Term.exprToSyntax (← remembered.getProof)
  let index ← Term.exprToSyntax operation.getAppArgs[0]!
  `(term| LocalSnapshots.load (body := $body) (pc := $pc) (args := $args) (frame := $frame)
      (stack := $stack) (index := $index) $snapshot $value $checked)

/-- The memory of the goal's run, when the goal has one. -/
private def snapshotRunMemory : TacticM (Option Expr) := do
  if (← getGoals).isEmpty then return none
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    return (target.find? (·.isAppOfArity ``run 8)).map (·.getAppArgs[7]!)

/-- State the program counter of the goal's run as a numeral when it is closed arithmetic,
    such as the `22 + 1` a snapshot load leaves, so the next lookup meets a numeral. -/
private def foldRunPc : TacticM Unit := do
  if (← getGoals).isEmpty then return
  withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let some execution := target.find? (·.isAppOfArity ``run 8) | return
    let counter := execution.getAppArgs[3]!
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
    let mut snapshot := snapshot
    let mut progressed := false
    repeat
      if (← getGoals).isEmpty then break
      let saved ← saveState
      try
        let updated ← withMainContext do
          let (methodFound, instructionFound, operation) ←
            cilFetchedOp ``run_next (fun target => target.find? (·.isAppOf ``run)) 3 prepared
          if operation == ``CIL.Op.setLocal then
            let (updated, stepped) ← snapshotStore snapshot methodFound instructionFound prepared
            evalTactic (← `(tactic| cil_strict rw
              [run_next $methodFound $instructionFound $stepped]))
            pure updated
          else if operation == ``CIL.Op.local then
            let loaded ← snapshotLoad snapshot methodFound instructionFound prepared
            evalTactic (← `(tactic| cil_strict rw
              [run_next $methodFound $instructionFound $loaded]))
            pure snapshot
          else if operation == ``CIL.Op.ret then
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
    unless progressed do throwError "Snapshot stepping took no step; justify the local premises"

/-- Compose a finite checked execution while retaining numeric local snapshots. Supplied
    step facts take priority over generated stores, and the snapshots follow a supplied store
    to its memory when the store's premises hold. Homes stated at an earlier memory, or after
    leading slots without byte homes, justify a store once the context shows the current
    memory retains their access. Each store names its memory `storedLocal`, its step
    `storingLocal` and `localSnapshots`, `localFormed`, `localBelow`, `localAccess` and
    `localWrite` about that memory, with a shared suffix `_1`, `_2` once a name is taken, and
    restates the named caller facts of the context there. The optional continuation stops the
    walk. -/
syntax "cil_contract_steps" "(" &"snapshots" ":=" term ")" "[" term,* "]"
  (" until " term)? : tactic

elab_rules : tactic
  | `(tactic| cil_contract_steps (snapshots := $initial) [$facts:term,*]
      $[until $continuation]?) => focus do
    let prepared ← prepareStepFacts facts.getElems
    let finish ← continuation.mapM fun term => do
      return (← cilContractContinuation term).2
    evalTactic (← `(tactic| cil_contract_prepare [$[$prepared:term],*]))
    let mut snapshot := initial
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
      let saved ← saveState
      -- A numeric local's step through the snapshots; a store's step may be `supplied`.
      let remembered (supplied : Bool) : TacticM Term := withMainContext do
        let (found, instruction, operation) ←
          cilFetchedOp ``run_next_exists some 4 prepared
        let (updated, checked) ← if operation == ``CIL.Op.setLocal ||
            operation == ``CIL.Op.setVectorLocal then
            snapshotStore snapshot found instruction prepared true supplied
          else if supplied then throwError "The instruction is not a numeric store"
          else if operation == ``CIL.Op.local || operation == ``CIL.Op.vectorLocal then do
            pure (snapshot, ← snapshotLoad snapshot found instruction prepared)
          else throwError "The instruction is not a numeric local"
        evalTactic (← `(tactic| (
          cil_strict refine run_next_exists (post := _) $found $instruction $checked ?_
          cil_stack_cleanup)))
        foldRunPc
        return updated
      let before ← snapshotRunMemory
      let ordinary ← try
          evalTactic (← `(tactic| cil_contract_step_normalized [$[$prepared:term],*]))
          pure true
        catch _ =>
          saved.restore
          pure false
      if ordinary then
        progressed := true
        -- A step that changed memory may be a supplied store, whose snapshots follow it.
        let after ← snapshotRunMemory
        if before.isSome && after.isSome && before != after then
          let taken ← saveState
          saved.restore
          try
            snapshot ← remembered true
          catch error =>
            taken.restore
            trace[CIL.snapshots] "{error.toMessageData}"
      else
        try
          snapshot ← remembered false
          progressed := true
        catch error =>
          saved.restore
          trace[CIL.snapshots] "{error.toMessageData}"
          break
    unless progressed do throwError "Snapshot contract stepping took no step"

end CIL.Safety
