import CIL.Safety.LocalSnapshots
import CIL.Safety.LoopFrames
import CIL.Safety.CallingTransport

/-!
# Checked stepping with remembered locals

The optional snapshot forms of `cil_checked_steps` and `cil_contract_steps` carry
`LocalSnapshots` through numeric local stores and use them for loads. Importing this module
enables these forms without requiring snapshot support in the ordinary tactics' dependencies.
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

/-- Assert a proved fact in the current continuation and return its fresh local name. -/
private def assertSnapshotFact (base : Name) (proof : Expr) : TacticM Term := withMainContext do
  let type ← inferType proof
  for declaration in ← getLCtx do
    if declaration.type == type then return ← Term.exprToSyntax declaration.toExpr
  let name ← mkFreshUserName base
  let (_, goal) ← (← (← getMainGoal).assert name type proof).intro1P
  replaceMainGoal [goal]
  return mkIdent name

/-- Carry access facts through a proved write; byte-value facts are deliberately not carried. -/
private def preserveSnapshotAccess (written : Term) : TacticM Unit := withMainContext do
  let writeProof ← Term.elabTerm written none
  let declarations := (← getLCtx).decls.toArray.filterMap id
  for declaration in declarations do
    let some (_, accessTerm, _) := declaration.type.eq? | continue
    unless accessTerm.isAppOf ``access do continue
    let saved ← saveState
    try
      let proof ← mkAppM ``snapshot_access_after_write #[declaration.toExpr, writeProof]
      discard <| assertSnapshotFact `snapshotAccess proof
    catch _ => saved.restore

/-- Retain only generic facts whose exact current memory is the source of this write. -/
private def preserveSnapshotFacts (written below : Term) : TacticM Unit := withMainContext do
  let writeProof ← Term.elabTerm written none
  let belowProof ← Term.elabTerm below none
  let declarations := (← getLCtx).decls.toArray.filterMap id
  for declaration in declarations do
    let saved ← saveState
    try
      let type := declaration.type.consumeMData
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
    catch _ => saved.restore

/-- Discover a selected writable home without exposing the concrete frame's slot list. -/
private def prepareSnapshotHome (memory frame index : Expr) : TacticM Unit := withMainContext do
  let declarations := (← getLCtx).decls.toArray.filterMap id
  for declaration in declarations.reverse do
    let saved ← saveState
    try
      let type := declaration.type.consumeMData
      let proof ← if type.isAppOfArity ``NumericHomes 4 then
          mkAppM ``NumericHomes.complete #[declaration.toExpr]
        else if type.isAppOfArity ``CompleteWritableHomes 4 then pure declaration.toExpr
        else continue
      let type ← inferType proof
      unless ← isDefEq type.getAppArgs[0]! memory do throwError "Different home memory"
      unless ← isDefEq type.getAppArgs[3]! (← mkAppM ``Frame.locals #[frame]) do
        throwError "Different home slots"
      let homes ← assertSnapshotFact `snapshotHomes proof
      let index ← Term.exprToSyntax index
      let home := mkIdent (← mkFreshUserName `snapshotHome)
      let slot := mkIdent (← mkFreshUserName `snapshotSlot)
      let bound := mkIdent (← mkFreshUserName `snapshotBound)
      let ready := mkIdent (← mkFreshUserName `snapshotReady)
      evalTactic (← `(tactic| obtain ⟨$home, $slot, $bound, $ready⟩ :=
        CompleteWritableHomes.home_at $homes $index _ (by rfl)))
      return
    catch _ => saved.restore

/-- Store one numeric local and return the name of its updated snapshot collection. -/
private def snapshotStore (snapshot methodFound instructionFound : Term)
    (facts : Array Term) (automatic := false) : TacticM (Term × Term) := withMainContext do
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
  if automatic then prepareSnapshotHome arguments[7]! arguments[5]! operation.getAppArgs[0]!
  let index ← Term.exprToSyntax operation.getAppArgs[0]!
  let proof ← withMainContext <| Term.withoutErrToSorry <| Term.elabTerm (← `(term|
    LocalSnapshots.store
    (body := $body) (pc := $pc) (args := $args) (frame := $frame)
    (stack := $rest) (index := $index)
    $snapshot ?_ ?_ ?_ ?_ $value ?_ ?_ ?_ ?_)) none
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
  let after := mkIdent (← mkFreshUserName `snapshotMemory)
  let stepped := mkIdent (← mkFreshUserName `snapshotStep)
  let updated := mkIdent (← mkFreshUserName `snapshots)
  let formed := mkIdent (← mkFreshUserName `snapshotFormed)
  let below := mkIdent (← mkFreshUserName `snapshotBelow)
  let retained := mkIdent (← mkFreshUserName `snapshotRetained)
  let written := mkIdent (← mkFreshUserName `snapshotWritten)
  evalTactic (← `(tactic| obtain
    ⟨$after, $stepped, $updated, $formed, $below, $retained, $written⟩ := $proofTerm))
  preserveSnapshotAccess written
  if automatic then preserveSnapshotFacts written below
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

/-- Step with explicit numeric snapshots, introducing each store's memory and new snapshots. -/
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
    step facts take priority over generated stores. The optional continuation stops the walk. -/
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
      try
        evalTactic (← `(tactic| cil_contract_step [$[$prepared:term],*]))
        progressed := true
      catch _ =>
        saved.restore
        try
          let updated ← withMainContext do
            let (found, instruction, operation) ←
              cilFetchedOp ``run_next_exists some 4 prepared
            let (updated, checked) ← if operation == ``CIL.Op.setLocal ||
                operation == ``CIL.Op.setVectorLocal then
                snapshotStore snapshot found instruction prepared true
              else if operation == ``CIL.Op.local || operation == ``CIL.Op.vectorLocal then do
                pure (snapshot, ← snapshotLoad snapshot found instruction prepared)
              else throwError "The instruction is not a numeric local"
            evalTactic (← `(tactic| (
              cil_strict refine run_next_exists (post := _) $found $instruction $checked ?_
              cil_stack_cleanup)))
            return updated
          snapshot := updated
          progressed := true
        catch error =>
          saved.restore
          trace[CIL.snapshots] "{error.toMessageData}"
          break
    unless progressed do throwError "Snapshot contract stepping took no step"

end CIL.Safety
