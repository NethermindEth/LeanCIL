import CIL.Safety.LocalSnapshots

/-!
# Checked stepping with remembered locals

The optional snapshot form of `cil_checked_steps` carries `LocalSnapshots` through numeric
local stores and uses them for loads. Importing this module enables the form without changing
the ordinary stepping tactic or requiring snapshot support in its dependency graph.
-/

namespace CIL.Safety

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
      | rfl
      | cil_lookup [$facts,*]
      | (simp [localNumber, localResult, rememberLocal, $[$facts:term],*]; done))))
  unless remaining.isEmpty do throwError "A local snapshot premise was not established"

/-- Assert a proved fact in the current continuation and return its fresh local name. -/
private def assertSnapshotFact (base : Name) (proof : Expr) : TacticM Term := do
  let name ← mkFreshUserName base
  let (_, goal) ← (← (← getMainGoal).assert name (← inferType proof) proof).intro1P
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

/-- Store one numeric local and return the name of its updated snapshot collection. -/
private def snapshotStore (snapshot methodFound instructionFound : Term)
    (facts : Array Term) : TacticM Term := withMainContext do
  let some runTerm := (← getMainTarget).find? (·.isAppOf ``run)
    | throwError "Expected a checked run equality"
  let arguments := runTerm.getAppArgs
  unless runTerm.isAppOf ``run && arguments.size == 8 do
    throwError "Expected a checked run"
  let methodProof ← Term.elabTerm methodFound none
  let some (_, _, found) := (← inferType methodProof).eq?
    | throwError "Expected a method lookup"
  let body ← Term.exprToSyntax found.appArg!
  let pc ← Term.exprToSyntax arguments[3]!
  let args ← Term.exprToSyntax arguments[4]!
  let stack ← whnf arguments[6]!
  unless stack.isAppOfArity ``List.cons 3 do throwError "The local store has no operand"
  let value ← whnf stack.getAppArgs[1]!
  unless value.isAppOfArity ``Value.scalar 1 do throwError "The local store is not numeric"
  let value ← Term.exprToSyntax value.appArg!
  let rest ← Term.exprToSyntax stack.appArg!
  let instructionProof ← Term.elabTerm instructionFound none
  let some (_, _, instruction) := (← inferType instructionProof).eq?
    | throwError "Expected an instruction lookup"
  let operation ← whnf instruction.appArg!
  let index ← Term.exprToSyntax operation.getAppArgs[0]!
  let proof ← Term.withoutErrToSorry <| Term.elabTerm (← `(term| LocalSnapshots.store
    (body := $body) (pc := $pc) (args := $args) (stack := $rest) (index := $index)
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
  evalTactic (← `(tactic| cil_strict rw [run_next $methodFound $instructionFound $stepped]))
  return updated

/-- Step with explicit numeric snapshots, introducing each store's memory and new snapshots. -/
syntax "cil_checked_steps" "(" &"snapshots" ":=" term ")" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| cil_checked_steps (snapshots := $snapshot) [$facts:term,*]) => focus do
    let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|)) facts.getElems
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
            snapshotStore snapshot methodFound instructionFound prepared
          else if operation == ``CIL.Op.local then
            evalTactic (← `(tactic| cil_strict rw [run_next $methodFound $instructionFound
              (LocalSnapshots.load $snapshot _
                (by first | rfl | simp [rememberLocal, localResult, $[$prepared:term],*]))]))
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

end CIL.Safety
