import CIL.Safety.LoopAutomation
import CIL.Safety.FrameProgress
import Lean

/-!
# Checked loop scaffolding

Proof-local generators derive entry frames and cutpoints from extracted methods. Generated
equations are checked by the kernel; no frame layout or instruction position is assumed.
Only proofs requesting the scaffold elaborate it, so extraction certificates stay unchanged.
-/

namespace CIL.Safety
open Lean Elab Command

/-- A successful checked entry's projections describe exactly the returned frame and memory. -/
theorem entry_result_checked (result : ExecutionResult (Frame × Memory))
    (success : result.toOption.isSome = true) : result = .ok (result.toOption.get success) := by
  cases result with
  | error fault => cases success
  | ok pair => rfl
#print axioms entry_result_checked

/-- Existing frame-validity premises justify symbolic entry without evaluating caller storage. -/
theorem enterFrame_isSome (body : CIL.Method) (args : List Value) (memory : Memory)
    (wellFormed : memory.WellFormed) (valid : ValuesValid memory args)
    (fits : FrameSetupFits body args) : (enterFrame body args memory).toOption.isSome = true := by
  obtain ⟨frame, entered, checked⟩ := enterFrame_succeeds body args memory wellFormed valid fits
  rw [checked]
  rfl
#print axioms enterFrame_isSome

/-- Derive parameterized frames, memory and numeric homes from checked allocation.
    Entry must reduce to success or have an explicit proof; no failure receives a default. -/
syntax "bind_entry " ident bracketedBinder* " := " term:max
  " with " term:max " from " term:max (" using " term:max)?
  (" simplifying " "[" term,* "]")? : command

/-- Normalize frame setup with explicit storage facts, retaining checked allocation semantics. -/
private def entrySimplifier (body : TSyntax `term) (facts : Array (TSyntax `term)) :
    CommandElabM (TSyntax `tactic) := do
  let facts := (if body.raw.isIdent then #[body] else #[]) ++ facts
  `(tactic| (simp [enterFrame, makeSelectedLocals, makeLocals,
    makeArgumentHomes, makeParameterHomes, makeLocal, storeLocal, Value.hasUnspecified,
    checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    $[$facts:term],*]; try rfl))

elab_rules : command
  | `(bind_entry $name $binders* := $body with $args from $memory $[using $witness]?
      $[simplifying [$facts,*]]?) => do
    if witness.isSome && facts.isSome then
      throwError "Choose a success witness or simplifying facts, not both"
    let normalizer ← entrySimplifier body (facts.map (·.getElems) |>.getD #[])
    let (parameters, computed) ← liftTermElabM <| Term.elabBinders binders fun variables => do
      let outcome ← Term.elabTermEnsuringType (← `(enterFrame $body $args $memory)) none
      Term.synthesizeSyntheticMVarsNoPostponing
      let computed ← if facts.isSome then do
        let pair ← Meta.mkFreshExprMVar (← Term.elabTerm (← `(Frame × Memory)) none)
        let success ← Meta.mkAppOptM ``Except.ok
          #[some (mkConst ``ExecutionFault), some (← Meta.inferType pair), some pair]
        let equality ← Meta.mkFreshExprMVar (← Meta.mkEq outcome success)
        let remaining ← Tactic.run equality.mvarId! (Tactic.evalTactic normalizer)
        unless remaining.isEmpty do
          throwError "Entry facts do not establish a successful allocation"
        let pair ← instantiateMVars pair
        if pair.hasMVar then throwError "Entry facts leave the allocated frame unresolved"
        pure (some (← PrettyPrinter.delab pair))
      else pure none
      unless computed.isSome || witness.isSome ||
          (← Meta.whnf (← instantiateMVars outcome)).isAppOf ``Except.ok do
        throwError "Frame entry must reduce to a successful checked allocation"
      let parameters ← variables.mapM fun parameter => do
        return mkIdent (← parameter.fvarId!.getDecl).userName
      return (parameters, computed)
    let result := mkIdent (name.getId ++ `result)
    let frame := mkIdent (name.getId ++ `frame)
    let entered := mkIdent (name.getId ++ `memory)
    let equation := mkIdent (name.getId ++ `checked)
    let success ← match witness with
      | some proof => pure proof
      | none => `(by rfl)
    let resultValue ← match computed with
      | some pair => pure pair
      | none => `(((enterFrame $body $args $memory).toOption).get $success)
    elabCommand (← `(def $result $binders* : Frame × Memory := $resultValue))
    let frameValue ← if witness.isSome && computed.isNone then `((@$result $parameters*).1) else
      liftTermElabM <| Term.elabBinders binders fun _ => do
        let value ← Term.elabTerm (← `((@$result $parameters*).1)) (some (mkConst ``Frame))
        PrettyPrinter.delab (← Meta.reduce (← instantiateMVars value))
    elabCommand (← `(def $frame $binders* : Frame := $frameValue))
    elabCommand (← `(def $entered $binders* : Memory := (@$result $parameters*).2))
    let checkedProof ← if computed.isSome then
      `(by simp only [$frame:term, $entered:term, $result:term]; $normalizer:tactic)
      else `(entry_result_checked _ $success)
    elabCommand (← `(theorem $equation $binders* :
      enterFrame $body $args $memory =
        .ok (@$frame $parameters*, @$entered $parameters*) := $checkedProof))
    elabCommand (← `(#print axioms $equation))
    let homes ← liftTermElabM <| Term.elabBinders binders fun _ => do
      let value ← Term.elabTerm (← `(@$frame $parameters*)) none
      let mut locals := mkApp (mkConst ``Frame.locals) value
      let mut homes := #[]
      let mut index := 0
      repeat
        match (← Meta.whnf locals).getAppFnArgs with
        | (``List.cons, #[_, slot, tail]) =>
          let slotValue ← Meta.whnf slot
          let (loaded, stored, address) ← match slotValue.getAppFnArgs with
          | (``LocalSlot.bytes, #[_, address]) =>
            pure (none, none, some (← PrettyPrinter.delab address))
          | (``LocalSlot.span, #[width, writable, _]) =>
            let width ← PrettyPrinter.delab width
            let writable ← PrettyPrinter.delab writable
            pure (some (← `(loadLocal_span (width := $width) (writable := $writable))),
              some (← `(storeLocal_span (width := $width) (writable := $writable))), none)
          | (``LocalSlot.root, _) =>
            pure (some (← `(loadLocal_root)), some (← `(storeLocal_root)), none)
          | (``LocalSlot.readOnlyRoot, _) =>
            pure (some (← `(loadLocal_readOnlyRoot)),
              some (← `(storeLocal_readOnlyRoot_readOnly)), none)
          | _ => pure (none, none, none)
          let symbolic := match slotValue.getAppFnArgs with
            | (``LocalSlot.span, #[width, writable, _]) => width.hasFVar || writable.hasFVar
            | _ => false
          homes := homes.push (index, ← PrettyPrinter.delab slot, loaded, stored, address, symbolic)
          locals := tail
          index := index + 1
        | _ => break
      return homes
    for (index, slot, loaded, stored, address, symbolic) in homes do
      if let some address := address then
        let home := mkIdent (name.getId ++ Name.mkSimple s!"home{index}")
        elabCommand (← `(abbrev $home $binders* : Reference := $address))
      if let (some loaded, some stored) := (loaded, stored) then
        let slotName := mkIdent (name.getId ++ Name.mkSimple s!"slot{index}")
        elabCommand (← `(abbrev $slotName $binders* : LocalSlot := $slot))
        let loadedName := mkIdent (name.getId ++ Name.mkSimple s!"load{index}")
        let storedName := mkIdent (name.getId ++ Name.mkSimple s!"store{index}")
        let factBinders := if symbolic then binders else #[]
        elabCommand (← `(abbrev $loadedName $factBinders* := $loaded))
        elabCommand (← `(abbrev $storedName $factBinders* := $stored))

/-- Derive the unique matching cutpoint and a state constructor from the extracted body.
    Ambiguous or missing matches fail the kernel-checked uniqueness obligation. -/
syntax "bind_cutpoint " ident " := " term:max " matching " term:max
  " with " term:max : command

/-- Select an instruction explicitly, including a structural label in a multi-loop method.
    The requested instruction must exist and satisfy the supplied predicate. -/
syntax "bind_cutpoint " ident bracketedBinder* " := " term:max " at " term:max
  " matching " term:max " with " term:max : command

elab_rules : command
  | `(bind_cutpoint $name $binders* := $body at $location matching $predicate with $frame) => do
    liftTermElabM do
      let selected ← Term.elabTermEnsuringType
        (← `(if ($body).code[$location]?.map $predicate = some true then 1 else 0))
        (some (mkConst ``Nat))
      Term.synthesizeSyntheticMVarsNoPostponing
      unless (← (Meta.evalNat (← Meta.reduce (← instantiateMVars selected))).run) == some 1 do
        throwError "Selected cutpoint must exist and match the instruction predicate"
    let pc := mkIdent (name.getId ++ `pc)
    let checked := mkIdent (name.getId ++ `checked)
    elabCommand (← `(@[cil_code] def $pc : Nat := $location))
    elabCommand (← `(theorem $checked :
      ($body).code[$pc]?.map $predicate = some true := by decide +kernel))
    elabCommand (← `(#print axioms $checked))
    elabCommand (← `(def $name $binders* (stack : List Value) (memory : Memory) : LoopState :=
      ⟨$pc, $frame, stack, memory⟩))

elab_rules : command
  | `(bind_cutpoint $name := $body matching $predicate with $frame) => do
    let pc := mkIdent (name.getId ++ `pc)
    let checked := mkIdent (name.getId ++ `checked)
    let location ← liftTermElabM do
      let count ← Term.elabTermEnsuringType (← `((($body).code.filter $predicate).length))
        (some (mkConst ``Nat))
      Term.synthesizeSyntheticMVarsNoPostponing
      unless (← (Meta.evalNat (← Meta.reduce (← instantiateMVars count))).run) == some 1 do
        throwError "Cutpoint must match exactly one instruction"
      let value ← Term.elabTermEnsuringType (← `(instructionLocation $body $predicate))
        (some (mkConst ``Nat))
      Term.synthesizeSyntheticMVarsNoPostponing
      let some location ← (Meta.evalNat (← Meta.reduce (← instantiateMVars value))).run
        | throwError "Cutpoint must reduce to an instruction index"
      return location
    elabCommand (← `(@[cil_code] def $pc : Nat := $(quote location)))
    elabCommand (← `(theorem $checked :
      ($body).code[$pc]?.map $predicate = some true ∧
        (($body).code.filter $predicate).length = 1 := by decide +kernel))
    elabCommand (← `(#print axioms $checked))
    elabCommand (← `(def $name (stack : List Value) (memory : Memory) : LoopState :=
      ⟨$pc, $frame, stack, memory⟩))

end CIL.Safety
