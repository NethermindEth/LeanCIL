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
  " with " term:max " from " term:max (" using " term:max)? : command

elab_rules : command
  | `(bind_entry $name $binders* := $body with $args from $memory $[using $witness]?) => do
    let parameters ← liftTermElabM <| Term.elabBinders binders fun variables => do
      let outcome ← Term.elabTermEnsuringType (← `(enterFrame $body $args $memory)) none
      Term.synthesizeSyntheticMVarsNoPostponing
      unless witness.isSome || (← Meta.whnf (← instantiateMVars outcome)).isAppOf ``Except.ok do
        throwError "Frame entry must reduce to a successful checked allocation"
      variables.mapM fun parameter => do
        return mkIdent (← parameter.fvarId!.getDecl).userName
    let result := mkIdent (name.getId ++ `result)
    let frame := mkIdent (name.getId ++ `frame)
    let entered := mkIdent (name.getId ++ `memory)
    let equation := mkIdent (name.getId ++ `checked)
    let success ← match witness with
      | some proof => pure proof
      | none => `(by rfl)
    elabCommand (← `(def $result $binders* : Frame × Memory :=
      ((enterFrame $body $args $memory).toOption).get $success))
    let frameValue ← if witness.isSome then `((@$result $parameters*).1) else
      liftTermElabM <| Term.elabBinders binders fun _ => do
        let value ← Term.elabTerm (← `((@$result $parameters*).1)) (some (mkConst ``Frame))
        PrettyPrinter.delab (← Meta.reduce (← instantiateMVars value))
    elabCommand (← `(def $frame $binders* : Frame := $frameValue))
    elabCommand (← `(def $entered $binders* : Memory := (@$result $parameters*).2))
    elabCommand (← `(theorem $equation $binders* :
      enterFrame $body $args $memory =
        .ok (@$frame $parameters*, @$entered $parameters*) :=
      entry_result_checked _ $success))
    elabCommand (← `(#print axioms $equation))
    let homes ← liftTermElabM <| Term.elabBinders binders fun _ => do
      let value ← Term.elabTerm (← `(@$frame $parameters*)) none
      let mut locals := mkApp (mkConst ``Frame.locals) value
      let mut homes := #[]
      let mut index := 0
      repeat
        match (← Meta.whnf locals).getAppFnArgs with
        | (``List.cons, #[_, slot, tail]) =>
          match (← Meta.whnf slot).getAppFnArgs with
          | (``LocalSlot.bytes, #[_, address]) =>
            homes := homes.push (index, ← PrettyPrinter.delab address)
          | _ => pure ()
          locals := tail
          index := index + 1
        | _ => break
      return homes
    for (index, address) in homes do
      let home := mkIdent (name.getId ++ Name.mkSimple s!"home{index}")
      elabCommand (← `(abbrev $home $binders* : Reference := $address))

/-- Derive the unique matching cutpoint and a state constructor from the extracted body.
    Ambiguous or missing matches fail the kernel-checked uniqueness obligation. -/
syntax "bind_cutpoint " ident " := " term:max " matching " term:max
  " with " term:max : command

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
      let value ← Term.elabTermEnsuringType (← `(instructionLocation $body $predicate)) (some (mkConst ``Nat))
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
