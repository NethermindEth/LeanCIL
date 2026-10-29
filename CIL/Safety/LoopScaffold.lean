import CIL.Safety.LoopAutomation
import Lean

/-!
# Checked loop scaffolding

Proof-local generators derive entry frames and cutpoints from extracted methods. Generated
equations are checked by the kernel; no frame layout or instruction position is assumed.
Only proofs requesting the scaffold elaborate it, so extraction certificates stay unchanged.
-/

namespace CIL.Safety
open Lean Elab Command

/-- Derive a successful entry's frame and memory from the existing checked frame allocator.
    Inputs must reduce to a successful entry; failure produces a proof error, never a default. -/
syntax "bind_entry " ident " := " term:max " with " term:max " from " term:max : command

elab_rules : command
  | `(bind_entry $name := $body with $args from $memory) => do
    liftTermElabM do
      let outcome ← Term.elabTerm (← `(enterFrame $body $args $memory)) none
      unless (← Meta.whnf outcome).isAppOf ``Except.ok do
        throwError "Frame entry must reduce to a successful checked allocation"
    let result := mkIdent (name.getId ++ `result)
    let frame := mkIdent (name.getId ++ `frame)
    let entered := mkIdent (name.getId ++ `memory)
    let equation := mkIdent (name.getId ++ `checked)
    elabCommand (← `(def $result : Frame × Memory :=
      ((enterFrame $body $args $memory).toOption).get (by decide)))
    let frameValue ← liftTermElabM do
      let value ← Term.elabTerm (← `($result.1)) (some (mkConst ``Frame))
      PrettyPrinter.delab (← Meta.reduce (← instantiateMVars value))
    elabCommand (← `(def $frame : Frame := $frameValue))
    elabCommand (← `(def $entered : Memory := $result.2))
    elabCommand (← `(theorem $equation :
      enterFrame $body $args $memory = .ok ($frame, $entered) := by rfl))
    elabCommand (← `(#print axioms $equation))
    let homes ← liftTermElabM do
      let value ← Term.elabTerm frame none
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
      elabCommand (← `(abbrev $home : Reference := $address))

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
