import CIL.Safety.StepComposition

namespace CIL.Safety

/-- Declares `step_<op>_<widths>_eq` for each listed value-only op and i32/i64 operand shape, evaluating the
    dispatcher once here, so a step rewrites by constructor and never unfolds `CIL.step` in a proof. -/
syntax "cil_value_steps " ("(" ident " : " term ")")? " [" ident,* "] " num : command

open Lean Meta Elab Command in
elab_rules : command
  | `(cil_value_steps $[($paramName : $paramType)]? [$ops,*] $arity) => do
  let widths := match arity.getNat with
    | 0 => [[]]
    | 1 => [[false], [true]]
    -- Top of stack first: equal widths, and an i32 count over an i64 value for shifts.
    | _ => [[false, false], [true, true], [false, true]]
  let params ← (paramName.toArray.zip paramType.toArray).mapM fun (name, type) =>
    `(Lean.Parser.Term.bracketedBinderF| ($name : $type))
  let rest := mkIdent `rest
  let ns ← getCurrNamespace
  let declared ← liftTermElabM do
    let unfolding (names : Array Name) (base : SimpTheorems) := names.foldlM (·.addDeclToUnfold ·) base
    let congruences ← getSimpCongrTheorems
    let simprocs := #[← Simp.getSimprocs]
    let select ← Simp.mkContext (congrTheorems := congruences) (simpTheorems := #[← unfolding #[
      ``CIL.Safety.pureArity, ``CIL.Safety.scalars, ``CIL.Safety.numericValue, ``CIL.Safety.checkedValue,
      ``List.take, ``List.drop, ``List.map, ``Bind.bind, ``Pure.pure, ``Except.bind, ``Except.pure,
      ``Option.bind] {}])
    -- Unfold a dispatcher only once its discriminants are constructors, so just the selected arm is kept.
    let arms (e : Expr) : MetaM Expr := transform e (pre := fun e => do
      unless [``CIL.Safety.step, ``CIL.step, ``CIL.binary, ``CIL.unary].any e.isAppOf do return .continue
      let some unfolded ← unfoldDefinition? e | return .continue
      let arm ← whnfCore unfolded
      if let some name := arm.getAppFn.constName? then
        if (← isMatcher name) then return .continue
      return .visit arm)
    let cleanup ← Simp.mkContext (config := { arith := true }) (congrTheorems := congruences)
      (simpTheorems := #[← unfolding #[``CIL.Safety.checkedValue, ``CIL.Safety.numericValue, ``Pure.pure,
        ``Except.pure, ``Functor.map, ``Except.map, ``Bind.bind, ``Except.bind] (← getSimpTheorems)])
    let mut declared := #[]
    for op in ops.getElems do
      for shape in widths do
        let names := (if shape.length = 1 then [`v] else [`b, `a]).take shape.length |>.map mkIdent
        let operands ← (names.zip shape).toArray.mapM fun (name, wide) =>
          if wide then `(Lean.Parser.Term.bracketedBinderF| ($name : CIL.W64))
          else `(Lean.Parser.Term.bracketedBinderF| ($name : CIL.W32))
        let stack ← (names.zip shape).foldrM (init := (rest : Term)) fun (name, wide) tail =>
          if wide then `(Value.scalar (CIL.Value.i64 $name) :: $tail)
          else `(Value.scalar (CIL.Value.i32 $name) :: $tail)
        let opName := mkIdent (`CIL.Op ++ op.getId)
        let opTerm ← match paramName with
          | some name => `(($opName $name))
          | none => `($opName)
        let statement ← `(∀ (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)
            ($rest : List Value) $params* $operands*,
            step body $opTerm pc args frame $stack memory = step body $opTerm pc args frame $stack memory)
        let suffix := String.join (shape.map fun wide => if wide then "_i64" else "_i32")
        let name := Name.mkSimple s!"step_{op.getId}{suffix}_eq"
        forallTelescope (← instantiateMVars (← Term.elabType statement)) fun xs equation => do
          let some (_, lhs, _) := equation.eq? | throwError "cil_value_steps: not an equation"
          let mut reduced := lhs
          repeat
            let next := (← dsimp (← arms reduced) select).1
            if next == reduced then break
            reduced := next
          let (result, _) ← simp reduced cleanup simprocs
          -- The proof states `reduced = rhs`; the kernel checks it at `lhs`, definitionally equal by `dsimp`.
          addDecl <| .thmDecl {
            name := ns ++ name, levelParams := []
            type := ← mkForallFVars xs (← mkEq lhs result.expr)
            value := ← mkLambdaFVars xs (← result.getProof) }
        declared := declared.push name
    return declared
  for name in declared do
    elabCommand (← `(attribute [cil_step] $(mkIdent name)))

-- Results stay on the stack; compare-branches expose their condition as an `if` that a fact can decide.
cil_value_steps [neg, bnot, convI1, convI2, convU2, convI4, convI8, convU1, convU4, convU8, convU] 1
cil_value_steps [gt, add, sub, mul, band, bor, bxor, shl, shr, shrUn, lt, ltu, gtu, eq] 2
cil_value_steps (target : Nat) [bgt, ble, bleu, bltu, bgeu, bgtu, bge, blt, beq, bne] 2
cil_value_steps (targets : List Nat) [switch] 1
cil_value_steps (target : Nat) [branch] 0
cil_value_steps [nop] 0
cil_value_steps (id : CIL.Feature) [feature] 0

end CIL.Safety
