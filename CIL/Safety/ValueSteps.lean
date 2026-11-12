import CIL.Safety.StepComposition
import CIL.Safety.GuardNormalization

/-!
# Value step equations

`@[cil_step]` equations for the value-only ops (arithmetic, comparisons, conversions,
branches, `switch`, `nop`, explicit throws and feature tests), one per op and i32/i64 operand shape.
`cil_value_steps` generates them as the library builds by evaluating the dispatcher once, so
stepping rewrites by constructor instead of unfolding `CIL.step` in every proof. A feature
test on a known feature is then reduced to the profile field that a caller's fact names.
-/

namespace CIL.Safety

-- The operand-count guard is false once one or two operands are on the stack.
private theorem operands_present_one (n : Nat) : (n + 1 < 1) = False := by simp
private theorem operands_present_two (n : Nat) : (n + 1 + 1 < 2) = False := by simp

/-- `cil_value_steps (p : T) [ops] arity` declares `step_<op>_<widths>_eq` for each listed
    value-only op and i32/i64 operand shape (widths top of stack first), taking the op's
    parameter `p` when given. The dispatcher is evaluated once here, so a step rewrites by
    constructor and never unfolds `CIL.step` in a proof. -/
syntax "cil_value_steps " ("(" ident " : " term ")")* " [" ident,* "] " num : command

open Lean Meta Elab Command in
elab_rules : command
  | `(cil_value_steps $[($paramName : $paramType)]* [$ops,*] $arity) => do
  let widths := match arity.getNat with
    | 0 => [[]]
    | 1 => [[false], [true]]
    -- Top of stack first: equal widths, and an i32 count over an i64 value for shifts.
    | _ => [[false, false], [true, true], [false, true]]
  let params ← (paramName.zip paramType).mapM fun (name, type) =>
    `(Lean.Parser.Term.bracketedBinderF| ($name : $type))
  let paramTerms : Array Term := paramName.map fun name => ⟨name.raw⟩
  let rest := mkIdent `rest
  let ns ← getCurrNamespace
  let declared ← liftTermElabM do
    let unfolding (names : Array Name) (base : SimpTheorems) :=
      names.foldlM (·.addDeclToUnfold ·) base
    let congruences ← getSimpCongrTheorems
    let simprocs := #[← Simp.getSimprocs]
    let selectionNames := #[
      ``CIL.Safety.pureArity, ``CIL.Safety.scalars, ``CIL.Safety.numericValue,
      ``CIL.Safety.checkedValue,
      ``CIL.Safety.observerCount, ``CIL.Safety.unspecifiedOperands,
      ``CIL.Safety.Value.hasUnspecified, ``CIL.Value.hasUnspecified, ``List.any,
      ``List.take, ``List.drop, ``List.map, ``Bind.bind, ``Pure.pure, ``Except.bind, ``Except.pure,
      ``Option.bind]
    let select ← Simp.mkContext (congrTheorems := congruences)
      (simpTheorems := #[← unfolding selectionNames {}])
    let preserveChecks := fun name =>
      name != ``CIL.Safety.checkedValue && name != ``CIL.Safety.numericValue
    let checkedSelect ← Simp.mkContext (congrTheorems := congruences)
      (simpTheorems := #[← unfolding (selectionNames.filter preserveChecks) {}])
    -- Smart unfolding discharges constructor guards before traversing the selected arm.
    let arms (e : Expr) : MetaM Expr := transform e (pre := fun e => do
      unless [``CIL.Safety.step, ``CIL.step, ``CIL.binary, ``CIL.unary].any e.isAppOf do
        return .continue
      let some unfolded ← unfoldDefinition? e | return .continue
      let arm ← withDefault <| whnf unfolded
      if let some name := arm.getAppFn.constName? then
        if (← isMatcher name) then return .continue
      return .visit arm)
    -- No `arith`: it would restate each branch condition in a linear form the caller's facts
    -- do not match.
    let unfolded ← unfolding #[``CIL.Safety.checkedValue, ``CIL.Safety.numericValue,
      ``Pure.pure, ``Except.pure, ``Functor.map, ``Except.map, ``Bind.bind, ``Except.bind]
      (← getSimpTheorems)
    let present ← (← unfolded.addConst ``operands_present_one).addConst ``operands_present_two
    let cleanup ← Simp.mkContext (congrTheorems := congruences) (simpTheorems := #[present])
    let checkedCleanup ← Simp.mkContext (congrTheorems := congruences)
      (simpTheorems := #[← unfolding #[``Pure.pure, ``Except.pure, ``Functor.map,
        ``Except.map, ``Bind.bind, ``Except.bind] (← getSimpTheorems)])
    let mut declared := #[]
    for op in ops.getElems do
      let checked := #[`checkedArithmetic, `checkedConvert, `divide].contains op.getId
      let select := if checked then checkedSelect else select
      let cleanup := if checked then checkedCleanup else cleanup
      for shape in widths do
        let names := (if shape.length = 1 then [`v] else [`b, `a]).take shape.length |>.map mkIdent
        let operands ← (names.zip shape).toArray.mapM fun (name, wide) =>
          if wide then `(Lean.Parser.Term.bracketedBinderF| ($name : CIL.W64))
          else `(Lean.Parser.Term.bracketedBinderF| ($name : CIL.W32))
        let stack ← (names.zip shape).foldrM (init := (rest : Term)) fun (name, wide) tail =>
          if wide then `(Value.scalar (CIL.Value.i64 $name) :: $tail)
          else `(Value.scalar (CIL.Value.i32 $name) :: $tail)
        let opName := mkIdent (instructionTypeName ++ op.getId)
        let opTerm ← `(($opName $paramTerms*))
        let statement ← `(∀ (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame)
            (memory : Memory) ($rest : List Value) $params* $operands*,
            step body $opTerm pc args frame $stack memory =
              step body $opTerm pc args frame $stack memory)
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
          -- The proof states `reduced = rhs`; the kernel checks it at `lhs`, definitionally
          -- equal by `dsimp`.
          addDecl <| .thmDecl {
            name := ns ++ name, levelParams := []
            type := ← mkForallFVars xs (← mkEq lhs result.expr)
            value := ← mkLambdaFVars xs (← result.getProof) }
        declared := declared.push name
    return declared
  for name in declared do
    elabCommand (← `(attribute [cil_step] $(mkIdent name)))

-- Results stay on the stack; compare-branches expose their condition as an `if` that a fact
-- can decide.
cil_value_steps [neg, bnot, convI1, convI2, convU2, convI4, convI8, convU1, convU4, convU8, convU] 1
cil_value_steps [gt, add, sub, mul, band, bor, bxor, shl, shr, shrUn, lt, ltu, gtu, eq] 2
cil_value_steps (target : Nat) [bgt, ble, bleu, bltu, bgeu, bgtu, bge, blt, beq, bne] 2
cil_value_steps (targets : List Nat) [switch] 1
cil_value_steps (target : Nat) [branch] 0
cil_value_steps [nop] 0
cil_value_steps (exception : String) [throw] 0
#print axioms step_throw_eq

cil_value_steps (id : CIL.Feature) [feature] 0
cil_value_steps (kind : CIL.CheckedBinaryKind) (signed : Bool) [checkedArithmetic] 2
cil_value_steps (width : Nat) (signed : Bool) (unsignedInput : Bool) [checkedConvert] 1
cil_value_steps (signed : Bool) (remainder : Bool) [divide] 2

#print axioms step_checkedArithmetic_i64_i64_eq
#print axioms step_checkedArithmetic_i32_i32_eq
#print axioms step_checkedArithmetic_i32_i64_eq
#print axioms step_checkedConvert_i64_eq
#print axioms step_checkedConvert_i32_eq
#print axioms step_divide_i64_i64_eq
#print axioms step_divide_i32_i32_eq
#print axioms step_divide_i32_i64_eq

/-- A proved checked arithmetic result advances the instruction without unfolding its check. -/
theorem step_checkedArithmetic_result {kind : CIL.CheckedBinaryKind} {signed : Bool}
    {left right value : CIL.Value} {memory : Memory}
    (calculated : CIL.checkedValues kind signed left right = .ok value)
    (leftKnown : left.hasUnspecified = false) (rightKnown : right.hasUnspecified = false)
    (checked : checkedValue memory (.scalar value) = .ok (.scalar value)) :
    ∀ body pc args frame rest,
      step body (.checkedArithmetic kind signed) pc args frame
        (.scalar right :: .scalar left :: rest) memory =
        .ok (.next (pc + 1) (.scalar value :: rest) frame memory) := by
  intro body pc args frame rest
  simp [step, observerCount, unspecifiedOperands, Value.hasUnspecified,
    leftKnown, rightKnown, calculated, checked, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_checkedArithmetic_result

/-- A proved checked conversion advances the instruction without unfolding its range check. -/
theorem step_checkedConvert_result {width : Nat} {signed unsignedInput : Bool}
    {input value : CIL.Value} {memory : Memory}
    (calculated : CIL.convertInteger width signed unsignedInput input = .ok value)
    (inputKnown : input.hasUnspecified = false)
    (checked : checkedValue memory (.scalar value) = .ok (.scalar value)) :
    ∀ body pc args frame rest,
      step body (.checkedConvert width signed unsignedInput) pc args frame
        (.scalar input :: rest) memory =
        .ok (.next (pc + 1) (.scalar value :: rest) frame memory) := by
  intro body pc args frame rest
  simp [step, observerCount, unspecifiedOperands, Value.hasUnspecified,
    inputKnown, calculated, checked, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms step_checkedConvert_result

open Lean Meta in
/-- `(m ..).profile` for a method definition or literal, unfolding only to the structure head;
    an opaque or case-split body is left for a caller's fact. -/
dsimproc [cil_step] reduceMethodProfile (CIL.Method.profile _) := fun e => do
  let_expr CIL.Method.profile body := e | return .continue
  let head ← withDefault <| whnf body
  unless head.isAppOf ``CIL.Method.mk do return .continue
  return .done (← withReducible <| whnf (mkApp (mkConst ``CIL.Method.profile) head))

end CIL.Safety
