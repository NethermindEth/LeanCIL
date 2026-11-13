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
      let checked := #[`div, `div_un, `rem, `rem_un, `add_ovf, `add_ovf_un, `sub_ovf,
        `sub_ovf_un, `mul_ovf, `mul_ovf_un, `checkedConvert].contains op.getId
      let select := if checked then checkedSelect else select
      let cleanup := if checked then checkedCleanup else cleanup
      for shape in widths do
        let names := (if shape.length = 1 then [`v] else [`b, `a]).take shape.length |>.map mkIdent
        let opName := mkIdent (instructionTypeName ++ op.getId)
        let opTerm ← `(($opName $paramTerms*))
        -- The equation at this shape; `asValue` types every operand as an unknown `Value`.
        let statementOver (asValue : Bool) : TermElabM Term := do
          let operands ← (names.zip shape).toArray.mapM fun (name, wide) =>
            if asValue then `(Lean.Parser.Term.bracketedBinderF| ($name : CIL.Value))
            else if wide then `(Lean.Parser.Term.bracketedBinderF| ($name : CIL.W64))
            else `(Lean.Parser.Term.bracketedBinderF| ($name : CIL.W32))
          let stack ← (names.zip shape).foldrM (init := (rest : Term)) fun (name, wide) tail =>
            if asValue then `(Value.scalar $name :: $tail)
            else if wide then `(Value.scalar (CIL.Value.i64 $name) :: $tail)
            else `(Value.scalar (CIL.Value.i32 $name) :: $tail)
          `(∀ (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame)
              (memory : Memory) ($rest : List Value) $params* $operands*,
              step body $opTerm pc args frame $stack memory =
                step body $opTerm pc args frame $stack memory)
        -- Proves `∀ xs, lhs = rhs` with `rhs` the arm the dispatcher selects, cleaned up.
        let reduceEquation (statement : Expr) : TermElabM (Expr × Expr) :=
          forallTelescope statement fun xs equation => do
            let some (_, lhs, _) := equation.eq? | throwError "cil_value_steps: not an equation"
            let mut reduced := lhs
            repeat
              let next := (← dsimp (← arms reduced) select).1
              if next == reduced then break
              reduced := next
            let (result, _) ← simp reduced cleanup simprocs
            -- The proof states `reduced = rhs`; the kernel checks it at `lhs`, definitionally
            -- equal by `dsimp`.
            return (← mkForallFVars xs (← mkEq lhs result.expr),
              ← mkLambdaFVars xs (← result.getProof))
        let specific ← instantiateMVars (← Term.elabType (← statementOver false))
        -- On fixed-width operands `whnf` and the kernel evaluate an unsigned overflow bound
        -- `2 ^ width` in unary, so faulting ops reduce over `Value`s and are instantiated.
        let (type, value) ← if checked && (shape.all id || shape.all (!·)) then
            let (generalType, generalProof) ←
              reduceEquation (← instantiateMVars (← Term.elabType (← statementOver true)))
            forallTelescope specific fun xs _ => do
              let fixed := xs.size - shape.length
              let mut arguments := xs.extract 0 fixed
              for (operand, wide) in (xs.extract fixed xs.size).zip shape.toArray do
                let constructor := if wide then ``CIL.Value.i64 else ``CIL.Value.i32
                arguments := arguments.push (mkApp (mkConst constructor) operand)
              let some (_, lhs, guarded) := (← instantiateForall generalType arguments).eq?
                | throwError "cil_value_steps: not an equation"
              -- The operand constructors decide the unspecified-operand guard; nothing else
              -- is reduced.
              let guard := guarded.getAppArgs
              unless guarded.isAppOf ``Bool.rec && guard.size > 3 do
                throwError "cil_value_steps: no unspecified-operand guard in {guarded}"
              let decided ← whnfD guard[3]!
              let some branch := if decided.isConstOf ``Bool.false then some guard[1]!
                  else if decided.isConstOf ``Bool.true then some guard[2]! else none
                | throwError "cil_value_steps: unspecified-operand guard not decided: {decided}"
              let selected := (mkAppN branch (guard.extract 4 guard.size)).headBeta
              -- `id` gives the proof the general statement as its type, so the kernel does not
              -- compare the dispatcher with the reduced form at fixed widths.
              let general := mkApp2 (mkConst ``id [.zero]) generalType generalProof
              return (← mkForallFVars xs (← mkEq lhs selected),
                ← mkLambdaFVars xs (mkAppN general arguments))
          else reduceEquation specific
        let suffix := String.join (shape.map fun wide => if wide then "_i64" else "_i32")
        let name := Name.mkSimple s!"step_{op.getId}{suffix}_eq"
        addDecl <| .thmDecl { name := ns ++ name, levelParams := [], type, value }
        declared := declared.push name
    return declared
  for name in declared do
    elabCommand (← `(attribute [cil_step] $(mkIdent name)))

-- Results stay on the stack; compare-branches expose their condition as an `if` that a fact
-- can decide.
cil_value_steps [neg, not, conv_i1, conv_i2, conv_u2, conv_i4, conv_i8, conv_u1, conv_u4,
  conv_u8, conv_u] 1
cil_value_steps [cgt, add, sub, mul, and, or, xor, shl, shr, shr_un, clt, clt_un, cgt_un, ceq] 2
cil_value_steps (target : Nat) [bgt, ble, ble_un, blt_un, bge_un, bgt_un, bge, blt, beq, bne_un] 2
cil_value_steps (targets : List Nat) [switch] 1
cil_value_steps (target : Nat) [br] 0
cil_value_steps [nop] 0
cil_value_steps (exception : String) [throw] 0
#print axioms step_throw_eq

cil_value_steps (id : CIL.Feature) [feature] 0
cil_value_steps (width : Nat) (signed : Bool) (unsignedInput : Bool) [checkedConvert] 1
cil_value_steps [div, div_un, rem, rem_un, add_ovf, add_ovf_un, sub_ovf, sub_ovf_un, mul_ovf,
  mul_ovf_un] 2

#print axioms step_add_ovf_i64_i64_eq
#print axioms step_add_ovf_un_i64_i64_eq
#print axioms step_sub_ovf_un_i32_i32_eq
#print axioms step_mul_ovf_un_i32_i64_eq
#print axioms step_checkedConvert_i64_eq
#print axioms step_checkedConvert_i32_eq
#print axioms step_div_i64_i64_eq
#print axioms step_rem_un_i32_i32_eq
#print axioms step_div_un_i32_i64_eq

/-- A proved overflow-checked arithmetic result advances the instruction without unfolding its
    check; `selected` names the constructor's flags. -/
theorem step_checked_result {operation : CIL.Instruction} {kind : CIL.CheckedBinaryKind}
    {signed : Bool} (selected : operation.checkedKind? = some (kind, signed))
    {left right value : CIL.Value} {memory : Memory}
    (calculated : CIL.checkedValues kind signed left right = .ok value)
    (leftKnown : left.hasUnspecified = false) (rightKnown : right.hasUnspecified = false)
    (checked : checkedValue memory (.scalar value) = .ok (.scalar value)) :
    ∀ body pc args frame rest,
      step body operation pc args frame (.scalar right :: .scalar left :: rest) memory =
        .ok (.next (pc + 1) (.scalar value :: rest) frame memory) := by
  intro body pc args frame rest
  cases operation <;> simp only [CIL.Instruction.checkedKind?, reduceCtorEq,
    Option.some.injEq, Prod.mk.injEq] at selected
  all_goals obtain ⟨rfl, rfl⟩ := selected
  all_goals simp [step, observerCount, unspecifiedOperands, Value.hasUnspecified,
    leftKnown, rightKnown, calculated, checked, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_checked_result

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
