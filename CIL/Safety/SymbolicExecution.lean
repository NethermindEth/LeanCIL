import CIL.SymbolicExecution
import CIL.StepEquations
import CIL.Safety.Equations
import CIL.Safety.StepComposition
import CIL.Safety.ValueSteps
import CIL.Safety.MemorySteps
import CIL.Safety.ObjectSteps
import CIL.Safety.InstructionSteps
import CIL.Safety.CallComposition
import CIL.Safety.CodeAt
import CIL.Safety.CheckedSide
import CIL.Safety.CheckedMemoryFacts
import CIL.Safety.AggregateMemorySteps
import CIL.Safety.LoopFacts

/-!
# Checked symbolic execution

The stepping tactics for the checked interpreter. `cil_checked_steps [facts]` proves an
`invoke` or `run` goal about a method by fetching each instruction, closing its lookup with
`cil_lookup`, rewriting the step with the `@[cil_step]` equations and the facts, and composing
steps through `run_next`, `run_return` and `run_call_of_invoke`, or `run_fault` toward a stated
fault. Facts are normalised once, at entry, to the form stepping leaves goals in. The contract
and loop tactics, the automation tests and downstream proofs all build on these;
`docs/PROOFS.md` describes their use.
-/

namespace CIL.Safety

open Lean Elab Tactic Conv in
/-- Replaces the focused term by its full reduction; stepping applies it to the goal's fuel. -/
elab "cil_reduce_fuel" : conv => do
  changeLhs (← Meta.reduce (← getLhs))

open Lean Elab Tactic in
/-- Runs `tactic` so that a failed candidate proof fails and can backtrack, rather than be
    recovered as an admitted term. Only the candidate's own errors count, so an earlier failed
    tactic cannot reject it. -/
elab "cil_strict " tactic:tactic : tactic =>
  Meta.withAssignableSyntheticOpaque <| Term.withoutErrToSorry <| withoutRecover do
    let errors := fun (log : MessageLog) =>
      log.reportedPlusUnreported.foldl
        (fun count m => if m.severity matches .error then count + 1 else count) 0
    let earlier := errors (← Core.getMessageLog)
    evalTactic tactic
    if errors (← Core.getMessageLog) > earlier then throwError "Checked step candidate failed"

/-- The projections of a method contract that stepping unfolds in a goal: its argument and
    result encodings, precondition, footprint and postcondition. -/
def contractProjections : List Lean.Name :=
  [`CIL.Safety.MethodContract.args, `CIL.Safety.MethodContract.results,
    `CIL.Safety.MethodContract.pre, `CIL.Safety.MethodContract.footprint,
    `CIL.Safety.MethodContract.post]

open Lean Meta in
/-- `term` with each projection of a defined contract replaced by what the contract's
    definition states for its arguments. A contract that is a variable, as in a rule stated for
    every contract, is left folded, and so is `Returns`, which a proof may restate. -/
def unfoldContractProjections (term : Expr) : MetaM Expr := do
  let named (e : Expr) : Bool := e.getAppFn.constName?.any contractProjections.contains
  -- Most goals name no contract, and are returned without being rebuilt.
  if (term.find? named).isNone then return term
  Meta.transform term (pre := fun e => do
    unless named e do return .continue
    let arguments := e.getAppArgs
    let some contract := arguments[2]? | return .continue
    let defined ← whnf contract
    unless defined.isAppOf `CIL.Safety.MethodContract.mk do return .continue
    let some info ← getProjectionFnInfo? e.getAppFn.constName! | return .continue
    let some field := defined.getAppArgs[info.numParams + info.i]? | return .continue
    return .visit (← whnfCore (mkAppN field (arguments.extract 3 arguments.size)).headBeta))

open Lean Elab Tactic Meta in
/-- State the goal with the projections of each defined contract unfolded, as
    `unfoldContractProjections` gives them; a goal that names none is left as it is. -/
elab "cil_unfold_contracts" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let unfolded ← unfoldContractProjections target
  unless unfolded == target do replaceMainGoal [← goal.replaceTargetDefEq unfolded]

open Lean Elab Tactic Meta in
/-- State the goal with `leaveFrame frame memory` as `memory` wherever `frame` is a literal
    frame that owns no allocation; nothing else in the goal changes. -/
elab "cil_frame_exit" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let leaves (e : Expr) : Bool := e.isAppOfArity `CIL.Safety.leaveFrame 2
  if (target.find? leaves).isNone then return
  let exited ← Meta.transform target (pre := fun e => do
    unless leaves e do return .continue
    let frame ← whnfR e.appFn!.appArg!
    unless frame.isAppOfArity `CIL.Safety.Frame.mk 5 do return .continue
    unless (← whnfR frame.getAppArgs[2]!).isAppOfArity ``List.nil 1 do return .continue
    return .visit e.appArg!)
  unless exited == target do replaceMainGoal [← goal.replaceTargetDefEq exited]

open Lean Elab Tactic Meta in
/-- Open an existential execution budget. Invocation uses the program's execution bound;
    a `run` uses the remaining code of a body identified by a lookup hypothesis. Every
    checked proof must establish that the candidate suffices. A stated fuel term stays fixed. -/
elab "cil_supply_fuel" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOfArity ``Exists 2 do return
  let .lam _ _ body _ := target.appArg! | return
  let some (_, invocation, _) := body.consumeMData.eq? | return
  if invocation.isAppOfArity `CIL.Safety.run 8 && invocation.getArg! 1 == .bvar 0 then
    let program := invocation.getArg! 0
    let method := invocation.getArg! 2
    let pc := invocation.getArg! 3
    if program.hasLooseBVars || method.hasLooseBVars || pc.hasLooseBVars then return
    let programTerm ← Term.exprToSyntax program
    let methodTerm ← Term.exprToSyntax method
    let lookup ← Term.elabTerm (← `(term| $programTerm[$methodTerm]?)) none
    for declaration in ← getLCtx do
      let some (_, found, result) := declaration.type.consumeMData.eq? | continue
      unless result.isAppOfArity ``Option.some 2 do continue
      unless ← withNewMCtxDepth <| isDefEq lookup found do continue
      for placement in ← getLCtx do
        let placed := placement.type.consumeMData
        unless placed.isAppOfArity ``CodeAt 3 do continue
        unless ← withNewMCtxDepth <| isDefEq placed.getAppArgs[0]! result.appArg! do continue
        unless ← withNewMCtxDepth <| isDefEq placed.getAppArgs[1]! pc do continue
        let segment ← Term.exprToSyntax placed.getAppArgs[2]!
        evalTactic (← `(tactic| refine ⟨(List.length $segment) + 1, ?_⟩))
        return
      let methodBody ← Term.exprToSyntax result.appArg!
      let position ← Term.exprToSyntax pc
      evalTactic (← `(tactic| refine ⟨(CIL.Method.code $methodBody).length - $position + 1, ?_⟩))
      return
    return
  unless invocation.isAppOfArity `CIL.Safety.invoke 5 do return
  let arguments := invocation.getAppArgs
  let program := arguments[0]!
  let method := arguments[2]!
  unless arguments[1]! == .bvar 0 && !program.hasLooseBVars && !method.hasLooseBVars do return
  let bound := mkApp2 (mkConst ``CIL.executionBound) program method
  let witness ← Term.exprToSyntax bound
  evalTactic (← `(tactic| refine ⟨$witness, ?_⟩))

/-- `cil_fact_simp (config) [lemmas] [facts]` runs `simp (config) [lemmas, facts]`, adding each
    local fact normalised by the default simp set and the non-local facts. -/
syntax "cil_fact_simp" Lean.Parser.Tactic.optConfig " [" term,* "]" " [" term,* "]" : tactic

-- `trace.CIL.factNormalize` names each local fact that `normaliseStepFacts` normalises.
initialize Lean.registerTraceClass `CIL.factNormalize

open Lean Elab Tactic Meta in
/-- `proof` and, for a fact over `Fin n` (n <= 64) or over every `Feature`, its instance at
    each value: the profile fields and indexed lemmas are reached only through concrete
    arguments. -/
def factInstances (proof : Expr) : TermElabM (Array Expr) := do
  let mut instances := #[proof]
  if let .forallE _ domain _ _ := ← whnf (← instantiateMVars (← inferType proof)) then
    let domain ← whnf domain
    if domain.isAppOfArity ``Fin 1 then
      if let some size ← (Lean.Meta.evalNat (← reduce domain.appArg!)).run then
        if size <= 64 then
          -- Concrete instances avoid simplifying dependent finite binders a second time.
          instances := #[]
          for index in [:size] do
            let numeral : Term := ⟨Syntax.mkNumLit (toString index)⟩
            let bound : Term := ⟨Syntax.mkNumLit (toString size)⟩
            let value ← Term.elabTerm (← `(term| ($numeral : Fin $bound))) (some domain)
            instances := instances.push (mkApp proof value)
    else if domain.isConstOf ``CIL.Feature then
      for ctor in (← getConstInfoInduct ``CIL.Feature).ctors do
        instances := instances.push (mkApp proof (mkConst ctor))
  return instances

open Lean Elab Tactic Meta in
/-- `facts`, followed by new hypotheses restating them in simp-normal form. The goal's subterms
    reach simp-normal form before a hypothesis can rewrite them, so a fact stated in another
    form would never fire; the originals stay in the simp set. Local facts are normalised with
    the supplied non-local facts, and a proof term, or a global theorem about `evaluate` or a
    method's profile, with the other supplied facts. -/
def normaliseStepFacts (config : TSyntax `Lean.Parser.Tactic.optConfig)
    (facts : Array Term) : TacticM (Array Term) := withMainContext do
    let isLocal (fact : Term) : TacticM Bool :=
      return fact.raw.isIdent && ((← getLCtx).findFromUserName? fact.raw.getId).isSome
    let locals ← facts.filterM isLocal
    let supplied ← facts.filterM fun fact => return !(← isLocal fact)
    let mut normalised : Array Term := #[]
    -- Asserts each instance of `proof` in the normaliser's form; the unchanged original is
    -- already a fact.
    let assertInstances (proof : Expr) (base : Name) (ctx : Simp.Context)
        (simprocs : Simp.SimprocsArray) : TacticM (Array Term) := withMainContext do
      let mut names := #[]
      for instanceProof in ← factInstances proof do
        let type ← instantiateMVars (← inferType instanceProof)
        let (result, _) ← simp type ctx simprocs
        if result.expr.consumeMData.isConstOf ``True then continue
        if result.expr == type && instanceProof == proof then continue
        let normalisedProof ← match result.proof? with
          | some eq => mkEqMP eq instanceProof
          | none => mkExpectedTypeHint instanceProof result.expr
        let name ← mkFreshUserName base
        let (_, goal) ← (← (← getMainGoal).assert name result.expr normalisedProof).intro1P
        replaceMainGoal [goal]
        names := names.push (mkIdent name)
      return names
    if !locals.isEmpty then
      -- `cil_step` reduces a pushed `evaluate` and a method's profile projection, so facts
      -- must land there too.
      let normaliser ← `(tactic| simp $config:optConfig [cil_guard, CIL.fin_val_three,
        CIL.fin_mk_ofNat, cil_feature, CIL.Safety.reduceMethodProfile, $[$supplied:term],*])
      let { ctx, simprocs, .. } ← mkSimpContext normaliser (eraseLocal := false)
      for fact in locals do
        let some decl := (← getLCtx).findFromUserName? fact.raw.getId | continue
        unless ← isProp (← instantiateMVars decl.type) do continue
        trace[CIL.factNormalize] "{decl.userName}"
        normalised := normalised ++ (← assertInstances decl.toExpr decl.userName ctx simprocs)
    -- A proof term such as `(show p from h)` is normalised like a local fact, without itself
    -- as a lemma, which would rewrite its own statement to `True`. Global names stay as given
    -- (most are unfolds), except theorems about `evaluate` or a method's profile, which
    -- `cil_step` rewrites past.
    for fact in supplied do
      if fact.raw.isIdent then
        let some name ← observing? <| realizeGlobalConstNoOverloadWithInfo fact.raw | continue
        let info ← getConstInfo name
        let mentions := (info.type.find? fun e =>
          e.isConstOf ``CIL.FeatureProfile.evaluate || e.isConstOf ``CIL.Method.profile).isSome
        unless mentions && (← isProp info.type) do continue
      let saved ← saveState
      let some proof ← (try
          let proof ← Term.withoutErrToSorry <| Term.elabTerm fact none
          Term.synthesizeSyntheticMVarsNoPostponing
          let proof ← instantiateMVars proof
          pure (if proof.hasMVar then none else some proof)
        catch _ => pure none) | saved.restore; continue
      unless ← isProp (← instantiateMVars (← inferType proof)) do saved.restore; continue
      let others := supplied.filter (· != fact)
      let normaliser ← `(tactic| simp $config:optConfig [cil_guard, CIL.fin_val_three,
        CIL.fin_mk_ofNat, cil_feature, CIL.Safety.reduceMethodProfile, $[$others:term],*])
      let { ctx, simprocs, .. } ← mkSimpContext normaliser (eraseLocal := false)
      let names ← assertInstances proof `supplied ctx simprocs
      if names.isEmpty then saved.restore; continue
      normalised := normalised ++ names
    return facts ++ normalised

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_fact_simp $config:optConfig [$lemmas:term,*] [$facts:term,*]) => do
    let prepared ← normaliseStepFacts config facts.getElems
    let all := lemmas.getElems ++ #[← `(term| cil_guard), ← `(term| CIL.fin_val_three),
      ← `(term| CIL.fin_mk_ofNat)] ++ prepared
    withMainContext <| evalTactic (← `(tactic| simp $config:optConfig [$[$all:term],*]))

/-- Run `tactic` once, failing with `message` when it does not apply, then repeat it. -/
macro "cil_steps_from " message:str tactic:tacticSeq : tactic =>
  `(tactic| ((first | $tactic | fail $message); repeat $tactic))

/-- Close a method or instruction lookup by evaluation for an extraction, else from a lookup
    hypothesis, else by rewriting feature tests in a profile-dependent body with the supplied
    facts. -/
syntax "cil_lookup" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
/-- Reuse a generated equation directly for a named body and a closed instruction position. -/
elab "cil_lookup_equation" : tactic => withMainContext do
  let some (_, lookup, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
    | throwError "Expected an instruction lookup"
  unless lookup.isAppOf ``GetElem?.getElem? do throwError "Expected an indexed lookup"
  let arguments := lookup.getAppArgs
  let code := arguments[arguments.size - 2]!
  unless code.isAppOfArity ``CIL.Method.code 1 do throwError "Expected a named method body"
  let body := code.appArg!
  let some name := body.getAppFn.constName? | throwError "Expected a named method body"
  let some position ← getNatValue? arguments.back! | throwError "Expected a closed position"
  let equation := name.appendAfter s!"_instruction{position}"
  unless (← getEnv).contains equation do throwError "No generated equation at this position"
  let proof := mkAppN (← mkConstWithFreshMVarLevels equation) body.getAppArgs
  let type ← inferType proof
  let some (_, _, found) := type.eq? | throwError "Expected an instruction equation"
  unless found.isAppOfArity ``Option.some 2 do throwError "Expected a successful lookup"
  let operation ← whnfD found.appArg!
  let some (.ctorInfo constructor) := (← getEnv).find? operation.getAppFn.constName!
    | throwError "Instruction needs profile facts"
  unless constructor.induct == ``CIL.Op do throwError "Expected an instruction constructor"
  let some (_, _, pending) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
    | throwError "Expected an instruction lookup"
  unless ← isDefEq pending (← mkAppM ``Option.some #[operation]) do
    throwError "The instruction equation finds another opcode"
  let goals ← (← getMainGoal).apply proof
  unless goals.isEmpty do throwError "The instruction equation left premises"
  replaceMainGoal []

/-- Close a lookup goal `lookup = result` with a hypothesis, up to reducible unfolding, trying
    only hypotheses that are equations whose left side has the goal's head; fails otherwise. -/
syntax "cil_lookup_assumption" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_lookup_assumption) => withMainContext do
    let goal ← getMainGoal
    let rec head (type : Expr) : Option Expr :=
      match type with
      | .forallE _ _ body _ => head body
      | .mdata _ body => head body
      | type => type.eq?.map fun (_, lhs, _) => lhs.consumeMData.getAppFn
    let some wanted := head (← instantiateMVars (← goal.getType))
      | throwError "cil_lookup_assumption: the goal is not an equation"
    -- A head that is not a constant may unify with anything, so every hypothesis is tried.
    let candidate (type : Expr) : Bool := match head type with
      | some found => !wanted.isConst || !found.isConst || found == wanted
      | none => false
    for declaration in ← getLCtx do
      if declaration.isImplementationDetail then continue
      unless candidate (← instantiateMVars declaration.type) do continue
      let saved ← saveState
      if declaration.type.isForall then
        try
          let remaining ← withReducible <| goal.apply declaration.toExpr
          if remaining.isEmpty then replaceMainGoal []; return
        catch _ => pure ()
        saved.restore
        continue
      if ← withReducible (isDefEq (← goal.getType) declaration.type) then
        goal.assign declaration.toExpr
        replaceMainGoal []
        return
      saved.restore
    throwError "cil_lookup_assumption: no hypothesis states this lookup"

/-- A lookup that finds `a` finds every `b` equal to it. -/
theorem lookup_eq_some_of_eq {α : Type u} {lookup : Option α} {a b : α}
    (found : lookup = some a) (reduced : a = b) : lookup = some b := by subst reduced; exact found

#print axioms lookup_eq_some_of_eq

/-- Close `l[i]? = some x`, or a lookup a `@[cil_code]` equation already rewrote to
    `some op = some x`, by `rfl`, deciding a fetched feature `if` with `facts` first so the
    op is a constructor and its step equation applies. -/
syntax "cil_lookup_rfl" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_lookup_rfl [$facts:term,*]) => withMainContext do
    let goal ← getMainGoal
    let saved ← saveState
    evalTactic (← `(tactic| rfl))
    let some (_, lookup, found) := (← instantiateMVars (← goal.getType)).eq? | return
    unless found.isAppOfArity ``Option.some 2 do return
    let op ← whnfR found.appArg!
    let isFeatureTest (e : Expr) := e.isAppOf ``ite || e.isAppOf ``dite || e.isAppOf ``cond
    unless isFeatureTest op do return
    let fetched ← saveState
    saved.restore
    -- Built as a term: `refine` cannot assign the caller's op metavariable inside a term-mode
    -- `by`.
    try
      let decide ← `(tactic| simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true,
        ite_true, ite_false, dite_true, dite_false, Bool.cond_true, Bool.cond_false, ↓reduceIte,
        ↓reduceDIte, $[$facts:term],*])
      let { ctx, simprocs, .. } ← mkSimpContext decide (eraseLocal := false)
      let (reduced, _) ← simp op ctx simprocs
      if isFeatureTest (← whnfR reduced.expr) then throwError "The feature test was not decided"
      let some (_, _, pending) := (← instantiateMVars (← goal.getType)).eq?
        | throwError "Unexpected lookup"
      unless ← isDefEq pending (← mkAppM ``Option.some #[reduced.expr]) do
        throwError "Unexpected lookup"
      let fetchedOp ← mkExpectedTypeHint (← mkEqRefl lookup)
        (← mkEq lookup (← mkAppM ``Option.some #[op]))
      goal.assign (← mkAppM ``CIL.Safety.lookup_eq_some_of_eq #[fetchedOp, ← reduced.getProof])
      replaceMainGoal []
    catch _ => fetched.restore

/-- Close an instruction lookup from a placed segment, without unfolding the abstract body. -/
syntax "cil_lookup_placed" "[" term,* "]" : tactic

open Lean Meta in
/-- Recognize a natural-number position as a literal offset after a segment's start. -/
private partial def placementOffset (start position : Expr) : MetaM Nat := do
  if ← isDefEq position start then return 0
  if let some positionValue ← getNatValue? position then
    if let some startValue ← getNatValue? start then
      if startValue ≤ positionValue then return positionValue - startValue
  if position.isAppOf ``HAdd.hAdd || position.isAppOfArity ``Nat.add 2 then
    if let some amount ← getNatValue? position.appArg! then
      return (← placementOffset start position.getAppArgs[position.getAppArgs.size - 2]!) + amount
  throwError "The position is not a literal offset from this placement"

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_lookup_placed [$facts:term,*]) => withMainContext do
    let original ← saveState
    let mut placements : Array Expr := #[]
    for declaration in ← getLCtx do
      if declaration.type.isAppOfArity ``CodeAt 3 then
        placements := placements.push declaration.toExpr
    for fact in facts.getElems do
      let saved ← saveState
      try
        let proof ← Term.withoutErrToSorry <| Term.elabTerm fact none
        let type ← instantiateMVars (← inferType proof)
        if type.isAppOfArity ``CodeAt 3 then placements := placements.push proof
        else saved.restore
      catch _ => saved.restore
    for placement in placements do
      let saved ← saveState
      try
        let type ← inferType placement
        let start := type.getAppArgs[1]!
        let some (_, lookup, _) := (← getMainTarget).consumeMData.eq?
          | throwError "Expected an instruction lookup"
        let position := lookup.getAppArgs.back!
        let index ← placementOffset start position
        let placedTerm ← Term.exprToSyntax placement
        let indexTerm : Term := ⟨Syntax.mkNumLit (toString index)⟩
        evalTactic (← `(tactic| cil_strict
          (simpa only [Nat.add_assoc, Nat.add_zero, Nat.reduceAdd] using
            (CodeAt.lookup $placedTerm $indexTerm rfl))))
        return
      catch _ => saved.restore
    original.restore
    throwError "No placed segment contains this instruction"

/-- Resolve a computed lookup by checking each value of a bounded finite index. -/
syntax "cil_lookup_finite" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_lookup_finite [$facts:term,*]) => withMainContext do
    let some (_, lookup, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
      | throwError "Expected a lookup equation"
    unless lookup.isAppOf ``GetElem?.getElem? do throwError "Expected an indexed lookup"
    let position := lookup.getAppArgs.back!
    for declaration in ← getLCtx do
      unless (position.find? (· == declaration.toExpr)).isSome do continue
      let type ← whnf declaration.type
      unless type.isAppOfArity ``Fin 1 do continue
      let some size ← (Lean.Meta.evalNat (← reduce type.appArg!)).run | continue
      unless size > 0 && size <= 64 do continue
      let index ← Term.exprToSyntax declaration.toExpr
      let value ← `(term| ($index).val)
      let rec splitAt (offset : Nat) (remaining : Nat) : TacticM (TSyntax `tactic) := do
        let numeral : Term := ⟨Syntax.mkNumLit (toString offset)⟩
        let equal := mkIdent (← mkFreshUserName `positionCase)
        let close ← `(tactic| (
          simp only [$equal:term, Nat.reduceMul, Nat.reduceAdd]
          all_goals first | cil_lookup_equation | cil_lookup [$[$facts:term],*]))
        match remaining with
        | 0 => `(tactic| (
            have $equal : $value = $numeral := by omega
            $close:tactic))
        | rest + 1 =>
          let tail ← splitAt (offset + 1) rest
          `(tactic| (by_cases $equal : $value = $numeral
                     · ($close:tactic)
                     · ($tail:tactic)))
      evalTactic (← splitAt 0 (size - 1))
      return
    throwError "No computed position with a finite bound of at most 64"

open Lean Elab Tactic Meta in
/-- Report a closed position outside a concrete instruction list without hiding its bounds. -/
elab "cil_lookup_failure" : tactic => do
  if (← getGoals).isEmpty then return
  withMainContext do
  if let some (_, lookup, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq? then
    if lookup.isAppOf ``GetElem?.getElem? then
      let arguments := lookup.getAppArgs
      if let some position ← (Lean.Meta.evalNat (← reduce arguments.back!)).run then
        let length ← mkAppM ``List.length #[arguments[arguments.size - 2]!]
        if let some count ← (Lean.Meta.evalNat (← reduce length)).run then
          if count <= position then
            throwError "cil_lookup: position {position} is outside body length {count}"
  evalTactic (← `(tactic| rfl))

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_lookup [$facts:term,*]) => withMainContext do
    let attempt (tactic : TSyntax `tactic) : TacticM Bool := do
      let saved ← saveState
      try evalTactic tactic; return true
      catch _ => saved.restore; return false
    if ← attempt (← `(tactic| cil_lookup_assumption)) then return
    if ← attempt (← `(tactic| cil_lookup_equation)) then return
    let some (_, lookup, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
      | throwError "Expected a lookup equation"
    if !lookup.hasFVar && !lookup.hasMVar then
      evalTactic (← `(tactic| try simp only [cil_code, Nat.reduceAdd, Nat.reduceMul]))
      pruneSolvedGoals
      if (← getGoals).isEmpty then return
      if ← attempt (← `(tactic| cil_lookup_rfl [$facts:term,*])) then return
      evalTactic (← `(tactic| cil_lookup_failure))
      return
    if lookup.isAppOf ``GetElem?.getElem? then
      let position := lookup.getAppArgs.back!
      let mut finite := false
      let mut placed := false
      for declaration in ← getLCtx do
        placed := placed || (declaration.type.find? (·.isAppOfArity ``CodeAt 3)).isSome
        if (position.find? (· == declaration.toExpr)).isSome then
          finite := finite || (← whnf declaration.type).isAppOfArity ``Fin 1
      if placed && (← attempt (← `(tactic| cil_lookup_placed [$facts:term,*]))) then return
      if finite && (← attempt (← `(tactic| cil_lookup_finite [$facts:term,*]))) then return
    evalTactic (← `(tactic| try simp only [cil_code, Nat.reduceAdd, Nat.reduceMul,
      bne_iff_ne, ne_eq, not_false_eq_true, Bool.false_eq_true, ite_true, ite_false,
      ↓reduceIte, $[$facts:term],*]))
    pruneSolvedGoals
    if (← getGoals).isEmpty then return
    if ← attempt (← `(tactic| cil_lookup_rfl [$facts:term,*])) then return
    evalTactic (← `(tactic| cil_lookup_failure))

-- The closed literal operands every stepping tactic evaluates, so a state reads the same
-- whichever tactic produced it. Each is a simproc that fires on numerals only.
attribute [cil_literal_proc] BitVec.reduceSignExtend BitVec.reduceSetWidth
  BitVec.reduceZeroExtend BitVec.reduceToNat BitVec.reduceOfInt Nat.reduceMod

open Lean Elab Tactic Meta in
/-- Evaluate the closed literal operands of the goal with the `cil_literal` set: a width
    conversion, sign extension or `toNat` of a bit-vector numeral, and a remainder of numerals,
    as a masked shift count is. A goal with none is left untouched, so a step pays for the
    normalisation only when its state has such an operand; never fails. -/
elab "cil_literal_operands" : tactic => do
  -- A step that closed its goal leaves nothing to normalise.
  if (← getGoals).isEmpty then return
  withMainContext do
  let numeral (e : Expr) : Bool := e.isRawNatLit || e.isAppOfArity ``OfNat.ofNat 3 ||
    (e.isAppOfArity ``BitVec.ofNat 2 &&
      (e.appArg!.isRawNatLit || e.appArg!.isAppOfArity ``OfNat.ofNat 3))
  let closed (e : Expr) : Bool :=
    ((e.isAppOfArity ``BitVec.signExtend 3 || e.isAppOfArity ``BitVec.setWidth 3 ||
      e.isAppOfArity ``BitVec.zeroExtend 3 || e.isAppOfArity ``BitVec.toNat 2) &&
      numeral e.appArg!) ||
    (e.isAppOfArity ``HMod.hMod 6 && numeral e.appArg! && numeral e.appFn!.appArg!)
  if ((← instantiateMVars (← getMainTarget)).find? closed).isSome then
    evalTactic (← `(tactic| try simp only [cil_literal]))

/-- Normalises the literal `take`, `drop`, `reverse` and `++` a step leaves on the stack and
    evaluates its closed literal operands (`cil_literal_operands`); never fails. -/
macro "cil_stack_cleanup" : tactic =>
  `(tactic| (
    try simp only [List.drop_succ_cons, List.drop_zero, List.drop_nil,
      List.take_succ_cons, List.take_zero, List.take_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.append_nil]
    cil_literal_operands))

/-- Closes a checked `step` goal by rewriting with the `@[cil_step]` and
    `@[cil_instruction_step]` equations, failing if nothing rewrites, then by the checked-value
    definitions and `facts`, constructors and `rfl`. -/
macro "cil_checked_step_by_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       simp only [cil_instruction_step, cil_step, cil_guard, CIL.Safety.instructionStep]
       try simp only [cil_guard, cil_checked, cil_side, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

open Lean Elab Tactic Meta in
/-- Succeed only on a checked `step` goal whose opcode has `@[cil_instruction_step]` equations;
    a syntactic test, since a trial rewrite would traverse the whole goal. -/
elab "cil_instruction_step_goal" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let some (_, lhs, _) := target.eq? | throwError "Expected a checked step equality"
  unless lhs.isAppOfArity ``CIL.Safety.step 7 do throwError "Expected a checked step equality"
  let head := (← whnfR lhs.getAppArgs[1]!).getAppFn.constName?
  -- The opcodes of `CIL.Safety.InstructionSteps`.
  unless head.any (#[``CIL.Op.load64, ``CIL.Op.store64, ``CIL.Op.storeScalar, ``CIL.Op.fieldAt,
      ``CIL.Op.fieldAddress, ``CIL.Op.setFieldAt, ``CIL.Op.asRef, ``CIL.Op.skipInit,
      ``CIL.Op.initAggregate, ``CIL.Op.loadAggregate, ``CIL.Op.storeAggregate].contains ·) do
    throwError "No instruction step equation for this opcode"

/-- `cil_checked_step_by_equations` without the `@[cil_instruction_step]` equations, for a step
    those equations rewrite: the step stays at `instruction`, where a supplied fact about
    `instruction`, or `CIL.Safety.instruction` itself, applies. -/
macro "cil_checked_instruction_from_fact " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       cil_instruction_step_goal
       simp only [cil_step, cil_guard, CIL.Safety.instructionStep]
       try simp only [cil_guard, cil_checked, cil_side, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

/-- `cil_checked_step_by_equations` for a `.memory` step, also rewriting `referenceAt` on
    `.null` and `.address`. Only memory equations expose `referenceAt`; its equations in the
    generic list would slow every other step. -/
macro "cil_checked_memory_by_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       simp only [cil_step, cil_guard, CIL.Safety.instructionStep]
       try simp only [cil_guard, cil_checked, cil_side, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

/-- Normalize checked conditions with the shared closed rules, retaining unresolved goals. -/
macro "cil_checked_normalize " "[" facts:term,* "]" : tactic =>
  `(tactic| try simp only [cil_checked, cil_guard, cil_side, $[$facts:term],*])

/-- Closes frame-entry and return premises with the closed checked-value rules and supplied
    facts. Returned objects retain formation when the exiting frame does not own them. -/
macro "cil_checked_side " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       try rfl
       all_goals cil_frame_exit
       all_goals cil_checked_normalize [$[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

open Lean Meta in
/-- Spell a literal `BitVec.ofNat n k` as the numeral `k`, as an evaluation fact with a literal
    operand states it; a symbolic `BitVec.ofNat n x` keeps its spelling so later facts on it
    still match. -/
dsimproc_decl bitVecOfNatLiteral (BitVec.ofNat _ _) := fun e => do
  let_expr BitVec.ofNat width operand ← e | return .continue
  let some value ← getNatValue? operand | return .continue
  return .done (← mkNumeral (mkApp (mkConst ``BitVec) width) value)

/-- Succeed only when the goal still mentions intrinsic evaluation. -/
elab "cil_intrinsic_pending" : tactic => Lean.Elab.Tactic.withMainContext do
  let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
  unless (target.find? fun e =>
      e.isConstOf ``CIL.evalIntrinsic || e.isConstOf ``CIL.Safety.checkedIntrinsic).isSome do
    Lean.throwError "No pending intrinsic evaluation"

/-- Closes a checked step through the opcode equations without recovering failed subproofs. -/
macro "cil_checked_step_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| cil_strict (cil_checked_step_by_equations [$[$facts:term],*]))

/-- Closes a memory step with a matching supplied operation fact. Memory-dispatch facts
    select the static dispatch equation explicitly before this tactic runs. -/
macro "cil_checked_memory_from_fact " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       rw [CIL.Safety.step_memory_eq]
       try simp only [cil_guard]
       try simp only [cil_guard, cil_checked, cil_side, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

open Lean Elab Tactic Meta in
/-- Whether a supplied fact's type satisfies `test`: a hypothesis, a constant, or an applied
    term that is elaborated, tested and then discarded, since `test` may meet its fresh
    metavariables. -/
def suppliedFactSatisfies (fact : Term) (test : Expr → MetaM Bool) : TacticM Bool := do
  if fact.raw.isIdent then
    match (← getLCtx).findFromUserName? fact.raw.getId with
    | some decl => test (← instantiateMVars decl.type)
    | none =>
      try test (← getConstInfo (← resolveGlobalConstNoOverload fact.raw)).type
      catch _ => return false
  else
    let saved ← saveState
    try test (← instantiateMVars (← inferType (← Term.withoutErrToSorry (Term.elabTerm fact none))))
    catch _ => return false
    finally saved.restore

open Lean Meta in
/-- Whether `e` contains a numeral whose type reduces to `BitVec n`, such as `(27 : W32)`. -/
partial def hasBitVecNumeral (e : Expr) : MetaM Bool := do
  if e.isAppOfArity ``OfNat.ofNat 3 && !(e.getArg! 0).hasLooseBVars then
    if (← whnfR (e.getArg! 0)).isAppOf ``BitVec then return true
  e.foldlM (fun found child => if found then pure true else hasBitVecNumeral child) false

/-- Succeed only when a supplied fact concludes `evalIntrinsic ... = _` with a numeral `BitVec`
    operand. -/
syntax "cil_numeral_eval_fact" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_numeral_eval_fact [$facts:term,*]) => withMainContext do
    for fact in facts.getElems do
      let found ← suppliedFactSatisfies fact fun type => forallTelescope type fun _ conclusion => do
        let some (_, lhs, _) := conclusion.eq? | return false
        unless lhs.isAppOf ``CIL.evalIntrinsic || lhs.isAppOf ``CIL.Safety.checkedIntrinsic do
          return false
        hasBitVecNumeral lhs
      if found then return
    throwError "No supplied evaluation fact with a numeral operand"

/-- Closes a checked intrinsic step: decides availability and the operand count, evaluates
    with the `@[cil_eval]` lemmas and `facts`, then closes the residue by `rfl` or the step
    equations. When a supplied evaluation fact has a numeral operand, the goal's literal
    operands are respelled as numerals to match it. -/
macro "cil_checked_intrinsic " "[" facts:term,* "]" : tactic =>
  `(tactic| (
    simp only [cil_step, cil_guard, CIL.Intrinsic.available, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceLT, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ite_false, ite_true, List.take_succ_cons, List.take_zero, List.take_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.append_nil,
      List.drop_succ_cons, List.drop_zero, List.drop_nil, CIL.Safety.scalars,
      CIL.Safety.numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure,
      BitVec.ofInt_ofNat, cil_eval, $[$facts:term],*]
    -- A fact that makes the intrinsic fault leaves no result for this pass to check.
    all_goals try simp only [CIL.Safety.checkedIntrinsic, cil_guard, cil_eval,
      List.any_cons, List.any_nil, Bool.false_or, Bool.true_or, Bool.or_false,
      Bool.false_eq_true, ite_false, CIL.Safety.checkedValue, CIL.Safety.numericValue, ite_true,
      Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
    -- `rfl` would evaluate a residue definitionally and push a value no later fact matches.
    -- Operands arrive as `BitVec.ofNat n k`, which only a supplied fact stated with a numeral
    -- `k` needs respelled; facts are splice-last.
    all_goals try (
         cil_numeral_eval_fact [$[$facts:term],*]
         cil_intrinsic_pending
         simp only [bitVecOfNatLiteral, CIL.Safety.checkedIntrinsic, cil_guard, cil_eval,
           List.any_cons, List.any_nil, Bool.false_or, Bool.true_or, Bool.or_false,
           Bool.false_eq_true, ite_false, CIL.Safety.checkedValue, CIL.Safety.numericValue,
           ite_true, Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
         fail_if_success cil_intrinsic_pending)
    all_goals cil_checked_side [$[$facts:term],*]))

open Lean Meta in
/-- The opcode constructor `op` denotes, when its head reduces to one: a body that picks an
    opcode with a decided `if` would otherwise match no step equation and unfold the whole
    dispatcher. -/
def cilReducedOp? (op : Expr) : MetaM (Option Expr) := do
  let reduced ← whnfD (← instantiateMVars op)
  let some name := reduced.getAppFn.constName? | return none
  let some (.ctorInfo info) := (← getEnv).find? name | return none
  return if info.induct == ``CIL.Op then some reduced else none

/-- One checked `step` goal, with facts already normalised: a supplied step fact for the
    fetched op, as given or with its `@[cil_code]` bodies unfolded, or else a strategy chosen
    by opcode and the kind of its supplied operation facts. -/
syntax "cil_checked_step_normalized" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
/-- Equations selected inside quantified conjunctions retain their original binders. -/
private partial def equationConjuncts (select : Expr → Bool) (proof : Expr) :
    MetaM (Array Expr) := do
  forallTelescope (← inferType proof) fun variables conclusion => do
    if conclusion.isAppOfArity ``And 2 then
      let applied := mkAppN proof variables
      let left ← equationConjuncts select (← mkAppM ``And.left #[applied])
      let right ← equationConjuncts select (← mkAppM ``And.right #[applied])
      (left ++ right).mapM (mkLambdaFVars variables)
    else
      let some (_, lhs, _) := conclusion.consumeMData.eq? | return #[]
      return if select lhs then #[proof] else #[]

open Lean Elab Tactic Meta in
/-- The supplied facts that state a `step` result for the goal's op, or for any op. -/
def stepFacts (target : Expr) (facts : Array Term) : TacticM (Array Term) := do
  -- A tactic `have` leaves the target under `mdata`, which `Expr.eq?` does not see through.
  let target := (← instantiateMVars target).consumeMData
  let some (_, lhs, _) := target.eq? | return #[]
  unless lhs.isAppOfArity ``CIL.Safety.step 7 do return #[]
  let head := (← whnfR lhs.getAppArgs[1]!).getAppFn.constName?
  let states (type : Expr) : MetaM Bool := withNewMCtxDepth do
    let openParameters := type.hasMVar
    let (_, _, conclusion) ← forallMetaTelescopeReducing type
    let some (_, factLhs, _) := conclusion.eq? | return false
    unless factLhs.isAppOfArity ``CIL.Safety.step 7 do return false
    match (← whnfR factLhs.getAppArgs[1]!).getAppFn.constName?, head with
    | some factHead, some goalHead => unless factHead == goalHead do return false
    | _, _ => pure ()
    if openParameters then return true
    -- A named body may need its generated equation unfolded before application.
    let arguments := factLhs.getAppArgs |>.set! 0 lhs.getAppArgs[0]!
    withTransparency .instances <| isDefEq (mkAppN factLhs.getAppFn arguments) lhs
  let mut matching := #[]
  for fact in facts do
    if ← suppliedFactSatisfies fact states then
      matching := matching.push fact
    else if ← suppliedFactSatisfies fact (fun type => forallTelescope type fun _ conclusion =>
        pure (conclusion.isAppOfArity ``And 2)) then
      let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm fact none
      for part in ← equationConjuncts (·.isAppOfArity ``CIL.Safety.step 7) proof do
        if ← states (← inferType part) then
          matching := matching.push (← Term.exprToSyntax part)
  return matching

open Lean Elab Tactic Meta in
/-- Close the goal with `fact` after unfolding the `@[cil_code]` definitions in its type, for a
    goal whose lookup already replaced a named body by its literal. Fails when the type has no
    such definition. -/
def applyUnfoldedStepFact (unfold : Simp.Context) (simprocs : Simp.SimprocsArray) (fact : Term) :
    TacticM Unit := withMainContext do
  let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm fact none
  let type ← instantiateMVars (← inferType proof)
  let (result, _) ← simp type unfold simprocs
  if result.expr == type then throwError "The step fact names no cil_code definition"
  let proof ← match result.proof? with
    | some eq => mkEqMP eq proof
    | none => mkExpectedTypeHint proof result.expr
  let goals ← withTransparency .instances <| (← getMainGoal).apply proof
  unless goals.isEmpty do throwError "The step fact left goals"
  replaceMainGoal []

open Lean Elab Tactic Meta in
/-- Match one dispatch equation, retaining quantified facts and conjunction-wrapped facts. -/
private partial def dispatchFactMatches (wanted : Expr) (function : Name) (type : Expr) :
    MetaM Bool := withNewMCtxDepth do
  let (_, _, conclusion) ← forallMetaTelescopeReducing type
  if conclusion.isAppOfArity ``And 2 then
    return (← dispatchFactMatches wanted function conclusion.getAppArgs[0]!) ||
      (← dispatchFactMatches wanted function conclusion.getAppArgs[1]!)
  let some (_, lhs, _) := conclusion.consumeMData.eq? | return false
  unless lhs.isAppOf function do return false
  withTransparency .instances <| isDefEq lhs wanted

open Lean Elab Tactic Meta in
/-- Supplied dispatch facts for this operation, stack and memory, including facts inside a
    conjunction. Matching fresh quantified variables never instantiates the caller's goal. -/
def dispatchFacts (step : Expr) (function : Name) (facts : Array Term) :
    TacticM (Array Term) := do
  let arguments := step.getAppArgs
  let operation ← whnfR arguments[1]!
  let wanted ← if function == ``CIL.Safety.instruction then
      mkAppM function #[operation, arguments[5]!, arguments[6]!]
    else if function == ``CIL.Safety.staticInstruction then
      mkAppM function #[arguments[0]!, arguments[2]!, operation.appArg!,
        arguments[5]!, arguments[6]!]
    else mkAppM function #[operation.appArg!, arguments[5]!, arguments[6]!]
  facts.filterM (suppliedFactSatisfies · (dispatchFactMatches wanted function))

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_checked_step_normalized [$facts:term,*]) => withMainContext do
    let initial := (← instantiateMVars (← getMainTarget)).consumeMData
    if let some (_, step, _) := initial.eq? then
      if step.isAppOfArity ``CIL.Safety.step 7 &&
          step.getAppArgs[1]!.isConstOf ``CIL.Op.nop then
        evalTactic (← `(tactic| exact step_nop_eq ..))
        return
    -- A body reached through a lookup hypothesis stays named; one reached by unfolding a
    -- `cil_code` program is already a literal, so a fact on the named body needs its own
    -- `cil_code` unfolded to match it.
    let candidates ← stepFacts (← getMainTarget) facts.getElems
    for fact in candidates do
      let saved ← saveState
      try
        evalTactic (← `(tactic| cil_strict ((with_reducible_and_instances apply $fact); done)))
        return
      catch _ => saved.restore
    if !candidates.isEmpty then
      let { ctx, simprocs, .. } ←
        mkSimpContext (← `(tactic| simp only [cil_code])) (eraseLocal := false)
      for fact in candidates do
        let saved ← saveState
        try
          applyUnfoldedStepFact ctx simprocs fact
          return
        catch _ => saved.restore
    evalTactic (← `(tactic| try simp only [cil_code, Nat.reduceAdd]))
    if (← getGoals).isEmpty then return
    -- A tactic `have` leaves the target under `mdata`, which `Expr.eq?` does not see through.
    let mut target := (← instantiateMVars (← getMainTarget)).consumeMData
    let some (_, lhs, rhs) := target.eq? | throwError "Expected a checked step equality"
    let mut args := lhs.getAppArgs
    let mut operation := Name.anonymous
    if lhs.isAppOfArity ``CIL.Safety.step 7 then
      if let some op ← cilReducedOp? args[1]! then
        operation := op.getAppFn.constName!
        unless op == args[1]! do
          args := args.set! 1 op
          target ← mkEq (mkAppN lhs.getAppFn args) rhs
          replaceMainGoal [← (← getMainGoal).replaceTargetDefEq target]
    if operation == ``CIL.Op.checkedArithmetic then
      for fact in facts.getElems do
        unless ← suppliedFactSatisfies fact (fun type => forallTelescope type fun _ conclusion => do
            let some (_, left, _) := conclusion.eq? | return false
            return left.isAppOf ``CIL.checkedValues) do continue
        let saved ← saveState
        try
          evalTactic (← `(tactic| cil_strict (
            apply step_checkedArithmetic_result $fact
            all_goals cil_checked_side [])))
          return
        catch _ => saved.restore
    let scalar := #[``CIL.Op.neg, ``CIL.Op.gt, ``CIL.Op.convI1, ``CIL.Op.convI2,
      ``CIL.Op.convU2, ``CIL.Op.convI8, ``CIL.Op.convI4, ``CIL.Op.convU1,
      ``CIL.Op.convU4, ``CIL.Op.convU8, ``CIL.Op.convU, ``CIL.Op.bnot,
      ``CIL.Op.add, ``CIL.Op.sub, ``CIL.Op.mul, ``CIL.Op.band, ``CIL.Op.bor,
      ``CIL.Op.bxor, ``CIL.Op.shl, ``CIL.Op.shr, ``CIL.Op.shrUn, ``CIL.Op.lt,
      ``CIL.Op.ltu, ``CIL.Op.gtu, ``CIL.Op.eq].contains operation
    if scalar && lhs.isAppOfArity ``CIL.Safety.step 7 then
      -- Reuse the selected value equation without rewriting its symbolic arithmetic result.
      let mut widths := #[]
      let mut stack ← whnfR args[5]!
      for _ in [:2] do
        unless stack.isAppOfArity ``List.cons 3 do break
        let value := stack.getAppArgs[1]!
        unless value.isAppOfArity ``Value.scalar 1 do break
        let scalar := value.appArg!
        if scalar.isAppOfArity ``CIL.Value.i32 1 then widths := widths.push "_i32"
        else if scalar.isAppOfArity ``CIL.Value.i64 1 then widths := widths.push "_i64"
        else break
        stack ← whnfR stack.getAppArgs[2]!
      for count in [0, 1, 2] do
        if count > widths.size then continue
        let suffix := String.join (widths.toList.take count)
        let name := `CIL.Safety ++ Name.mkSimple s!"step_{operation.getString!}{suffix}_eq"
        unless (← getEnv).contains name do continue
        let saved ← saveState
        try
          let remaining ← withTransparency .instances <|
            (← getMainGoal).apply (← mkConstWithFreshMVarLevels name)
          if remaining.isEmpty then replaceMainGoal []; return
        catch _ => pure ()
        saved.restore
      if rhs.isAppOfArity ``Except.error 3 then
        let saved ← saveState
        try
          evalTactic (← `(tactic| cil_strict (
            apply step_unspecified
            simp only [observerCount, cil_guard, cil_side, $[$facts:term],*]
            done)))
          return
        catch _ => saved.restore
    let strategy ← if operation == ``CIL.Op.intrinsic then
        `(tactic| cil_checked_intrinsic [$facts:term,*])
      else if operation == ``CIL.Op.memory then
        let matchingStatic :=
          !(← dispatchFacts lhs ``CIL.Safety.staticInstruction facts.getElems).isEmpty
        let matchingMemory :=
          !(← dispatchFacts lhs ``CIL.Safety.memoryInstruction facts.getElems).isEmpty
        -- A supplied operation fact retains its abstraction; otherwise select its equation.
        if matchingStatic then
          `(tactic| cil_strict (cil_checked_memory_from_fact [$facts:term,*]))
        else if matchingMemory then
          `(tactic| cil_strict (
            cil_checked_memory_from_fact [CIL.Safety.staticInstruction, $facts:term,*]))
        else
          `(tactic| cil_strict (cil_checked_memory_by_equations [$facts:term,*]))
      -- A fact about `instruction` keeps its abstraction only if tried before a per-shape
      -- equation rewrites past it.
      else if !(← dispatchFacts lhs ``CIL.Safety.instruction facts.getElems).isEmpty then
        `(tactic| cil_strict (cil_checked_instruction_from_fact [$facts:term,*]))
      else
        `(tactic| cil_checked_step_equations [$facts:term,*])
    evalTactic strategy

/-- One checked `step` goal: normalises `facts`, then runs `cil_checked_step_normalized`. -/
syntax "cil_checked_step" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
/-- Derive checked load and store facts from byte operations once, before stepping. The
    byte width selects the existing bridge; quantified facts retain their binders. -/
def prepareOperationFacts (facts : Array Term) : TacticM (Array Term) := withMainContext do
  let operationEquation (operation : Expr) :=
    operation.isAppOfArity ``CIL.Safety.read 4 ||
      operation.isAppOfArity ``CIL.Safety.readSnapshot 4 ||
      operation.isAppOfArity ``CIL.Safety.write 4
  let mut prepared := facts
  for fact in facts do
    unless ← suppliedFactSatisfies fact (fun type => forallTelescope type fun _ conclusion => do
        if conclusion.isAppOfArity ``And 2 then return true
        let some (_, operation, _) := conclusion.consumeMData.eq? | return false
        return operationEquation operation) do continue
    let saved ← saveState
    try
      let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm fact none
      for part in ← equationConjuncts operationEquation proof do
        let derived ← forallTelescope (← inferType part) fun variables conclusion => do
          let some (_, operation, _) := conclusion.consumeMData.eq? | return #[]
          let reading := operation.isAppOfArity ``CIL.Safety.read 4
          let snapshot := operation.isAppOfArity ``CIL.Safety.readSnapshot 4
          let applied := mkAppN part variables
          let mut candidates : Array (Name × Array Expr) := #[]
          if reading then
            candidates := candidates.push (``loadSnapshot_aggregate_of_read, #[applied])
          if snapshot then
            candidates := candidates.push (``loadSnapshot_aggregate_of_readSnapshot, #[applied])
          if !snapshot then
            let arguments := operation.getAppArgs
            let width := if reading then some arguments[2]! else
              let bytes := arguments[2]!
              if bytes.isAppOfArity ``numberBytes 2 then some bytes.appArg! else none
            if let some width := width then
              if let some width ← (Lean.Meta.evalNat (← reduce width)).run then
                if reading && [1, 2, 4].contains width then
                  let scalar ← mkDecideProof (mkApp (mkConst ``ScalarWidth) (mkNatLit width))
                  candidates := candidates ++ #[(``load_scalar_of_read, #[scalar, applied]),
                    (``load_scalar_signed_of_read, #[scalar, applied])]
                else
                  let bridge := match reading, width with
                    | true, 8 => ``load_word64_of_read
                    | true, 16 => ``load_vector128_of_read
                    | true, 32 => ``load_vector256_of_read
                    | true, 64 => ``load_vector512_of_read
                    | false, 8 => ``step_store64_of_write
                    | false, 1 | false, 2 | false, 4 => ``step_storeScalar_of_write
                    | false, 16 => ``step_store128_of_write
                    | false, 32 => ``step_store256_of_write
                    | false, 64 => ``step_store512_of_write
                    | _, _ => Name.anonymous
                  unless bridge.isAnonymous do candidates := candidates.push (bridge, #[applied])
          let mut results := #[]
          for (bridge, arguments) in candidates do
            let before ← getMCtx
            try
              let result ← mkAppM bridge arguments
              let result ← instantiateMVars (← mkLambdaFVars variables result)
              if result.hasMVar then setMCtx before
              else results := results.push result
            catch _ => setMCtx before
          return results
        for result in derived do
          prepared := prepared.push (← Term.exprToSyntax result)
    catch _ => saved.restore
  return prepared

open Lean Elab Tactic in
/-- Normalise `CIL.truth` and `facts` once for a stepping loop, then build its tactic from the
    raw and normalised facts; per-step normalisation would re-simp every local fact on every
    instruction. -/
def cilWithNormalisedFacts (facts : Array Term)
    (body : Array Term → Array Term → TacticM Syntax) : TacticM Unit :=
  withMainContext do
    let prepared ←
      normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
        (← prepareOperationFacts (#[← `(CIL.truth)] ++ facts))
    withMainContext <| evalTactic (← body facts prepared)

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_step [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config (← prepareOperationFacts facts.getElems)
    withMainContext <| evalTactic (← `(tactic| cil_checked_step_normalized [$[$prepared:term],*]))

open Lean Elab Tactic in
/-- What a stepping tactic outside a loop steps with: `facts` and the object evidence facts its
    context gives (`gatherEvidenceFacts`), each normalised once. -/
def prepareStepFacts (facts : Array Term) : TacticM (Array Term) := do
  normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
    (← prepareOperationFacts (← gatherEvidenceFacts facts))

/-- `cil_checked_steps` with facts already normalised: enters an `invoke` goal through
    `cil_checked_entry`, then takes checked `run` steps until the goal closes or a step fails,
    leaving that goal. Fails if it takes no step. -/
syntax "cil_checked_steps_normalized" "[" term,* "]" : tactic

/-- Takes a fetched `ret` through `run_return`, given the method and instruction lookups, and
    leaves the equation between the returned state and the stated result unless frame cleanup,
    `rfl` or simp with `facts` closes it. -/
macro "cil_checked_return_at " methodFound:term:max instructionFound:term:max
    "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_strict refine Eq.trans (CIL.Safety.run_return $methodFound $instructionFound
      (by cil_checked_step_normalized [$[$facts:term],*])
      (by cil_checked_side [$[$facts:term],*])) ?_
    try simp only [CIL.Safety.leaveFrame, List.foldl_nil, List.nil_append, List.append_nil,
      CIL.NarrowKind.extend_ite_one_zero, CIL.NarrowKind.extend_ite_ofNat_one_zero,
      List.reverse_cons, List.reverse_nil, cil_literal, BitVec.isValue,
      Bool.false_eq_true, ite_true, ite_false]
    try with_reducible rfl
    try (with_reducible simp [$[$facts:term],*]; done)))

/-- Takes a fetched step that continues in the same method through `run_next`, given the
    lookups, leaving the `run` goal at the next state. The step proof is elaborated before the
    continuation goal exists, so step facts can still assign reference and frame metavariables. -/
macro "cil_checked_next_at " methodFound:term:max instructionFound:term:max
    "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_strict refine Eq.trans (CIL.Safety.run_next $methodFound $instructionFound
      (by cil_checked_step_normalized [$[$facts:term],*])) ?_
    cil_stack_cleanup))

/-- Takes a fetched step that faults through `run_fault`, given the lookups; the goal's
    located fault fixes the fault the step must raise. -/
macro "cil_checked_fault_at " methodFound:term:max instructionFound:term:max
    "[" facts:term,* "]" : tactic =>
  `(tactic| cil_strict exact CIL.Safety.run_fault $methodFound $instructionFound
    (by cil_checked_step_normalized [$[$facts:term],*]))

/-- Close a child invocation with supplied exact-run or invocation-certificate evidence. -/
syntax "cil_checked_child" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_checked_child [$facts:term,*]) => withMainContext do
    let mut candidates := facts.getElems
    for declaration in ← getLCtx do
      unless declaration.isImplementationDetail do
        let type := declaration.type.consumeMData
        if type.isAppOf `CIL.Safety.InvocationCertificate ||
            (type.eq?.any fun (_, left, _) => left.isAppOf ``CIL.Safety.invoke) then
          candidates := candidates.push (← Term.exprToSyntax declaration.toExpr)
    let mut attempted : Array Expr := #[]
    let target ← instantiateMVars (← getMainTarget)
    for candidate in candidates do
      let saved ← saveState
      try
        let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm candidate none
        if attempted.contains proof then
          throwError "Already considered this invocation fact"
        attempted := attempted.push proof
        let type := (← instantiateMVars (← inferType proof)).consumeMData
        let invocationType ← if type.isAppOf `CIL.Safety.InvocationCertificate then
          inferType (← mkAppM ``And.left #[proof])
        else pure type
        if let some (_, provided, _) := invocationType.eq? then
          if let some (_, requested, _) := target.eq? then
            if provided.isAppOf ``CIL.Safety.invoke && requested.isAppOf ``CIL.Safety.invoke then
              let providedFuel ← getNatValue? provided.getAppArgs[1]!
              let requestedFuel ← getNatValue? requested.getAppArgs[1]!
              -- An abstract program cannot reduce to reconcile different concrete budgets.
              let program := requested.getAppArgs[0]!
              -- Only a local program has a declaration; a nested `←` would also run on a constant.
              let abstract ← if program.isFVar then
                  pure (← program.fvarId!.getDecl).value?.isNone
                else pure false
              if abstract && provided.getAppArgs[0]! == program then
                if let some supplied := providedFuel then
                  if let some needed := requestedFuel then
                    if supplied != needed then
                      throwError "Child invocation has a different concrete fuel budget"
        if type.isAppOf `CIL.Safety.InvocationCertificate then
          evalTactic (← `(tactic| cil_strict exact ($candidate).1))
        else if type.eq?.any (fun (_, left, _) => left.isAppOf ``CIL.Safety.invoke) then
          evalTactic (← `(tactic| cil_strict exact $candidate))
        else throwError "Not an invocation fact"
        return
      catch _ => saved.restore
    throwError "No child invocation evidence matches the requested fuel and state"

/-- Takes a fetched call through `run_call_of_invoke`, given the lookups: the callee runs to its
    return, and the caller's continuation, on the returned values, stays open as the goal. -/
macro "cil_checked_call_open_at " methodFound:term:max instructionFound:term:max
    "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_strict refine CIL.Safety.run_call_of_invoke $methodFound $instructionFound
      (by cil_checked_step_normalized [$[$facts:term],*])
      (by first | cil_checked_child [$[$facts:term],*]
                | (cil_checked_steps_normalized [$[$facts:term],*]; done)) ?_
    cil_stack_cleanup))

open Lean Elab Tactic Meta in
/-- Instantiate `lemma` against the goal through `select`, close its method and instruction
    lookups (the premises `lookups` places from the end) with `cil_lookup`, and return both
    proofs as syntax with the fetched opcode's constructor. -/
def cilFetchedOp (lemma : Lean.Name) (select : Lean.Expr → Option Lean.Expr) (lookups : Nat)
    (facts : Array Lean.Term) : Lean.Elab.Tactic.TacticM (Lean.Term × Lean.Term × Lean.Name) := do
  -- A tactic `have` leaves the target under `mdata`, which `select` (`Expr.eq?`) does not see
  -- through.
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let (premises, _, conclusion) ←
    forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels lemma))
  let some goalPart := select target | throwError "The goal does not have the shape of {lemma}"
  let some lemmaPart := select conclusion | throwError "Unexpected statement of {lemma}"
  unless ← isDefEq lemmaPart goalPart do throwError "The goal does not have the shape of {lemma}"
  let methodFound := premises[premises.size - lookups]!
  let instructionFound := premises[premises.size - lookups + 1]!
  for proof in [methodFound, instructionFound] do
    let remaining ← Tactic.run proof.mvarId! (evalTactic (← `(tactic| cil_lookup [$facts,*])))
    unless remaining.isEmpty do throwError "The method or instruction lookup did not close"
  let fetched ← instantiateMVars (← inferType instructionFound)
  let some (_, _, found) := fetched.eq? | throwError "Unexpected instruction lookup"
  let operation :=
    ((← cilReducedOp? found.appArg!).bind (·.getAppFn.constName?)).getD Name.anonymous
  return (← Term.exprToSyntax (← instantiateMVars methodFound),
    ← Term.exprToSyntax (← instantiateMVars instructionFound), operation)

open Lean Elab Tactic Meta in
/-- Whether the main goal is an equation whose right side is syntactically `Except.error`. -/
def cilGoalStatesFault : TacticM Bool := withMainContext do
  return (← instantiateMVars (← getMainTarget)).consumeMData.eq?.any
    fun (_, _, result) => result.isAppOf ``Except.error

/-- Enters an `invoke` goal through `invoke_of_run_fault` when it states `.error`, else through
    `invoke_of_run`, and leaves the goal unchanged when entry fails. A goal already about `run`
    tries neither, since unifying an entry lemma against it costs a failed defeq check. -/
syntax "cil_checked_entry" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_checked_entry [$facts:term,*]) => withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.eq?.any (·.2.1.consumeMData.isAppOf ``CIL.Safety.run) then return
    let entry := mkIdent (if ← cilGoalStatesFault then ``CIL.Safety.invoke_of_run_fault
      else ``CIL.Safety.invoke_of_run)
    evalTactic (← `(tactic| try
      (cil_strict apply $entry
       · cil_lookup [$facts,*]
       · cil_checked_side [$facts,*]
       · cil_checked_side [$facts,*])))

/-- Whether an opcode steps to a call action: `call`, or `callvirt` with a non-null receiver. -/
def callsCallee (operation : Lean.Name) : Bool :=
  operation == ``CIL.Op.call || operation == ``CIL.Op.callInstance ||
    operation == ``CIL.Op.callVirtual

open Lean Elab Tactic Meta in
/-- One `run` step: prove the method and instruction lookups once, then apply only the
    composition lemma for the fetched opcode. A call proves its callee and leaves the caller's
    continuation as the goal. Toward a stated fault, a step that raises it ends the run. -/
def cilRunStep (facts : Array Term) : TacticM Unit := withMainContext do
  -- `run_fault` can close only at the pc the stated fault names; elsewhere it only costs.
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let faulting ← match target.eq? with
    | some (_, current, result) =>
      if !result.isAppOf ``Except.error then pure false
      else
        let located := result.appArg!.consumeMData
        if located.isAppOfArity ``CIL.Safety.LocatedFault.mk 3 &&
            current.isAppOfArity ``CIL.Safety.run 8 then
          withNewMCtxDepth <| withTransparency .instances <|
            isDefEq located.getAppArgs[1]! current.getAppArgs[3]!
        else pure true
    | none => pure false
  let (methodSyntax, instructionSyntax, operation) ←
    cilFetchedOp ``CIL.Safety.run_next (fun e => e.eq?.map (·.2.1)) 3 facts
  -- An object construction runs its constructor as a call before continuing in the caller.
  let constructs := operation == ``CIL.Op.newObject
  -- These fault before their callee runs: a short heap budget, a null receiver, or a receiver
  -- whose class a dispatch table omits.
  let faultsFirst := constructs || operation == ``CIL.Op.callInstance ||
    operation == ``CIL.Op.callVirtual
  evalTactic (← if operation == ``CIL.Op.ret then
      `(tactic| cil_checked_return_at $methodSyntax $instructionSyntax [$facts,*])
    else if callsCallee operation || constructs then
      let call ← `(tactic| cil_checked_call_open_at $methodSyntax $instructionSyntax [$facts,*])
      if faulting && faultsFirst then
        `(tactic| first
          | cil_checked_fault_at $methodSyntax $instructionSyntax [$facts,*]
          | $call:tactic)
      else pure call
    else if faulting then
      `(tactic| first
        | cil_checked_fault_at $methodSyntax $instructionSyntax [$facts,*]
        | cil_checked_next_at $methodSyntax $instructionSyntax [$facts,*])
    else
      `(tactic| cil_checked_next_at $methodSyntax $instructionSyntax [$facts,*]))

/-- One `run` step of the goal, chosen by the fetched opcode; at a call it proves the callee and
    leaves the caller's continuation. -/
syntax "cil_checked_run_step" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| cil_checked_run_step [$facts:term,*]) => cilRunStep facts.getElems

macro_rules
  | `(tactic| cil_checked_steps_normalized [$facts:term,*]) =>
  `(tactic| (
    try (conv => lhs; arg 2; cil_reduce_fuel)
    cil_checked_entry [$[$facts:term],*]
    cil_steps_from "cil_checked_steps took no step: the method or instruction lookup, or the \
      first step, did not close; pass the lookup hypothesis, feature facts or step facts"
      cil_checked_run_step [$[$facts:term],*]))

/-- Proves an `invoke` or `run` goal, returning or stating a located fault, by checked
    stepping with `facts` and the object evidence facts of the context, such as `live.formed` of
    a `LiveObject` and the load a scalar field's `Readable` gives, normalised once at entry. A goal
    `∃ fuel, invoke ..` takes the execution bound of its method as the fuel, and the projections
    of a defined contract are unfolded. Stops at the first step it cannot take, leaving that
    goal; fails if it takes none. -/
syntax "cil_checked_steps" "[" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_steps [$facts:term,*]) => do
    evalTactic (← `(tactic| (cil_supply_fuel; cil_unfold_contracts)))
    let prepared ← prepareStepFacts facts.getElems
    withMainContext <| evalTactic (← `(tactic| cil_checked_steps_normalized [$[$prepared:term],*]))

/-- `cil_checked_steps` with no facts. -/
macro "cil_checked_steps" : tactic => `(tactic| cil_checked_steps [])

/-- Exactly `n` fetched steps of the left-hand `run`, for run-to-run goals whose target state
    is not syntactically the stepped one; unbounded stepping would run past it when the fuel is
    a literal. -/
syntax "cil_checked_steps " num " [" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_steps $count:num [$facts:term,*]) => do
    let prepared ← prepareStepFacts facts.getElems
    -- Focus the original goal: an early close must error, not step into an unrelated pending goal.
    focus do
      for taken in [:count.getNat] do
        if (← getGoals).isEmpty then
          throwError "cil_checked_steps {count.getNat}: the goal closed after {taken} steps"
        cilRunStep prepared
      -- Fold the stepped pc (`2 + 1`) so the residual matches a target stated with a numeral.
      unless (← getGoals).isEmpty do
        evalTactic (← `(tactic| try (conv => lhs; arg 4; simp only [Nat.reduceAdd])))

/-- `cil_checked_steps n` with no facts. -/
macro "cil_checked_steps " count:num : tactic => `(tactic| cil_checked_steps $count [])

end CIL.Safety
