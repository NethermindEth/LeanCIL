import CIL.SymbolicExecution
import CIL.StepEquations
import CIL.Safety.Equations
import CIL.Safety.StepComposition
import CIL.Safety.ValueSteps
import CIL.Safety.MemorySteps
import CIL.Safety.CallComposition

namespace CIL.Safety

open Lean Elab Tactic Conv in
elab "cil_reduce_fuel" : conv => do
  changeLhs (← Meta.reduce (← getLhs))

-- Failed candidate proofs must backtrack, rather than be recovered as admitted
-- terms. Only the candidate's own errors count, so an earlier failed tactic cannot reject it.
open Lean Elab Tactic in
elab "cil_strict " tactic:tactic : tactic =>
  Meta.withAssignableSyntheticOpaque <| Term.withoutErrToSorry <| withoutRecover do
    let errors := fun (log : MessageLog) =>
      log.reportedPlusUnreported.foldl (fun count m => if m.severity matches .error then count + 1 else count) 0
    let earlier := errors (← Core.getMessageLog)
    evalTactic tactic
    if errors (← Core.getMessageLog) > earlier then throwError "Checked step candidate failed"

/-- `simp config [lemmas, facts]`, adding each local fact normalised by the default simp set and the non-local facts. -/
syntax "cil_fact_simp" Lean.Parser.Tactic.optConfig " [" term,* "]" " [" term,* "]" : tactic

-- The goal's subterms reach simp-normal form before a hypothesis can rewrite them,
-- so a fact stated in another form would never fire. Originals stay in the simp set.
initialize Lean.registerTraceClass `CIL.factNormalize

open Lean Elab Tactic Meta in
/-- `proof` and, for a fact over `Fin n` (n <= 64) or over every `Feature`, its instance at each value:
    the profile fields and indexed lemmas are reached only through concrete arguments. -/
def factInstances (proof : Expr) : TermElabM (Array Expr) := do
  let mut instances := #[proof]
  if let .forallE _ domain _ _ := ← whnf (← instantiateMVars (← inferType proof)) then
    let domain ← whnf domain
    if domain.isAppOfArity ``Fin 1 then
      if let some size ← getNatValue? domain.appArg! then
        if size <= 64 then
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
def normaliseStepFacts (config : TSyntax `Lean.Parser.Tactic.optConfig)
    (facts : Array Term) : TacticM (Array Term) := withMainContext do
    let isLocal (fact : Term) : TacticM Bool :=
      return fact.raw.isIdent && ((← getLCtx).findFromUserName? fact.raw.getId).isSome
    let locals ← facts.filterM isLocal
    let supplied ← facts.filterM fun fact => return !(← isLocal fact)
    let mut normalised : Array Term := #[]
    -- Asserts each instance of `proof` in the normaliser's form; the unchanged original is already a fact.
    let assertInstances (proof : Expr) (base : Name) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) :
        TacticM (Array Term) := withMainContext do
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
      -- `cil_step` reduces a pushed `evaluate` and a method's profile projection, so facts must land there too.
      let normaliser ← `(tactic| simp $config:optConfig [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat,
        CIL.FeatureProfile.evaluate, CIL.Safety.reduceMethodProfile, $[$supplied:term],*])
      let { ctx, simprocs, .. } ← mkSimpContext normaliser (eraseLocal := false)
      for fact in locals do
        let some decl := (← getLCtx).findFromUserName? fact.raw.getId | continue
        unless ← isProp (← instantiateMVars decl.type) do continue
        trace[CIL.factNormalize] "{decl.userName}"
        normalised := normalised ++ (← assertInstances decl.toExpr decl.userName ctx simprocs)
    -- A proof term such as `(show p from h)` is normalised like a local fact, without itself as a lemma,
    -- which would rewrite its own statement to `True`. Global names stay as given (most are unfolds),
    -- except theorems about `evaluate` or a method's profile, which `cil_step` rewrites past.
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
      let normaliser ← `(tactic| simp $config:optConfig [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat,
        CIL.FeatureProfile.evaluate, CIL.Safety.reduceMethodProfile, $[$others:term],*])
      let { ctx, simprocs, .. } ← mkSimpContext normaliser (eraseLocal := false)
      let names ← assertInstances proof `supplied ctx simprocs
      if names.isEmpty then saved.restore; continue
      normalised := normalised ++ names
    return facts ++ normalised

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_fact_simp $config:optConfig [$lemmas:term,*] [$facts:term,*]) => do
    let prepared ← normaliseStepFacts config facts.getElems
    let all := lemmas.getElems ++ #[← `(term| cil_guard), ← `(term| CIL.fin_val_three), ← `(term| CIL.fin_mk_ofNat)] ++ prepared
    withMainContext <| evalTactic (← `(tactic| simp $config:optConfig [$[$all:term],*]))

/-- Run `tactic` once, failing with `message` when it does not apply, then repeat it. -/
macro "cil_steps_from " message:str tactic:tacticSeq : tactic =>
  `(tactic| ((first | $tactic | fail $message); repeat $tactic))

/-- Close a method or instruction lookup by evaluation for an extraction, else from a lookup hypothesis,
    else by rewriting feature tests in a profile-dependent body with the supplied facts. -/
syntax "cil_lookup" "[" term,* "]" : tactic

-- Reducible `assumption` keeps a failed candidate lookup from unfolding every hypothesis.
macro_rules
  | `(tactic| cil_lookup [$facts:term,*]) =>
  `(tactic| first
    | with_reducible assumption
    | (simp only [cil_code, Nat.reduceAdd]; rfl)
    | rfl
    | (simp only [cil_code, Nat.reduceAdd, $[$facts:term],*]; done)
    | (simp only [cil_code, Nat.reduceAdd, $[$facts:term],*]; rfl))

macro "cil_stack_cleanup" : tactic =>
  `(tactic| try simp only [List.drop_succ_cons, List.drop_zero, List.drop_nil,
    List.take_succ_cons, List.take_zero, List.take_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.append_nil])

macro "cil_checked_step_by_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       simp only [cil_step, cil_guard, CIL.Safety.instructionStep]
       try simp [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.checkedValue, CIL.Safety.numericValue, CIL.Safety.scalars,
         CIL.Safety.formValue, CIL.Safety.checkedAt, CIL.Safety.leaveFrame, Except.mapError, Bind.bind,
         Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

-- Only memory equations expose `referenceAt`; its equations in the generic list would slow every other step.
macro "cil_checked_memory_by_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       simp only [cil_step, cil_guard, CIL.Safety.instructionStep]
       try simp [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.checkedValue, CIL.Safety.numericValue, CIL.Safety.scalars,
         CIL.Safety.formValue, CIL.Safety.checkedAt, CIL.Safety.referenceAt_null, CIL.Safety.referenceAt_address, CIL.Safety.leaveFrame, Except.mapError, Bind.bind,
         Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

macro "cil_checked_step_by_unfolding " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       fail_if_success simp only [cil_step]
       simp [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.step, CIL.Safety.checkedValue, CIL.Safety.numericValue,
        CIL.Safety.pureArity, CIL.Safety.scalars, CIL.Safety.leaveFrame, CIL.step,
        $[$facts:term],*] <;> (repeat constructor) <;> rfl))

macro "cil_checked_step_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| first
    | cil_checked_step_by_equations [$[$facts:term],*]
    | cil_checked_step_by_unfolding [$[$facts:term],*])

-- A fact at the `memoryInstruction` level fails once a per-shape memory equation rewrites past it,
-- so the elaborator retries such facts through the generic `step_memory_eq`.
macro "cil_checked_memory_retry " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       rw [CIL.Safety.step_memory_eq]
       try simp only [cil_guard]
       try simp [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.checkedValue, CIL.Safety.numericValue, CIL.Safety.scalars,
         CIL.Safety.formValue, CIL.Safety.checkedAt, CIL.Safety.referenceAt_null, CIL.Safety.referenceAt_address, CIL.Safety.leaveFrame, Except.mapError, Bind.bind,
         Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

open Lean Elab Tactic Meta in
/-- Whether a supplied fact is, or is stated about, `memoryInstruction` or `staticInstruction`;
    a compound term is assumed to be. -/
def mentionsMemoryInstruction (facts : Array Term) : TacticM Bool := withMainContext do
  let legacy := fun (e : Expr) => (e.find? fun sub =>
    sub.isConstOf ``CIL.Safety.memoryInstruction || sub.isConstOf ``CIL.Safety.staticInstruction).isSome
  facts.anyM fun fact => do
    unless fact.raw.isIdent do return true
    if let some decl := (← getLCtx).findFromUserName? fact.raw.getId then
      return legacy (← instantiateMVars decl.type)
    let some name ← observing? <| realizeGlobalConstNoOverloadWithInfo fact.raw | return true
    let info ← getConstInfo name
    return name == ``CIL.Safety.memoryInstruction || name == ``CIL.Safety.staticInstruction || legacy info.type

macro "cil_checked_intrinsic " "[" facts:term,* "]" : tactic =>
  `(tactic| (
    simp only [cil_step, cil_guard, CIL.Intrinsic.available, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceLT, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ite_false, ite_true, List.take_succ_cons, List.take_zero, List.take_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.append_nil,
      List.drop_succ_cons, List.drop_zero, List.drop_nil, CIL.Safety.scalars,
      CIL.Safety.numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure,
      BitVec.ofInt_ofNat, cil_eval, $[$facts:term],*]
    all_goals simp only [CIL.Safety.checkedIntrinsic, cil_guard, cil_eval, $[$facts:term],*,
      List.any_cons, List.any_nil, Bool.false_or, Bool.true_or, Bool.or_false,
      Bool.false_eq_true, ite_false, CIL.Safety.checkedValue, CIL.Safety.numericValue, ite_true,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    all_goals (first | rfl | cil_checked_step_equations [$[$facts:term],*])))

open Lean Meta in
/-- The opcode constructor `op` denotes, when its head reduces to one: a body that picks an opcode with a
    decided `if` would otherwise match no step equation and unfold the whole dispatcher. -/
def cilReducedOp? (op : Expr) : MetaM (Option Expr) := do
  let reduced ← whnfD (← instantiateMVars op)
  let some name := reduced.getAppFn.constName? | return none
  let some (.ctorInfo info) := (← getEnv).find? name | return none
  return if info.induct == ``CIL.Op then some reduced else none

syntax "cil_checked_step_normalized" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_checked_step_normalized [$facts:term,*]) => withMainContext do
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
    let scalar := #[``CIL.Op.nop, ``CIL.Op.neg, ``CIL.Op.gt, ``CIL.Op.convI1,
      ``CIL.Op.convI2, ``CIL.Op.convU2, ``CIL.Op.convI8, ``CIL.Op.convI4,
      ``CIL.Op.convU1, ``CIL.Op.convU4, ``CIL.Op.convU8, ``CIL.Op.convU,
      ``CIL.Op.bnot, ``CIL.Op.add, ``CIL.Op.sub, ``CIL.Op.mul, ``CIL.Op.band,
      ``CIL.Op.bor, ``CIL.Op.bxor, ``CIL.Op.shl, ``CIL.Op.shr, ``CIL.Op.shrUn,
      ``CIL.Op.lt, ``CIL.Op.ltu, ``CIL.Op.gtu, ``CIL.Op.eq].contains operation
    let strategy ← if scalar then
        `(tactic| first | rfl | cil_checked_step_equations [$facts:term,*])
      else if operation == ``CIL.Op.intrinsic then
        `(tactic| cil_checked_intrinsic [$facts:term,*])
      else if operation == ``CIL.Op.memory then
        let saved ← saveState
        -- Without recovery, `all_goals` throws its error instead of logging it and aborting.
        let attempt := fun (tactic : Syntax) => do
          try withoutRecover (evalTactic tactic); return none
          catch error => saved.restore; return some error
        let some equationError ← attempt (← `(tactic| cil_checked_memory_by_equations [$facts:term,*])) | return
        let progressed := (← attempt (← `(tactic| simp only [cil_step]))).isNone
        saved.restore
        let unfolding ← `(tactic| cil_checked_step_by_unfolding [$facts:term,*])
        let some unfoldingError ← (if progressed then pure (some equationError) else attempt unfolding) | return
        if ← mentionsMemoryInstruction facts.getElems then
          if (← attempt (← `(tactic| cil_checked_memory_retry [$facts:term,*]))).isNone then return
        -- Report the per-shape goal, where facts belong, rather than the legacy retry's.
        throw unfoldingError
      else
        `(tactic| cil_checked_step_equations [$facts:term,*])
    evalTactic strategy

syntax "cil_checked_step" "[" term,* "]" : tactic

open Lean Elab Tactic in
/-- Normalise `CIL.truth` and `facts` once for a stepping loop, then build its tactic from the raw and
    normalised facts; per-step normalisation would re-simp every local fact on every instruction. -/
def cilWithNormalisedFacts (facts : Array Term) (body : Array Term → Array Term → TacticM Syntax) : TacticM Unit :=
  withMainContext do
    let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|)) (#[← `(CIL.truth)] ++ facts)
    withMainContext <| evalTactic (← body facts prepared)

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_step [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config facts.getElems
    withMainContext <| evalTactic (← `(tactic| cil_checked_step_normalized [$[$prepared:term],*]))

/-- Execute checked instructions using extracted lookups and proved semantic facts.
    Unresolved memory and arithmetic conditions remain proof obligations. -/
syntax "cil_checked_steps_normalized" "[" term,* "]" : tactic

macro "cil_checked_return_at " methodFound:term:max instructionFound:term:max "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_strict refine Eq.trans (CIL.Safety.run_return $methodFound $instructionFound
      (by cil_checked_step_normalized [$[$facts:term],*])
      (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl))) ?_
    try simp only [CIL.Safety.leaveFrame, List.foldl_nil, List.nil_append, List.append_nil,
      CIL.NarrowKind.extend_ite_one_zero, CIL.NarrowKind.extend_ite_ofNat_one_zero,
      List.reverse_cons, List.reverse_nil, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.reduceOfInt, BitVec.isValue,
      Nat.reduceMod, Bool.false_eq_true, ite_true, ite_false]
    try with_reducible rfl
    try (with_reducible simp [$[$facts:term],*]; done)))

-- Elaborate the step proof before creating the continuation goal, so reference/frame
-- metavariables remain assignable by the step facts.
macro "cil_checked_next_at " methodFound:term:max instructionFound:term:max "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_strict refine Eq.trans (CIL.Safety.run_next $methodFound $instructionFound
      (by cil_checked_step_normalized [$[$facts:term],*])) ?_
    cil_stack_cleanup))

macro "cil_checked_call_at " methodFound:term:max instructionFound:term:max "[" facts:term,* "]" : tactic =>
  `(tactic| cil_strict refine CIL.Safety.run_call_of_invoke $methodFound $instructionFound
    (by cil_checked_step_normalized [$[$facts:term],*])
    (by cil_checked_steps_normalized [$[$facts:term],*]; done)
    (by cil_checked_steps_normalized [$[$facts:term],*]; done))

-- The callee runs to its return, but the caller's continuation stays open as the goal.
macro "cil_checked_call_open_at " methodFound:term:max instructionFound:term:max "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_strict refine CIL.Safety.run_call_of_invoke $methodFound $instructionFound
      (by cil_checked_step_normalized [$[$facts:term],*])
      (by cil_checked_steps_normalized [$[$facts:term],*]; done) ?_
    cil_stack_cleanup))

open Lean Elab Tactic Meta in
/-- Instantiate `lemma` against the goal through `select`, close its method and instruction lookups
    (the premises `lookups` places from the end) with `cil_lookup`, and return both proofs as syntax
    with the fetched opcode's constructor. -/
def cilFetchedOp (lemma : Lean.Name) (select : Lean.Expr → Option Lean.Expr) (lookups : Nat)
    (facts : Array Lean.Term) : Lean.Elab.Tactic.TacticM (Lean.Term × Lean.Term × Lean.Name) := do
  -- A tactic `have` leaves the target under `mdata`, which `select` (`Expr.eq?`) does not see through.
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let (premises, _, conclusion) ← forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels lemma))
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
  let operation := ((← cilReducedOp? found.appArg!).bind (·.getAppFn.constName?)).getD Name.anonymous
  return (← Term.exprToSyntax (← instantiateMVars methodFound),
    ← Term.exprToSyntax (← instantiateMVars instructionFound), operation)

open Lean Elab Tactic Meta in
/-- One `run` step: prove the method and instruction lookups once, then apply only the composition
    lemma for the fetched opcode. With `openCall`, a call leaves the caller's continuation as the goal. -/
def cilRunStep (facts : Array Term) (openCall : Bool) : TacticM Unit := withMainContext do
  let (methodSyntax, instructionSyntax, operation) ←
    cilFetchedOp ``CIL.Safety.run_next (fun e => e.eq?.map (·.2.1)) 3 facts
  evalTactic (← if operation == ``CIL.Op.ret then
      `(tactic| cil_checked_return_at $methodSyntax $instructionSyntax [$facts,*])
    else if operation == ``CIL.Op.call then
      if openCall then `(tactic| cil_checked_call_open_at $methodSyntax $instructionSyntax [$facts,*])
      else `(tactic| cil_checked_call_at $methodSyntax $instructionSyntax [$facts,*])
    else
      `(tactic| cil_checked_next_at $methodSyntax $instructionSyntax [$facts,*]))

syntax "cil_checked_run_step" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| cil_checked_run_step [$facts:term,*]) => cilRunStep facts.getElems false

macro_rules
  | `(tactic| cil_checked_steps_normalized [$facts:term,*]) =>
  `(tactic| (
    try (conv => lhs; arg 2; cil_reduce_fuel)
    try (cil_strict apply CIL.Safety.invoke_of_run
         · cil_lookup [$[$facts:term],*]
         · first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl)
         · first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl))
    cil_steps_from "cil_checked_steps took no step: the method or instruction lookup, or the first step, did not close; pass the lookup hypothesis, feature facts or step facts"
      cil_checked_run_step [$[$facts:term],*]))

syntax "cil_checked_steps" "[" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_steps [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config facts.getElems
    withMainContext <| evalTactic (← `(tactic| cil_checked_steps_normalized [$[$prepared:term],*]))

macro "cil_checked_steps" : tactic => `(tactic| cil_checked_steps [])

/-- Exactly `n` fetched steps of the left-hand `run`, for run-to-run goals whose target state is not
    syntactically the stepped one; unbounded stepping would run past it when the fuel is a literal. -/
syntax "cil_checked_steps " num " [" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_steps $count:num [$facts:term,*]) => do
    let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|)) facts.getElems
    -- Focus the original goal: an early close must error, not step into an unrelated pending goal.
    focus do
      for taken in [:count.getNat] do
        if (← getGoals).isEmpty then
          throwError "cil_checked_steps {count.getNat}: the goal closed after {taken} steps"
        cilRunStep prepared true
      -- Fold the stepped pc (`2 + 1`) so the residual matches a target stated with a numeral.
      unless (← getGoals).isEmpty do
        evalTactic (← `(tactic| try (conv => lhs; arg 4; simp only [Nat.reduceAdd])))

macro "cil_checked_steps " count:num : tactic => `(tactic| cil_checked_steps $count [])

end CIL.Safety
