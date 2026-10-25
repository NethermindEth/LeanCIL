import CIL.SymbolicExecution
import CIL.StepEquations
import CIL.Safety.Equations
import CIL.Safety.StepComposition
import CIL.Safety.ValueSteps
import CIL.Safety.MemorySteps
import CIL.Safety.CallComposition

/-!
# Checked symbolic execution

The stepping tactics for the checked interpreter. `cil_checked_steps [facts]` proves an
`invoke` or `run` goal about a method by fetching each instruction, closing its lookup with
`cil_lookup`, rewriting the step with the `@[cil_step]` equations and the facts, and composing
steps through `run_next`, `run_return` and `run_call_of_invoke`. Facts are normalised once,
at entry, to the form stepping leaves goals in. The contract and loop tactics, the automation
tests and downstream proofs all build on these; `docs/PROOFS.md` describes their use.
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
        CIL.fin_mk_ofNat, CIL.FeatureProfile.evaluate, CIL.Safety.reduceMethodProfile,
        $[$supplied:term],*])
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
        CIL.fin_mk_ofNat, CIL.FeatureProfile.evaluate, CIL.Safety.reduceMethodProfile,
        $[$others:term],*])
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

/-- A lookup that finds `a` finds every `b` equal to it. -/
theorem getElem?_eq_some_of_eq {α : Type u} {l : List α} {i : Nat} {a b : α}
    (found : l[i]? = some a) (reduced : a = b) : l[i]? = some b := by subst reduced; exact found

#print axioms getElem?_eq_some_of_eq

/-- Close `l[i]? = some x` by `rfl`, deciding a fetched feature `if` with `facts` first so the
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
      goal.assign (← mkAppM ``CIL.Safety.getElem?_eq_some_of_eq #[fetchedOp, ← reduced.getProof])
      replaceMainGoal []
    catch _ => fetched.restore

-- Reducible `assumption` keeps a failed candidate lookup from unfolding every hypothesis.
-- A branch leaves `(v != 0) = true` in the pc: the negation lemmas decide it from
-- `Not (v = 0)`, and the trailing `rfl` decides it once `v = 0` or a literal closes it.
macro_rules
  | `(tactic| cil_lookup [$facts:term,*]) =>
  `(tactic| first
    | with_reducible assumption
    | (simp only [cil_code, Nat.reduceAdd]; cil_lookup_rfl [$[$facts:term],*])
    | cil_lookup_rfl [$[$facts:term],*]
    | (simp only [cil_code, Nat.reduceAdd, bne_iff_ne, ne_eq, not_false_eq_true,
        Bool.false_eq_true, ite_true, ite_false, ↓reduceIte, $[$facts:term],*]; done)
    | (simp only [cil_code, Nat.reduceAdd, bne_iff_ne, ne_eq, not_false_eq_true,
        Bool.false_eq_true, ite_true, ite_false, ↓reduceIte, $[$facts:term],*]; rfl))

/-- Normalises the literal `take`, `drop`, `reverse` and `++` a step leaves on the stack;
    never fails. -/
macro "cil_stack_cleanup" : tactic =>
  `(tactic| try simp only [List.drop_succ_cons, List.drop_zero, List.drop_nil,
    List.take_succ_cons, List.take_zero, List.take_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.append_nil])

/-- Closes a checked `step` goal by rewriting with the `@[cil_step]` equations, failing if
    nothing rewrites, then by the checked-value definitions and `facts`, constructors and `rfl`. -/
macro "cil_checked_step_by_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       simp only [cil_step, cil_guard, CIL.Safety.instructionStep]
       try simp [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.checkedValue,
         CIL.Safety.numericValue, CIL.Safety.scalars, CIL.Safety.formValue, CIL.Safety.checkedAt,
         CIL.Safety.leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
         $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

/-- `cil_checked_step_by_equations` for a `.memory` step, also rewriting `referenceAt` on
    `.null` and `.address`. Only memory equations expose `referenceAt`; its equations in the
    generic list would slow every other step. -/
macro "cil_checked_memory_by_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       simp only [cil_step, cil_guard, CIL.Safety.instructionStep]
       try simp [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.checkedValue,
         CIL.Safety.numericValue, CIL.Safety.scalars,
         CIL.Safety.formValue, CIL.Safety.checkedAt, CIL.Safety.referenceAt_null,
         CIL.Safety.referenceAt_address, CIL.Safety.leaveFrame, Except.mapError, Bind.bind,
         Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

/-- Closes a checked `step` goal for an op with no `@[cil_step]` equation by unfolding
    `CIL.Safety.step` and `CIL.step` with `facts`, unfolding the return checks only if needed. -/
macro "cil_checked_step_by_unfolding " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       fail_if_success simp only [cil_step]
       -- Keep established arithmetic proofs compact. Unfolding checkedAt/formValue in the
       -- first pass can expand return checks enough to exceed the kernel recursion limit.
       first
       | (simp [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.step,
           CIL.Safety.checkedValue, CIL.Safety.numericValue,
           CIL.Safety.pureArity, CIL.Safety.scalars, CIL.Safety.leaveFrame, CIL.step,
           $[$facts:term],*] <;> (repeat constructor) <;> rfl)
       | (simp [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.step,
           CIL.Safety.checkedValue, CIL.Safety.numericValue,
           CIL.Safety.pureArity, CIL.Safety.scalars, CIL.Safety.leaveFrame, CIL.step,
           CIL.Safety.formValue, CIL.Safety.checkedAt, Except.mapError,
           $[$facts:term],*] <;> (repeat constructor) <;> rfl)))

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

/-- Closes a checked `step` goal by its equation, or by unfolding when the op has none. -/
macro "cil_checked_step_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| first
    | cil_checked_step_by_equations [$[$facts:term],*]
    | cil_checked_step_by_unfolding [$[$facts:term],*])

/-- Closes a `.memory` step through the generic `step_memory_eq` with `facts`, constructors
    and `rfl`. A fact stated at the `memoryInstruction` or `staticInstruction` level fails once
    a per-shape memory equation rewrites past it, so the stepping tactics retry such facts
    here. -/
macro "cil_checked_memory_retry " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       rw [CIL.Safety.step_memory_eq]
       try simp only [cil_guard]
       try simp [cil_guard, CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.checkedValue,
         CIL.Safety.numericValue, CIL.Safety.scalars,
         CIL.Safety.formValue, CIL.Safety.checkedAt, CIL.Safety.referenceAt_null,
         CIL.Safety.referenceAt_address, CIL.Safety.leaveFrame, Except.mapError, Bind.bind,
         Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

open Lean Elab Tactic Meta in
/-- Whether a supplied fact is, or is stated about, the definition `level`; a compound term is
    assumed to be. -/
def factsMention (facts : Array Term) (level : Name) : TacticM Bool := withMainContext do
  let mentions := fun (e : Expr) => (e.find? (·.isConstOf level)).isSome
  facts.anyM fun fact => do
    unless fact.raw.isIdent do return true
    if let some decl := (← getLCtx).findFromUserName? fact.raw.getId then
      return mentions (← instantiateMVars decl.type)
    let some name ← observing? <| realizeGlobalConstNoOverloadWithInfo fact.raw | return true
    return name == level || mentions (← getConstInfo name).type

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
    all_goals simp only [CIL.Safety.checkedIntrinsic, cil_guard, cil_eval,
      List.any_cons, List.any_nil, Bool.false_or, Bool.true_or, Bool.or_false,
      Bool.false_eq_true, ite_false, CIL.Safety.checkedValue, CIL.Safety.numericValue, ite_true,
      Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
    -- `rfl` would evaluate a residue definitionally and push a value no later fact matches.
    -- Operands arrive as `BitVec.ofNat n k`, which only a supplied fact stated with a numeral
    -- `k` needs respelled; facts are splice-last.
    all_goals (first
      | (cil_numeral_eval_fact [$[$facts:term],*]
         cil_intrinsic_pending
         simp only [bitVecOfNatLiteral, CIL.Safety.checkedIntrinsic, cil_guard, cil_eval,
           List.any_cons, List.any_nil, Bool.false_or, Bool.true_or, Bool.or_false,
           Bool.false_eq_true, ite_false, CIL.Safety.checkedValue, CIL.Safety.numericValue,
           ite_true, Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
         fail_if_success cil_intrinsic_pending
         first | rfl | cil_checked_step_equations [$[$facts:term],*])
      | rfl
      | cil_checked_step_equations [$[$facts:term],*])))

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
    by opcode (scalar, intrinsic, memory with its retry, or the generic equations). -/
syntax "cil_checked_step_normalized" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
/-- The supplied facts that state a `step` result for the goal's op, or for any op. -/
def stepFacts (target : Expr) (facts : Array Term) : TacticM (Array Term) := do
  -- A tactic `have` leaves the target under `mdata`, which `Expr.eq?` does not see through.
  let target := (← instantiateMVars target).consumeMData
  let some (_, lhs, _) := target.eq? | return #[]
  unless lhs.isAppOfArity ``CIL.Safety.step 7 do return #[]
  let head := (← whnfR lhs.getAppArgs[1]!).getAppFn.constName?
  let states (type : Expr) : MetaM Bool := forallTelescope type fun _ conclusion => do
    let some (_, factLhs, _) := conclusion.eq? | return false
    unless factLhs.isAppOfArity ``CIL.Safety.step 7 do return false
    match (← whnfR factLhs.getAppArgs[1]!).getAppFn.constName?, head with
    | some factHead, some goalHead => return factHead == goalHead
    | _, _ => return true
  facts.filterM (suppliedFactSatisfies · states)

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
elab_rules : tactic
  | `(tactic| cil_checked_step_normalized [$facts:term,*]) => withMainContext do
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
        -- `step_memory_eq` matches every `.memory` step, so the unfolding fallback, which runs
        -- only when no equation applies, cannot apply here.
        let some equationError ←
            attempt (← `(tactic| cil_checked_memory_by_equations [$facts:term,*])) | return
        -- A `staticInstruction` fact must be tried before `staticInstruction` is unfolded,
        -- which rewrites past it; a `memoryInstruction` fact is reached only by that unfolding.
        if ← factsMention facts.getElems ``CIL.Safety.staticInstruction then
          if (← attempt (← `(tactic| cil_checked_memory_retry [$facts:term,*]))).isNone then return
        if ← factsMention facts.getElems ``CIL.Safety.memoryInstruction then
          let retry ← `(tactic|
            cil_checked_memory_retry [CIL.Safety.staticInstruction, $facts:term,*])
          if (← attempt retry).isNone then return
        -- Report the per-shape goal, where facts belong, rather than the whole-instruction retry's.
        throw equationError
      else
        `(tactic| cil_checked_step_equations [$facts:term,*])
    evalTactic strategy

/-- One checked `step` goal: normalises `facts`, then runs `cil_checked_step_normalized`. -/
syntax "cil_checked_step" "[" term,* "]" : tactic

open Lean Elab Tactic in
/-- Normalise `CIL.truth` and `facts` once for a stepping loop, then build its tactic from the
    raw and normalised facts; per-step normalisation would re-simp every local fact on every
    instruction. -/
def cilWithNormalisedFacts (facts : Array Term)
    (body : Array Term → Array Term → TacticM Syntax) : TacticM Unit :=
  withMainContext do
    let prepared ←
      normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|)) (#[← `(CIL.truth)] ++ facts)
    withMainContext <| evalTactic (← body facts prepared)

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_step [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config facts.getElems
    withMainContext <| evalTactic (← `(tactic| cil_checked_step_normalized [$[$prepared:term],*]))

/-- `cil_checked_steps` with facts already normalised: enters an `invoke` goal through
    `invoke_of_run`, then takes checked `run` steps until the goal closes or a step fails,
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
      (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl))) ?_
    try simp only [CIL.Safety.leaveFrame, List.foldl_nil, List.nil_append, List.append_nil,
      CIL.NarrowKind.extend_ite_one_zero, CIL.NarrowKind.extend_ite_ofNat_one_zero,
      List.reverse_cons, List.reverse_nil, BitVec.reduceToNat, BitVec.reduceSignExtend,
      BitVec.reduceOfInt, BitVec.isValue,
      Nat.reduceMod, Bool.false_eq_true, ite_true, ite_false]
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

/-- Takes a fetched call through `run_call_of_invoke`, given the lookups, stepping both the
    callee and the caller's continuation to completion. -/
macro "cil_checked_call_at " methodFound:term:max instructionFound:term:max
    "[" facts:term,* "]" : tactic =>
  `(tactic| cil_strict refine CIL.Safety.run_call_of_invoke $methodFound $instructionFound
    (by cil_checked_step_normalized [$[$facts:term],*])
    (by cil_checked_steps_normalized [$[$facts:term],*]; done)
    (by cil_checked_steps_normalized [$[$facts:term],*]; done))

/-- `cil_checked_call_at`, except that only the callee runs to its return; the caller's
    continuation stays open as the goal. -/
macro "cil_checked_call_open_at " methodFound:term:max instructionFound:term:max
    "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_strict refine CIL.Safety.run_call_of_invoke $methodFound $instructionFound
      (by cil_checked_step_normalized [$[$facts:term],*])
      (by cil_checked_steps_normalized [$[$facts:term],*]; done) ?_
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
/-- One `run` step: prove the method and instruction lookups once, then apply only the
    composition lemma for the fetched opcode. With `openCall`, a call leaves the caller's
    continuation as the goal. -/
def cilRunStep (facts : Array Term) (openCall : Bool) : TacticM Unit := withMainContext do
  let (methodSyntax, instructionSyntax, operation) ←
    cilFetchedOp ``CIL.Safety.run_next (fun e => e.eq?.map (·.2.1)) 3 facts
  evalTactic (← if operation == ``CIL.Op.ret then
      `(tactic| cil_checked_return_at $methodSyntax $instructionSyntax [$facts,*])
    else if operation == ``CIL.Op.call then
      if openCall then
        `(tactic| cil_checked_call_open_at $methodSyntax $instructionSyntax [$facts,*])
      else `(tactic| cil_checked_call_at $methodSyntax $instructionSyntax [$facts,*])
    else
      `(tactic| cil_checked_next_at $methodSyntax $instructionSyntax [$facts,*]))

/-- One `run` step of the goal, chosen by the fetched opcode; at a call it also proves the
    caller's whole continuation. -/
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
    cil_steps_from "cil_checked_steps took no step: the method or instruction lookup, or the \
      first step, did not close; pass the lookup hypothesis, feature facts or step facts"
      cil_checked_run_step [$[$facts:term],*]))

/-- Proves an `invoke` or `run` goal by checked stepping with `facts`, normalised once at
    entry. Stops at the first step it cannot take, leaving that goal; fails if it takes none. -/
syntax "cil_checked_steps" "[" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_steps [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config facts.getElems
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

/-- `cil_checked_steps n` with no facts. -/
macro "cil_checked_steps " count:num : tactic => `(tactic| cil_checked_steps $count [])

end CIL.Safety
