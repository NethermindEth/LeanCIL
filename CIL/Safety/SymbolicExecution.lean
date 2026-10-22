import CIL.SymbolicExecution
import CIL.Safety.StepComposition
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
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_fact_simp $config:optConfig [$lemmas:term,*] [$facts:term,*]) => withMainContext do
    let isLocal (fact : Term) : TacticM Bool :=
      return fact.raw.isIdent && ((← getLCtx).findFromUserName? fact.raw.getId).isSome
    let locals ← facts.getElems.filterM isLocal
    let supplied ← facts.getElems.filterM fun fact => return !(← isLocal fact)
    let mut normalised : Array Term := #[]
    if !locals.isEmpty then
      let normaliser ← `(tactic| simp $config:optConfig [$[$supplied:term],*])
      let { ctx, simprocs, .. } ← mkSimpContext normaliser (eraseLocal := false)
      for fact in locals do
        let some decl := (← getLCtx).findFromUserName? fact.raw.getId | continue
        let type ← instantiateMVars decl.type
        unless ← isProp type do continue
        let (result, _) ← simp type ctx simprocs
        if result.expr.consumeMData.isConstOf ``True || result.expr == type then continue
        let proof ← match result.proof? with
          | some eq => mkEqMP eq decl.toExpr
          | none => mkExpectedTypeHint decl.toExpr result.expr
        let name ← mkFreshUserName decl.userName
        let (_, goal) ← (← (← getMainGoal).assert name result.expr proof).intro1P
        replaceMainGoal [goal]
        normalised := normalised.push (mkIdent name)
    let all := lemmas.getElems ++ facts.getElems ++ normalised
    withMainContext <| evalTactic (← `(tactic| simp $config:optConfig [$[$all:term],*]))

/-- Close definitional steps before using instruction equations or the dispatcher. -/
macro "cil_checked_step " "[" facts:term,* "]" : tactic => do
  -- With facts, reflexivity can assign a symbolic branch target before its
  -- condition is rewritten, leaving the next instruction lookup stuck.
  let reflexivity ← if facts.getElems.isEmpty then `(tactic| rfl) else `(tactic| fail)
  `(tactic| (
    try simp only [cil_code, Nat.reduceAdd]
    first
    | $reflexivity:tactic
    | (
      first
      | rw [CIL.Safety.step_argument_eq]
      | rw [CIL.Safety.step_return_eq]
      | rw [CIL.Safety.step_brzero_i32_eq]
      | rw [CIL.Safety.step_brzero_i64_eq]
      | rw [CIL.Safety.step_brnonzero_i32_eq]
      | rw [CIL.Safety.step_brnonzero_i64_eq]
      | skip
      all_goals cil_fact_simp [CIL.Safety.step, CIL.Safety.checkedValue, CIL.Safety.numericValue,
        CIL.Safety.pureArity, CIL.Safety.scalars, CIL.Safety.leaveFrame, CIL.step]
        [$[$facts:term],*] <;> (repeat constructor) <;> rfl)))

/-- Execute checked instructions using extracted lookups and proved semantic facts.
    Unresolved memory and arithmetic conditions remain proof obligations. -/
syntax "cil_checked_steps" "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_checked_steps [$facts:term,*]) =>
  `(tactic| (
    try (conv => lhs; arg 2; cil_reduce_fuel)
    try (cil_strict apply CIL.Safety.invoke_of_run
         · simp only [cil_code, Nat.reduceAdd]; rfl
         · first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl)
         · first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl))
    repeat first
    | (cil_strict refine Eq.trans (CIL.Safety.run_return (op := .ret _)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by cil_checked_step [$[$facts:term],*])
        (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl))) ?_
       try (dsimp only [CIL.Safety.leaveFrame, List.foldl]; with_reducible rfl))
    -- Elaborate each intermediate-state proof before creating the continuation
    -- goal, so reference/frame metavariables remain assignable by the step facts.
    | (cil_strict refine Eq.trans (CIL.Safety.run_next
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by cil_checked_step [$[$facts:term],*])) ?_)
    | (cil_strict apply CIL.Safety.run_call_of_invoke
       · simp only [cil_code, Nat.reduceAdd]; rfl
       · simp only [cil_code, Nat.reduceAdd]; rfl
       · cil_checked_step [$[$facts:term],*]
       · solve | cil_checked_steps [$[$facts:term],*]
       · solve | cil_checked_steps [$[$facts:term],*])
    ))

macro "cil_checked_steps" : tactic => `(tactic| cil_checked_steps [])

end CIL.Safety
