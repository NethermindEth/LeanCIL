import CIL.SymbolicExecution
import CIL.Safety.StepComposition
import CIL.Safety.ValueSteps
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
def normaliseStepFacts (config : TSyntax `Lean.Parser.Tactic.optConfig)
    (facts : Array Term) : TacticM (Array Term) := withMainContext do
    let isLocal (fact : Term) : TacticM Bool :=
      return fact.raw.isIdent && ((← getLCtx).findFromUserName? fact.raw.getId).isSome
    let locals ← facts.filterM isLocal
    let supplied ← facts.filterM fun fact => return !(← isLocal fact)
    let mut normalised : Array Term := #[]
    if !locals.isEmpty then
      let normaliser ← `(tactic| simp $config:optConfig [CIL.fin_val_three, CIL.fin_mk_ofNat,
        $[$supplied:term],*])
      let { ctx, simprocs, .. } ← mkSimpContext normaliser (eraseLocal := false)
      for fact in locals do
        let some decl := (← getLCtx).findFromUserName? fact.raw.getId | continue
        let type ← instantiateMVars decl.type
        unless ← isProp type do continue
        trace[CIL.factNormalize] "{decl.userName}"
        let mut instances := #[decl.toExpr]
        if let .forallE _ domain _ _ := ← whnf type then
          let domain ← whnf domain
          if domain.isAppOfArity ``Fin 1 then
            if let some size ← getNatValue? domain.appArg! then
              if size <= 64 then
                for index in [:size] do
                  let numeral : Term := ⟨Syntax.mkNumLit (toString index)⟩
                  let bound : Term := ⟨Syntax.mkNumLit (toString size)⟩
                  let value ← Term.elabTerm (← `(term| ($numeral : Fin $bound))) (some domain)
                  instances := instances.push (mkApp decl.toExpr value)
        for instanceProof in instances do
          let type ← inferType instanceProof
          let (result, _) ← simp type ctx simprocs
          if result.expr.consumeMData.isConstOf ``True then continue
          if result.expr == type && instanceProof == decl.toExpr then continue
          let proof ← match result.proof? with
            | some eq => mkEqMP eq instanceProof
            | none => mkExpectedTypeHint instanceProof result.expr
          let name ← mkFreshUserName decl.userName
          let (_, goal) ← (← (← getMainGoal).assert name result.expr proof).intro1P
          replaceMainGoal [goal]
          normalised := normalised.push (mkIdent name)
    return facts ++ normalised

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_fact_simp $config:optConfig [$lemmas:term,*] [$facts:term,*]) => do
    let prepared ← normaliseStepFacts config facts.getElems
    let all := lemmas.getElems ++ #[← `(term| CIL.fin_val_three), ← `(term| CIL.fin_mk_ofNat)] ++ prepared
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
    | (simp only [cil_code, Nat.reduceAdd]; rfl)
    | rfl
    | with_reducible assumption
    | (simp only [cil_code, Nat.reduceAdd, $[$facts:term],*]; done)
    | (simp only [cil_code, Nat.reduceAdd, $[$facts:term],*]; rfl))

/-- Close definitional steps before using instruction equations or the dispatcher. -/
macro "cil_checked_step_normalized " "[" facts:term,* "]" : tactic => do
  -- With facts, reflexivity can assign a symbolic branch target before its
  -- condition is rewritten, leaving the next instruction lookup stuck.
  let reflexivity ← if facts.getElems.isEmpty then `(tactic| rfl) else `(tactic| fail)
  `(tactic| (
    try simp only [cil_code, Nat.reduceAdd]
    first
    | $reflexivity:tactic
    -- An equation is an exact rewrite of `step`, so only an op without one falls back to unfolding the dispatcher.
    | (simp only [cil_step, CIL.Safety.instructionStep]
       try simp [CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.checkedValue, CIL.Safety.numericValue, CIL.Safety.scalars,
         CIL.Safety.formValue, CIL.Safety.checkedAt, CIL.Safety.leaveFrame, Except.mapError, Bind.bind, Except.bind,
         Pure.pure, Except.pure, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl))
    | (fail_if_success simp only [cil_step]
       simp [CIL.fin_val_three, CIL.fin_mk_ofNat, CIL.Safety.step, CIL.Safety.checkedValue, CIL.Safety.numericValue,
        CIL.Safety.pureArity, CIL.Safety.scalars, CIL.Safety.leaveFrame, CIL.step,
        $[$facts:term],*] <;> (repeat constructor) <;> rfl)))

syntax "cil_checked_step" "[" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_step [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config facts.getElems
    withMainContext <| evalTactic (← `(tactic| cil_checked_step_normalized [$[$prepared:term],*]))

/-- Execute checked instructions using extracted lookups and proved semantic facts.
    Unresolved memory and arithmetic conditions remain proof obligations. -/
syntax "cil_checked_steps_normalized" "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_checked_steps_normalized [$facts:term,*]) =>
  `(tactic| (
    try (conv => lhs; arg 2; cil_reduce_fuel)
    try (cil_strict apply CIL.Safety.invoke_of_run
         · cil_lookup [$[$facts:term],*]
         · first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl)
         · first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl))
    cil_steps_from "cil_checked_steps took no step: the method or instruction lookup, or the first step, did not close; pass the lookup hypothesis, feature facts or step facts" first
    | (cil_strict refine CIL.Safety.run_return (op := .ret _)
        (by cil_lookup [$[$facts:term],*])
        (by cil_lookup [$[$facts:term],*])
        (by cil_checked_step_normalized [$[$facts:term],*])
        (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl)))
    -- Elaborate each intermediate-state proof before creating the continuation
    -- goal, so reference/frame metavariables remain assignable by the step facts.
    | (cil_strict refine Eq.trans (CIL.Safety.run_next
        (by cil_lookup [$[$facts:term],*])
        (by cil_lookup [$[$facts:term],*])
        (by cil_checked_step_normalized [$[$facts:term],*])) ?_)
    | (cil_strict apply CIL.Safety.run_call_of_invoke
       · cil_lookup [$[$facts:term],*]
       · cil_lookup [$[$facts:term],*]
       · cil_checked_step_normalized [$[$facts:term],*]
       · solve | cil_checked_steps_normalized [$[$facts:term],*]
       · solve | cil_checked_steps_normalized [$[$facts:term],*])
    ))

syntax "cil_checked_steps" "[" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_steps [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config facts.getElems
    withMainContext <| evalTactic (← `(tactic| cil_checked_steps_normalized [$[$prepared:term],*]))

macro "cil_checked_steps" : tactic => `(tactic| cil_checked_steps [])

end CIL.Safety
