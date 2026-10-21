import CIL.SymbolicExecution
import CIL.Safety.StepComposition
import CIL.Safety.CallComposition

namespace CIL.Safety

open Lean Elab Tactic Conv in
elab "cil_reduce_fuel" : conv => do
  changeLhs (← Meta.reduce (← getLhs))

-- Failed candidate proofs must backtrack, rather than be recovered as admitted
-- terms. Intermediate call results are inferred by the checked child execution.
open Lean Elab Tactic in
elab "cil_strict " tactic:tactic : tactic =>
  Meta.withAssignableSyntheticOpaque <| Term.withoutErrToSorry <| withoutRecover do
    evalTactic tactic
    if ← MonadLog.hasErrors then throwError "Checked step candidate failed"

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
      all_goals simp [CIL.Safety.step, CIL.Safety.checkedValue, CIL.Safety.numericValue,
        CIL.Safety.pureArity, CIL.Safety.scalars, CIL.Safety.leaveFrame, CIL.step,
        $[$facts:term],*] <;> (repeat constructor) <;> rfl)))

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
    | (cil_strict refine CIL.Safety.run_return (op := .ret _)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by cil_checked_step [$[$facts:term],*])
        (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl)))
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
