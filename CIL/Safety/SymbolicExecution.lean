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
    | (cil_strict refine CIL.Safety.run_return
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by simp [cil_code, CIL.Safety.step, CIL.Safety.checkedValue,
          CIL.Safety.numericValue, CIL.Safety.pureArity, CIL.Safety.scalars,
          CIL.Safety.leaveFrame, CIL.step, $[$facts:term],*] <;> (repeat constructor) <;> rfl)
        (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl)))
    -- Elaborate each intermediate-state proof before creating the continuation
    -- goal, so reference/frame metavariables remain assignable by the step facts.
    | (cil_strict refine Eq.trans (CIL.Safety.run_next
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by simp [cil_code, CIL.Safety.step, CIL.Safety.checkedValue,
          CIL.Safety.numericValue, CIL.Safety.pureArity, CIL.Safety.scalars, CIL.step,
          $[$facts:term],*] <;> (repeat constructor) <;> rfl)) ?_)
    | (cil_strict apply CIL.Safety.run_call_of_invoke
       · simp only [cil_code, Nat.reduceAdd]; rfl
       · simp only [cil_code, Nat.reduceAdd]; rfl
       · simp [cil_code, CIL.Safety.step, CIL.Safety.checkedValue,
           CIL.Safety.numericValue, $[$facts:term],*] <;> (repeat constructor) <;> rfl
       · solve | cil_checked_steps [$[$facts:term],*]
       · solve | cil_checked_steps [$[$facts:term],*])
    ))

macro "cil_checked_steps" : tactic => `(tactic| cil_checked_steps [])

end CIL.Safety
