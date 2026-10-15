import CIL.SymbolicExecution
import CIL.Safety.StepComposition

namespace CIL.Safety

open Lean Elab Tactic Conv in
elab "cil_reduce_fuel" : conv => do
  changeLhs (← Meta.reduce (← getLhs))

/-- Execute checked instructions using extracted lookups and proved semantic facts.
    Unresolved memory and arithmetic conditions remain proof obligations. -/
macro "cil_checked_steps" facts:term,+ : tactic =>
  `(tactic| (
    try (conv => lhs; arg 2; cil_reduce_fuel)
    try (apply CIL.Safety.invoke_of_run
         · simp only [cil_code]; rfl
         · rfl
         · rfl)
    repeat first
    | (apply CIL.Safety.run_return
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [cil_code, CIL.Safety.step, CIL.Safety.checkedValue,
           CIL.Safety.numericValue, CIL.Safety.pureArity, CIL.Safety.scalars, CIL.step, $[$facts:term],*] <;> rfl
       · rfl)
    -- Apply composition before solving its premises so the goal fixes the current
    -- state. Elaborating a rewrite lemma first leaves those inputs unconstrained.
    | (apply Eq.trans; apply CIL.Safety.run_next
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [cil_code, CIL.Safety.step, CIL.Safety.checkedValue,
           CIL.Safety.numericValue, CIL.Safety.pureArity, CIL.Safety.scalars, CIL.step, $[$facts:term],*] <;> rfl)
    ))

macro "cil_checked_steps" : tactic => `(tactic| cil_checked_steps Nat.add_zero)

end CIL.Safety
