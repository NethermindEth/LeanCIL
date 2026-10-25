import Lean
import CIL.ExecutionLemmas

/-!
# Symbolic execution of the reference interpreter

`cil_steps` runs `CIL.run` on an extracted method by rewriting, one instruction at a time,
until the method returns or a symbolic fact is needed. `if_extracted` admits optional
summary proofs that fall back to raw stepping when they fail. Everything here is a tactic
or a simp set; the kernel still checks every resulting proof.
-/

/-- Definitions and facts emitted from the current extracted assembly, and nothing else.
    Registering a definition supplies its kernel-checked unfolding equations; it does not
    assign a behavioural contract to the method. -/
register_simp_attr cil_code
/-- Evaluation lemmas that the checked stepping tactics in `CIL.Safety.SymbolicExecution`
    rewrite with. -/
register_simp_attr cil_eval

namespace CIL

-- Complete Std's numeral projection rules (which cover zero, one and two).
theorem fin_val_three (n : Nat) : (3 : Fin (n + 4)).val = 3 := rfl

theorem fin_mk_ofNat {n k : Nat} [NeZero n] (bound : k < n) :
    (⟨k, bound⟩ : Fin n) = Fin.ofNat n k := by
  apply Fin.ext
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt bound]

/-- A candidate fuel budget for the selected method and later callees: one more than their
    supported instruction count. Each execution proof establishes that it suffices. -/
def executionBound (program : Program) (method : Nat) : Nat :=
  (program.drop method).foldl (fun total body => total +
    (body.code.filter fun op => match op with | .unsupported _ => false | _ => true).length) 0 + 1

open Lean Elab Command in
/-- `if_extracted name { commands }` elaborates a summary candidate when `name` exists. It is
    a transaction: failed elaboration, kernel checking or an admitted proof leaves neither
    declarations nor simp registrations behind, and execution then uses instructions directly. -/
elab "if_extracted " name:ident " {" commands:command* "}" : command => do
  unless (← getEnv).contains name.getId do return
  let saved ← get
  try
    for command in commands do
      elabCommand (← `(command| set_option Elab.async false in $command))
      if (← get).messages.hasErrors then
        throwError "Summary proof failed"
    let env ← getEnv
    for (declName, info) in env.constants.toList do
      if saved.env.contains declName then continue
      if info.isAxiom || (info.value? true).any Expr.hasSorry then
        throwError "Summary contains an admitted declaration"
      if (env.checked.get.find? declName).isNone then
        throwError "Summary declaration was not kernel checked"
  catch exception =>
    let failed ← get
    let message := failed.messages.toList.find? fun message => message.severity == .error
    let detail ← (message.map (·.data) |>.getD exception.toMessageData).toString
    let resource := ["maximum number of heartbeats", "maximum recursion depth",
      "maximum number of steps exceeded", "deep recursion", "stack overflow"].any
        fun marker => (detail.splitOn marker).length > 1
    let failureClass := if resource then "resource limit" else "proof obligation"
    set saved
    logInfo m!"Optional summary candidate {name.getId} was not proved; \
      using raw execution ({failureClass}):\n{detail}"

/-- Execute instructions until execution finishes or a symbolic obligation prevents further
    reduction. Facts are ordinary proved hypotheses or lemmas. There is no instruction trace,
    method identity or local layout in this procedure; Lean's heartbeat and depth limits
    remain explicit failure limits. -/
macro "cil_steps" facts:term,+ : tactic =>
  `(tactic| ((try (simp only [cil_code])); repeat
    (rw [run];
     -- Resolve the method and instruction before unfolding the selected step.
     -- Otherwise simp explores instruction cases under unresolved bind lambdas.
     simp only [List.getElem_eq_getElem?_get, cil_code, Option.get_some,
       Option.pure_def, Option.bind_eq_bind, Option.bind_some];
     -- Retain checked rewrite proofs instead of making the kernel repeat large
     -- definitional reductions when checking the resulting execution proof.
     simp (config := { implicitDefEqProofs := false })
      [cil_code, step, binary, truth, write64, initLocals, initFrame, Value.initialized,
      cil_feature, Intrinsic.available,
      fin_val_three, $[$facts:term],*])))

/-- `cil_steps` with no extra facts. -/
macro "cil_steps" : tactic => `(tactic| cil_steps Nat.add_zero)

end CIL
