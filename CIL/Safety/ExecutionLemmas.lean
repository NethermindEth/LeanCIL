import CIL.Safety.Execution

/-!
# Successful runs start with a successful step

A single inversion lemma on the checked interpreter: a run that succeeds with fuel left
fetched an instruction and stepped it without a fault.
-/

namespace CIL.Safety

/-- A successful run fetched a method body and an instruction at `pc`, and that instruction
    stepped without a fault, when no exception clause of the method protects `pc`. -/
theorem run_success_step (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (result : List Value)
    (unprotected : (program[method]?).all (·.unprotectedAt pc) = true)
    (success : run program (fuel + 1) method pc args frame stack m = .ok (final, result)) :
    ∃ body op action, program[method]? = some body ∧ body.code[pc]? = some op ∧
      step body op pc args frame stack m = .ok action := by
  rw [run_succ _ _ _ _ _ _ _ _ unprotected] at success
  cases hb : program[method]? with
  | none => simp [hb] at success
  | some body =>
    cases ho : body.code[pc]? with
    | none => simp [hb, ho] at success
    | some op =>
      cases hs : step body op pc args frame stack m with
      | error fault =>
        simp [hb, ho, hs, Bind.bind, Except.bind, Except.mapError] at success
      | ok action => exact ⟨body, op, action, rfl, ho, hs⟩
#print axioms run_success_step

end CIL.Safety
