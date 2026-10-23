import CIL.Safety.Certificate

namespace CIL.Safety

private theorem bind_success {source : Except ε α} {continuation : α → Except ε β} {value : β} :
    (source.bind continuation = .ok value) ↔
      ∃ input, source = .ok input ∧ continuation input = .ok value := by
  cases source <;> simp [Except.bind]

/-- A checked return has the arity declared by its actual method body. -/
theorem step_return_length (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory) (values : List Value)
    (executed : step body operation pc args frame stack memory = .ok (.returned values final)) :
    values.length = if body.returnsValue then 1 else 0 := by
  unfold step at executed
  dsimp only at executed
  repeat' first
    | split at executed
    | solve |
      have same : values = stack := (checkedValues_valid _ _ _ (by assumption)).1
      rw [same]
      simp_all
    | solve | simp_all
    | cases executed
    | obtain ⟨_, _, executed⟩ := bind_success.mp executed
    | simp only [Bind.bind, Pure.pure, Except.pure] at executed

theorem run_return_length (program : CIL.Program) (fuel method pc : Nat) (body : CIL.Method)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory) (values : List Value)
    (lookup : program[method]? = some body)
    (executed : run program fuel method pc args frame stack memory = .ok (final, values)) :
    values.length = if body.returnsValue then 1 else 0 := by
  obtain ⟨lastPc, lastFrame, lastStack, before, returned, raw, _, fetched, _, checked⟩ :=
    run_success_return_trace program fuel method pc args frame stack memory final values executed
  obtain ⟨actualBody, operation, found, _, stepped⟩ := fetched
  rw [lookup] at found
  cases found
  rw [(checkedValues_valid _ _ _ checked).1]
  exact step_return_length body operation lastPc args lastFrame lastStack before returned raw stepped

#print axioms step_return_length
#print axioms run_return_length
end CIL.Safety
