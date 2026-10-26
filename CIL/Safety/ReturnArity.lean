import CIL.Safety.Certificate

/-!
# Return arity and fully specified results

A successful return yields exactly as many values as the method declares (one or none), and
neither returned values nor ordinary call arguments contain unspecified SIMD lanes. The two
return properties share one dispatcher proof, then lift to runs and invocations through the
return trace.
-/

namespace CIL.Safety

private theorem bind_success {source : Except ε α} {continuation : α → Except ε β}
    {value : β} :
    (source.bind continuation = .ok value) ↔
      ∃ input, source = .ok input ∧ continuation input = .ok value := by
  cases source <;> simp [Except.bind]

set_option maxHeartbeats 400000 in
/-- A successful return has its declared arity and exposes no unspecified SIMD lanes. -/
theorem step_return_properties (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory)
    (values : List Value)
    (executed : step body operation pc args frame stack memory = .ok (.returned values final)) :
    values.length = (if body.returnsValue then 1 else 0) ∧
      values.any Value.hasUnspecified = false := by
  unfold step at executed
  dsimp only at executed
  repeat' first
    | solve |
        simp only [Bind.bind, Pure.pure, Except.pure, bind_success, Except.ok.injEq,
          reduceCtorEq, and_false, exists_false] at executed
    | split at executed
    | solve |
      have same : values = stack := (checkedValues_valid _ _ _ (by assumption)).1
      rw [same]
      simp_all [observerCount, unspecifiedOperands, List.take_of_length_le,
        Value.hasUnspecified, CIL.Value.hasUnspecified]
    | solve | simp_all [Value.hasUnspecified, CIL.Value.hasUnspecified]
    | cases executed
    | obtain ⟨_, _, executed⟩ := bind_success.mp executed
    | simp only [Bind.bind, Pure.pure, Except.pure] at executed

#print axioms step_return_properties

/-- A checked return has the arity declared by its actual method body. -/
theorem step_return_length (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory)
    (values : List Value)
    (executed : step body operation pc args frame stack memory = .ok (.returned values final)) :
    values.length = if body.returnsValue then 1 else 0 :=
  (step_return_properties body operation pc args frame stack memory final values executed).1

/-- A successful run of `method` returns the arity its body declares. -/
theorem run_return_length (program : CIL.Program) (fuel method pc : Nat) (body : CIL.Method)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory)
    (values : List Value)
    (lookup : program[method]? = some body)
    (executed : run program fuel method pc args frame stack memory = .ok (final, values)) :
    values.length = if body.returnsValue then 1 else 0 := by
  obtain ⟨lastPc, lastFrame, lastStack, before, returned, raw, _, fetched, _, checked⟩ :=
    run_success_return_trace program fuel method pc args frame stack memory final values executed
  obtain ⟨actualBody, operation, found, _, stepped⟩ := fetched
  rw [lookup] at found
  cases found
  rw [(checkedValues_valid _ _ _ checked).1]
  exact step_return_length body operation lastPc args lastFrame lastStack before returned raw
    stepped

#print axioms step_return_length
#print axioms run_return_length

/-- Successful returns never expose unspecified SIMD lanes. -/
theorem step_return_known (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory)
    (values : List Value)
    (executed : step body operation pc args frame stack memory = .ok (.returned values final)) :
    values.any Value.hasUnspecified = false :=
  (step_return_properties body operation pc args frame stack memory final values executed).2

#print axioms step_return_known

/-- A successful invocation never returns unspecified SIMD lanes. -/
theorem invoke_return_known {program : CIL.Program} {fuel method : Nat}
    {args values : List Value} {memory final : Memory}
    (executed : invoke program fuel method args memory = .ok (final, values)) :
    values.any Value.hasUnspecified = false := by
  obtain ⟨_, arguments, frame, entered, _, _, _, ran⟩ := invoke_success_setup executed
  obtain ⟨pc, lastFrame, stack, before, returned, raw, _, fetched, _, checked⟩ :=
    run_success_return_trace program fuel method 0 arguments frame [] entered final values ran
  obtain ⟨body, operation, _, _, stepped⟩ := fetched
  rw [(checkedValues_valid _ _ _ checked).1]
  exact step_return_known body operation pc arguments lastFrame stack before returned raw stepped

#print axioms invoke_return_known

/-- A successful ordinary call exposes only fully specified arguments. -/
theorem step_call_known {body : CIL.Method} {callee argc pc : Nat}
    {args stack arguments rest : List Value} {frame : Frame} {memory final : Memory}
    (executed : step body (.call callee argc) pc args frame stack memory =
      .ok (.call callee arguments rest final)) :
    arguments.any Value.hasUnspecified = false := by
  simp only [step, observerCount, Bool.or_false] at executed
  split at executed
  · cases executed
  · rename_i known
    split at executed
    · cases executed
    · cases checked : (stack.take argc).reverse.mapM (checkedValue memory) with
      | error fault => simp [checked, Bind.bind, Except.bind] at executed
      | ok checkedArgs =>
        simp only [checked, Bind.bind, Except.bind, Pure.pure, Except.pure,
          Except.ok.injEq, FrameAction.call.injEq] at executed
        obtain ⟨_, rfl, rfl, rfl⟩ := executed
        rw [(checkedValues_valid _ _ _ checked).1]
        simpa [unspecifiedOperands] using known

#print axioms step_call_known
end CIL.Safety
