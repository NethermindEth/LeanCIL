import CIL.Safety.Certificate

/-!
# Return arity and fully specified results

A successful return yields exactly as many values as the method declares (one or none), and
neither returned values nor ordinary call arguments contain unspecified SIMD lanes. The two
return properties share one dispatcher proof. Run traces preserve arity across tail calls;
terminal-return witnesses carry the absence of unspecified lanes through invocation.
-/

namespace CIL.Safety

private theorem bind_success {source : Except ε α} {continuation : α → Except ε β}
    {value : β} :
    (source.bind continuation = .ok value) ↔
      ∃ input, source = .ok input ∧ continuation input = .ok value := by
  cases source <;> simp [Except.bind]

/-- Managed dispatch produces a next step or child invocation, never a method return. -/
private theorem calliStep_not_returned (signature : CIL.ManagedSignature) (tail : Bool) (link : Option CIL.Link)
    (frame : Frame) (stack : List Value) (memory final : Memory) (values : List Value) :
    calliStep signature tail link frame stack memory ≠ .ok (.returned values final) := by
  intro executed
  unfold calliStep at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first | cases executed | split at executed
#print axioms calliStep_not_returned

set_option maxHeartbeats 400000 in
/-- A successful return has its declared arity and exposes no unspecified SIMD lanes. -/
theorem step_return_properties (body : CIL.Method) (operation : CIL.Instruction) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory)
    (values : List Value)
    (executed : step body operation pc args frame stack memory = .ok (.returned values final)) :
    values.length = (if body.returnsValue then 1 else 0) ∧
      values.any Value.hasUnspecified = false := by
  unfold step observedCall referenceCompareCall referenceSubtractCall newobjStep
    constructAggregate constructObject at executed
  dsimp only at executed
  generalize narrowing : body.returnNarrow = narrow at executed
  repeat' first
    | unfold returnFrom at executed
    | unfold localAllocation at executed
    | solve | exact False.elim (calliStep_not_returned _ _ _ _ _ _ _ _ executed)
    | solve | (obtain ⟨_, ⟨_, same⟩ | ⟨_, _, same⟩⟩ := leaveStep_resumes executed <;> cases same)
    | solve |
        (obtain ⟨_, ⟨_, same⟩ | ⟨_, _, same⟩⟩ := endFinallyStep_resumes executed <;> cases same)
    | solve | (obtain ⟨_, _, _, returned, _⟩ := modelStep_frame executed; cases returned)
    | solve |
        simp only [Bind.bind, Pure.pure, Except.pure, bind_success, Except.ok.injEq,
          reduceCtorEq, and_false, exists_false] at executed
    | split at executed
    | solve |
      have same : values = stack := (checkedValues_valid _ _ _ (by assumption)).1
      rw [same]
      simp_all [observerCount, unspecifiedOperands, List.take_of_length_le,
        Value.hasUnspecified, CIL.Value.hasUnspecified]
    | solve |
        simp_all only [reduceCtorEq, implies_true, Bool.not_eq_true,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.length_cons,
          List.length_nil, Nat.zero_add, ↓reduceIte, List.any_cons, Value.hasUnspecified,
          CIL.Value.hasUnspecified, List.any_nil, Bool.or_self, and_self]
    | cases executed
    | unfold initializeSpanHome at executed
    | obtain ⟨_, _, executed⟩ := bind_success.mp executed
    | simp only [Bind.bind, Pure.pure, Except.pure] at executed

#print axioms step_return_properties

/-- A checked return has the arity declared by its actual method body. -/
theorem step_return_length (body : CIL.Method) (operation : CIL.Instruction) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory)
    (values : List Value)
    (executed : step body operation pc args frame stack memory = .ok (.returned values final)) :
    values.length = if body.returnsValue then 1 else 0 :=
  (step_return_properties body operation pc args frame stack memory final values executed).1

/-- A successful run of `method`, through caught faults and tail calls, returns the arity its
    body declares. -/
theorem run_return_length (program : CIL.Program) (fuel method pc : Nat) (body : CIL.Method)
    (args : List Value) (frame : Frame) (stack : List Value) (memory final : Memory)
    (values : List Value)
    (lookup : program[method]? = some body)
    (executed : run program fuel method pc args frame stack memory = .ok (final, values)) :
    values.length = if body.returnsValue then 1 else 0 := by
  have trace := run_ok_trace executed
  clear executed
  generalize ended : (Except.ok (final, values) : Except FaultState _) = outcome at trace
  induction trace generalizing body with
  | returned found _ stepped checked =>
    cases ended
    rw [lookup] at found
    cases found
    rw [(checkedValues_valid _ _ _ checked).1]
    exact step_return_length _ _ _ _ _ _ _ _ _ stepped
  | caught _ _ _ _ _ ih | next _ _ _ _ ih | raiseCaught _ _ _ _ _ ih
  | called _ _ _ _ _ _ _ _ ih | constructed _ _ _ _ _ _ _ _ _ ih
  | callCaught _ _ _ _ _ _ _ _ _ ih | constructCaught _ _ _ _ _ _ _ _ _ ih =>
    exact ih _ lookup ended
  | tailed found _ _ childLookup returns _ _ _ ih =>
    have same := Option.some.inj (lookup.symm.trans found)
    subst same
    have result := ih _ childLookup ended
    simpa only [bne_eq_false_iff_eq.mp returns] using result
  | exhausted | missing | faulted | raised | callMissing | callUnentered | tailMissing
  | tailMismatched | constructMissing | constructUnentered | tailUnchecked | tailUnentered
  | returnUnchecked | callFaulted | constructFaulted | constructValued | constructUnloaded =>
    cases ended

#print axioms step_return_length
#print axioms run_return_length

/-- Successful returns never expose unspecified SIMD lanes. -/
theorem step_return_known (body : CIL.Method) (operation : CIL.Instruction) (pc : Nat)
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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, stepped, _, checked⟩ :=
    (run_ok_trace ran).returnedBy rfl
  rw [(checkedValues_valid _ _ _ checked).1]
  exact step_return_known _ _ _ _ _ _ _ _ _ stepped

#print axioms invoke_return_known

/-- A successful ordinary call exposes only fully specified arguments. -/
theorem step_call_known {body : CIL.Method} {method : Extraction.MethodRef}
    {prefixes : CallPrefixes} {callee pc : Nat}
    {args stack arguments rest : List Value} {frame : Frame} {memory final : Memory}
    (executed : step body (.call method prefixes) pc args frame stack memory =
      .ok (.call callee arguments rest final)) :
    arguments.any Value.hasUnspecified = false := by
  simp only [step] at executed
  split at executed
  · cases executed
  split at executed
  · split at executed
    · cases executed
    · obtain ⟨_, _, _, called, _⟩ := modelStep_frame executed
      cases called
  rename_i link _
  unfold observedCall at executed
  split at executed
  · cases executed
  rename_i known
  cases link <;> try (first | (cases executed; done) | (simp at executed; done))
  dsimp only at executed
  split at executed
  · split at executed
    · cases executed
    · cases checked : stack.reverse.mapM (callArgument frame memory) <;>
        simp [checked, Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  split at executed
  · cases executed
  · cases checked :
        (stack.take method.argumentCount).reverse.mapM (callArgument frame memory) with
    | error fault => simp [checked, Bind.bind, Except.bind] at executed
    | ok checkedArgs =>
      simp only [checked, Bind.bind, Except.bind, Pure.pure, Except.pure,
        Except.ok.injEq, FrameAction.call.injEq] at executed
      obtain ⟨_, rfl, rfl, rfl⟩ := executed
      rw [callArguments_hasUnspecified checked]
      simpa [unspecifiedOperands] using known

#print axioms step_call_known
end CIL.Safety
