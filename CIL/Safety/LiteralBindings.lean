import CIL.Safety.StaticBindingBounds

/-!
# String literal bindings are fixed for a whole run

No checked step, frame entry, frame exit or nested call rebinds `Memory.literals`. An `ldstr`
after a call therefore loads the object bound by the caller (`invoke_literals`).
-/

namespace CIL.Safety

/-- Allocation adds storage without rebinding a literal. -/
theorem allocate_literals {source target : Memory} {descriptor : Allocation}
    {identity : AllocationId} (allocated : allocate source descriptor = .ok (identity, target)) :
    target.literals = source.literals := by
  unfold allocate at allocated
  repeat' first | cases allocated | split at allocated
  rfl
#print axioms allocate_literals

/-- Ordinary memory effects never rebind a literal. -/
theorem InstructionEffect.literals {source target : Memory}
    (effect : InstructionEffect source target) : target.literals = source.literals := by
  cases effect with
  | unchanged => rfl
  | write success => exact write_literals success
  | snapshot success => exact writeSnapshot_literals success
  | slot success =>
    obtain ⟨-, -, rfl⟩ := storeSlot_ok success
    rfl
  | arraySlot success =>
    obtain ⟨-, -, -, rfl⟩ := storeArraySlot_ok success
    rfl
#print axioms InstructionEffect.literals

/-- Resolving a static reference may allocate and bind a static, never a literal. -/
theorem staticReference_literals {source target : Memory} {descriptor : CIL.StaticDescriptor}
    {reference : Reference}
    (success : staticReference descriptor source = .ok (target, reference)) :
    target.literals = source.literals := by
  cases cached : source.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨name, address⟩ := binding
    obtain ⟨rfl, _, _⟩ := cached_static_reference_checked _ _ _ _ _ _ cached success
    rfl
  | none =>
    simp only [staticReference, cached] at success
    split at success
    · cases success
    cases allocated : allocate source
        ⟨.immutableStatic,
          ⟨descriptor.bytes.length, descriptor.alignment, []⟩, true, [descriptor.bytes.length]⟩ <;>
      simp only [allocated, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at success
    · cases success
    · rename_i pair
      obtain ⟨identity, memory⟩ := pair
      cases success
      have literals := allocate_literals allocated
      exact literals
#print axioms staticReference_literals

/-- Every checked dispatcher effect leaves the literal bindings as they were. -/
theorem StepEffect.literals {body : CIL.Method} {operation : CIL.Instruction}
    {source target : Memory}
    {frame final : Frame} (effect : StepEffect body operation frame source final target) :
    target.literals = source.literals := by
  cases effect with
  | arrayAllocation effect =>
    cases effect with
    | fresh _ _ allocation =>
      have literals := allocate_literals allocation
      exact literals
  | objectAllocation effect _ =>
    cases effect with
    | fresh _ allocation =>
      have literals := allocate_literals allocation
      exact literals
  | stackAllocation effect =>
    cases effect with
    | empty => rfl
    | fresh allocated initialized =>
      have retained := (allocateHome_setup _ _ _ _ _ .word32 allocated).literals
      rcases initialized with rfl | written
      · exact retained
      · exact (write_literals written).trans retained
  | memory effect =>
    cases effect with
    | ordinary effect => exact effect.literals
    | reference _ success => exact staticReference_literals success
  | store _ stored => exact storeLocal_literals stored
  | valueHome allocated stored =>
    exact ((storeValue_effect _ _ _ _ stored).literals).trans
      (allocateHome_setup _ _ _ _ _ .word32 allocated).literals
  | localHome allocated stored =>
    exact (storeLocal_literals stored).trans
      (allocateHome_setup _ _ _ _ _ .word32 allocated).literals
#print axioms StepEffect.literals

/-- Expiring a frame changes liveness, never the literal bindings. -/
theorem leaveFrame_literals (frame : Frame) (memory : Memory) :
    (leaveFrame frame memory).literals = memory.literals := by
  unfold leaveFrame
  generalize frame.owned = owned
  induction owned generalizing memory with
  | nil => rfl
  | cons identity owned induction => exact induction (expire memory identity)
#print axioms leaveFrame_literals

/-- Every successful run, including nested calls, ends with the literal bindings it began with. -/
theorem run_literals {program : CIL.Program} {fuel method pc : Nat}
    {arguments stack values : List Value} {frame : Frame} {source target : Memory}
    (success : run program fuel method pc arguments frame stack source = .ok (target, values)) :
    target.literals = source.literals := by
  have trace := run_success_trace _ _ _ _ _ _ _ _ _ _ success
  clear success
  induction trace with
  | next step _ induction =>
    obtain ⟨body, operation, _, _, stepped⟩ := step
    exact induction.trans (step_effect _ _ _ _ _ _ _ _ stepped).literals
  | returned step _ =>
    obtain ⟨body, operation, _, _, stepped⟩ := step
    exact (leaveFrame_literals _ _).trans (step_effect _ _ _ _ _ _ _ _ stepped).literals
  | tailCall step _ _ _ _ entered _ _ induction =>
    obtain ⟨body, operation, _, _, stepped⟩ := step
    exact induction.trans ((enterFrame_setup _ _ _ _ _ entered).literals.trans
      ((leaveFrame_literals _ _).trans (step_effect _ _ _ _ _ _ _ _ stepped).literals))
  | call step _ entered _ _ _ childInduction induction
  | construct step _ entered _ _ _ _ childInduction induction =>
    obtain ⟨body, operation, _, _, stepped⟩ := step
    exact induction.trans (childInduction.trans
      ((enterFrame_setup _ _ _ _ _ entered).literals.trans
        (step_effect _ _ _ _ _ _ _ _ stepped).literals))
#print axioms run_literals

/-- A successful invocation ends with the caller's literal bindings, so an `ldstr` after a call
    loads the object the caller bound before it. -/
theorem invoke_literals {program : CIL.Program} {fuel method : Nat}
    {arguments values : List Value} {initial final : Memory}
    (success : invoke program fuel method arguments initial = .ok (final, values)) :
    final.literals = initial.literals := by
  obtain ⟨_, _, _, _, _, _, setup, executed⟩ := invoke_success_setup success
  exact (run_literals executed).trans (enterFrame_setup _ _ _ _ _ setup).literals
#print axioms invoke_literals

end CIL.Safety
