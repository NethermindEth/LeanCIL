import CIL.Safety.ExecutionTrace
import CIL.Safety.FrameSetupLemmas
import CIL.Safety.StaticMemoryLemmas

/-!
# What one checked step may change

`step_contract` classifies every successful checked step by its effect on memory and frame
(`StepEffect`) and shows that it pushes only values valid in the resulting memory. The
memory-preservation lemmas below, from `step_preserves_wellFormed` up to
`invoke_preserves_wellFormed`, are all derived from this one dispatcher proof, so a new
instruction needs a contract here before anything above it can be proved.
-/

namespace CIL.Safety

/-- The memory a step leaves behind, whatever it asks the driver to do next. -/
def FrameAction.memory : FrameAction → Memory
  | .next _ _ _ m | .call _ _ _ m | .construct _ _ _ _ _ _ m | .returned _ m => m

/-- Calls and returns keep the current frame until the run dispatcher acts;
    ordinary steps and constructor allocation supply their updated frame. -/
def FrameAction.frameAfter (action : FrameAction) (current : Frame) : Frame :=
  match action with
  | .next _ _ frame _ | .construct _ _ _ frame _ _ _ => frame
  | .call _ _ _ _ | .returned _ _ => current

/-- A step's memory and frame changes, with successful primitive operations as
    evidence. Value-stack validity is independent of this effect classification. -/
inductive StepEffect (body : CIL.Method) (frame : Frame) (m : Memory) :
    Frame → Memory → Prop where
  | memory {result} (effect : StaticInstructionEffect body m result) :
      StepEffect body frame m frame result
  | store {index slot final value result}
      (found : frame.locals[index]? = some slot)
      (stored : storeLocal m slot value = .ok (final, result)) :
      StepEffect body frame m { frame with locals := frame.locals.set index final } result
  | valueHome {home result r width value}
      (allocated : allocateHome m frame.activation width = .ok (r, home))
      (stored : storeValue home (.address r) value = .ok result) :
      StepEffect body frame m { frame with owned := r.allocation :: frame.owned } result
  | localHome {home result r width slot final value}
      (allocated : allocateHome m frame.activation width = .ok (r, home))
      (stored : storeLocal home slot value = .ok (final, result)) :
      StepEffect body frame m { frame with owned := r.allocation :: frame.owned } result

theorem StepEffect.wellFormed {body : CIL.Method} {frame final : Frame} {m result : Memory}
    (effect : StepEffect body frame m final result) (hm : m.WellFormed) : result.WellFormed := by
  cases effect with
  | memory effect => exact effect.wellFormed hm
  | store _ stored => exact storeLocal_preserves_wellFormed _ _ _ _ _ hm stored
  | valueHome allocated stored =>
    exact storeValue_preserves_wellFormed _ _ _ _
      (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocated) stored
  | localHome allocated stored =>
    exact storeLocal_preserves_wellFormed _ _ _ _ _
      (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocated) stored

theorem StepEffect.allocations {body : CIL.Method} {frame final : Frame} {m result : Memory}
    (effect : StepEffect body frame m final result) : AllocationExtension m result := by
  cases effect with
  | memory effect => exact effect.allocations
  | store _ stored => exact storeLocal_extends_allocations _ _ _ _ _ stored
  | valueHome allocated stored =>
    exact (allocateHome_fresh _ _ _ _ _ allocated).1.trans
      (storeValue_effect _ _ _ _ stored).allocations
  | localHome allocated stored =>
    exact (allocateHome_fresh _ _ _ _ _ allocated).1.trans
      (storeLocal_extends_allocations _ _ _ _ _ stored)

/-- A value loaded from a local is valid in the memory it was loaded from. -/
theorem loadLocal_result_valid (m : Memory) (slot : LocalSlot) (value : Value)
    (h : loadLocal m slot = .ok value) : value.Valid m := by
  unfold loadLocal at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | rfl
      | solve | cases ‹Opaque128Value› <;> rfl
      | solve | exact loadSnapshot_numeric (by assumption)
      | solve | apply formValue_result_valid; assumption
      | cases h
      | split at h

theorem localAddress_result_valid (m : Memory) (slot : LocalSlot) (value : Value)
    (h : localAddress m slot = .ok value) : value.Valid m := by
  cases slot with
  | root root => cases h
  | opaque128 _ => cases h
  | bytes kind r => exact formValue_result_valid m (.address r) value h

theorem ValuesValid.drop {m : Memory} {values : List Value}
    (valid : ValuesValid m values) (count : Nat) : ValuesValid m (values.drop count) :=
  fun _ member => valid _ (List.mem_of_mem_drop member)

theorem checkedValues_preserved (m result : Memory) (values checked : List Value)
    (hm : m.WellFormed) (ext : AllocationExtension m result)
    (h : values.mapM (checkedValue m) = .ok checked) : ValuesValid result checked :=
  (checkedValues_valid _ _ _ h).2.preserve hm ext

theorem allocated_store_reference_valid (m home result : Memory) (activation width : Nat)
    (r : Reference) (value : CIL.Value) (hm : m.WellFormed)
    (allocation : allocateHome m activation width = .ok (r, home))
    (store : storeValue home (.address r) value = .ok result) : form result r = .ok r :=
  (storeValue_effect _ _ _ _ store).allocations.preserves_reference
    (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocation) r r
    (allocateHome_reference_valid _ _ _ _ _ allocation)

theorem allocated_storeLocal_reference_valid (m home result : Memory) (activation width : Nat)
    (r : Reference) (slot finalSlot : LocalSlot) (value : Value) (hm : m.WellFormed)
    (allocation : allocateHome m activation width = .ok (r, home))
    (store : storeLocal home slot value = .ok (finalSlot, result)) : form result r = .ok r :=
  (storeLocal_extends_allocations _ _ _ _ _ store).preserves_reference
    (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocation) r r
    (allocateHome_reference_valid _ _ _ _ _ allocation)

/-- Every value the action carries is valid in its memory: the new stack, the returned
    values, or a child's arguments together with the caller stack left behind. -/
def FrameAction.LiveValues (action : FrameAction) : Prop :=
  match action with
  | .next _ values _ memory | .returned values memory => ValuesValid memory values
  | .call _ args rest memory | .construct _ args rest _ _ _ memory =>
    ValuesValid memory args ∧ ValuesValid memory rest

/-- One dispatcher proof supplies memory/frame effects and conditional value validity. -/
structure StepContract (body : CIL.Method) (frame : Frame) (stack : List Value)
    (m : Memory) (action : FrameAction) : Prop where
  effect : StepEffect body frame m (action.frameAfter frame) action.memory
  values : m.WellFormed → ValuesValid m stack → action.LiveValues

theorem StepContract.of_effect {body : CIL.Method} {frame : Frame} {stack : List Value}
    {m : Memory} {action : FrameAction}
    (effect : StepEffect body frame m (action.frameAfter frame) action.memory)
    (preserve : m.WellFormed → AllocationExtension m action.memory →
      ValuesValid action.memory stack → action.LiveValues) :
    StepContract body frame stack m action :=
  ⟨effect, fun hm valid => preserve hm effect.allocations (valid.preserve hm effect.allocations)⟩

theorem StepContract.instruction {body : CIL.Method} {frame : Frame} {stack values : List Value}
    {m result : Memory} {pc : Nat} (contract : InstructionContract m result stack values) :
    StepContract body frame stack m (.next pc values frame result) :=
  ⟨.memory (.ordinary contract.effect), contract.values⟩

theorem StepContract.staticInstruction {body : CIL.Method} {frame : Frame}
    {stack values : List Value} {m result : Memory} {pc : Nat}
    (contract : StaticInstructionContract body m result stack values) :
    StepContract body frame stack m (.next pc values frame result) :=
  ⟨.memory contract.effect, contract.values⟩

/-- Every successful checked step has a `StepContract`. The proof walks every dispatcher arm,
    so it is the place that breaks when an instruction is added without an effect. -/
theorem step_contract (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (h : step body operation pc args frame stack m = .ok action) :
    StepContract body frame stack m action := by
  unfold step at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals repeat' first
    | solve | exact .staticInstruction (staticInstruction_contract _ _ _ _ _ _ _ (by assumption))
    | solve | exact .instruction (instruction_contract _ _ _ _ _ (by assumption))
    | solve |
        refine StepContract.of_effect ?_ ?_
        · first
          | exact .memory (.ordinary (.unchanged _))
          | exact .store (by assumption) (by assumption)
          | exact .valueHome (by assumption) (by assumption)
          | exact .localHome (by assumption) (by assumption)
        · intro hm ext retained
          repeat' first
            | exact retained
            | solve | simp [FrameAction.LiveValues, ValuesValid, Value.Valid, numericValue]
            | exact retained.tail
            | solve | exact retained.drop _
            | solve | apply checkedValues_preserved _ _ _ _ hm ext; assumption
            | solve |
                apply ValuesValid.append
                · apply checkedValues_preserved _ _ _ _ hm ext; assumption
                · first | exact retained.drop _ | exact retained.tail.tail
            | solve |
                apply ValuesValid.cons
                · first
                  | rfl
                  | exact (checkedValue_valid _ _ _ (by assumption)).2
                  | apply loadLocal_result_valid; assumption
                  | apply localAddress_result_valid; assumption
                  | apply allocated_store_reference_valid; exact hm; assumption; assumption
                  | apply allocated_storeLocal_reference_valid; exact hm; assumption; assumption
                · first
                  | exact retained
                  | exact retained.drop _
                  | exact retained.tail.tail
                  | exact retained.tail
                  | apply checkedValues_preserved _ _ _ _ hm ext; assumption
            | constructor
    | cases h
    | split at h

theorem step_effect (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (h : step body operation pc args frame stack m = .ok action) :
    StepEffect body frame m (action.frameAfter frame) action.memory :=
  (step_contract _ _ _ _ _ _ _ _ h).effect

theorem step_preserves_wellFormed (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed)
    (h : step body operation pc args frame stack m = .ok action) : action.memory.WellFormed := by
  exact (step_effect _ _ _ _ _ _ _ _ h).wellFormed hm

#print axioms step_preserves_wellFormed

theorem programStep_preserves_wellFormed (program : CIL.Program) (method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory) (action : FrameAction)
    (hm : m.WellFormed) (hs : ProgramStep program method pc args frame stack m action) :
    action.memory.WellFormed := by
  obtain ⟨body, op, _, _, hs⟩ := hs
  exact step_preserves_wellFormed _ _ _ _ _ _ _ _ hm hs

/-- A successful run, including all nested calls and frame teardowns, ends in well-formed
    memory. -/
theorem run_preserves_wellFormed (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value) (hm : m.WellFormed)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    final.WellFormed := by
  have trace := run_success_trace program fuel method pc args frame stack m final values h
  clear h
  induction trace with
  | next step _ ih =>
    exact ih (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
  | returned step _ =>
    exact leaveFrame_preserves_wellFormed _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step)
  | call step _ enter _ _ _ childIH ih
  | construct step _ enter _ _ _ _ childIH ih =>
    exact ih (childIH (enterFrame_preserves_wellFormed _ _ _ _ _
      (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ hm step) enter))

#print axioms run_preserves_wellFormed

theorem invoke_preserves_wellFormed (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory) (hm : m.WellFormed)
    (h : invoke program fuel method args m = .ok (final, values)) : final.WellFormed := by
  obtain ⟨_, _, _, _, _, _, setup, executed⟩ := invoke_success_setup h
  exact run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _
    (enterFrame_preserves_wellFormed _ _ _ _ _ hm setup) executed

#print axioms invoke_preserves_wellFormed

end CIL.Safety
