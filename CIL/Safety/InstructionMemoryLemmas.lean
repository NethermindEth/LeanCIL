import CIL.Safety.InstructionMemory

namespace CIL.Safety

theorem instructions_append (first second : List CIL.Op) (stack : List Value) (m : Memory) :
    instructions (first ++ second) stack m =
      (instructions first stack m).bind (fun (memory, values) => instructions second values memory) := by
  induction first generalizing stack m with
  | nil => rfl
  | cons op first ih =>
    simp only [List.cons_append, instructions]
    cases hi : instruction op stack m with
    | error fault => rfl
    | ok result =>
      rcases result with ⟨memory, values⟩
      exact ih values memory

theorem instruction_fault_cannot_be_erased (first second : List CIL.Op) (stack : List Value)
    (m : Memory) (fault : ExecutionFault) (h : instructions first stack m = .error fault) :
    instructions (first ++ second) stack m = .error fault := by
  rw [instructions_append, h]
  rfl

theorem successful_instruction_prefix (first second : List CIL.Op) (stack : List Value)
    (m final : Memory) (values : List Value)
    (h : instructions (first ++ second) stack m = .ok (final, values)) :
    ∃ intermediate stack', instructions first stack m = .ok (intermediate, stack') := by
  rw [instructions_append] at h
  cases hi : instructions first stack m with
  | error fault => simp [hi, Except.bind] at h
  | ok result =>
    rcases result with ⟨memory, stack'⟩
    exact ⟨memory, stack', rfl⟩

/-- The only memory changes made by an ordinary instruction. Successful
    primitive operations retain their checks, independently of input invariants. -/
inductive InstructionEffect : Memory → Memory → Prop where
  | unchanged (m) : InstructionEffect m m
  | write {m result r bytes alignment} (h : write m r bytes alignment = .ok result) :
      InstructionEffect m result
  | snapshot {m result r bytes alignment} (h : writeSnapshot m r bytes alignment = .ok result) :
      InstructionEffect m result

theorem InstructionEffect.wellFormed {m result : Memory} (effect : InstructionEffect m result)
    (hm : m.WellFormed) : result.WellFormed := by
  cases effect with
  | unchanged => exact hm
  | write h => exact write_preserves_wellFormed _ _ _ _ _ hm h
  | snapshot h => exact writeSnapshot_preserves_wellFormed _ _ _ _ _ hm h

theorem InstructionEffect.allocations {m result : Memory} (effect : InstructionEffect m result) :
    AllocationExtension m result := by
  cases effect with
  | unchanged => exact .refl _
  | write h => exact write_extends_allocations _ _ _ _ _ h
  | snapshot h => exact writeSnapshot_extends_allocations _ _ _ _ _ h

theorem storeValue_effect (m result : Memory) (reference : ManagedReference) (value : CIL.Value)
    (h : storeValue m reference value = .ok result) : InstructionEffect m result := by
  unfold storeValue at h
  repeat' first
    | solve | exact .write (checkedAt_ok (by assumption))
    | solve | exact .snapshot (checkedAt_ok (by assumption))
    | cases h
    | split at h
    | simp only [Bind.bind, Except.bind] at h

set_option maxHeartbeats 800000 in
theorem memoryInstruction_effect (operation : CIL.MemoryOp) (stack values : List Value)
    (m result : Memory) (h : memoryInstruction operation stack m = .ok (result, values)) :
    InstructionEffect m result := by
  unfold memoryInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact .unchanged _
      | solve | exact .write (checkedAt_ok (by assumption))
      | solve | exact .snapshot (checkedAt_ok (by assumption))
      | solve | apply storeValue_effect; assumption
      | cases h
      | split at h

set_option maxHeartbeats 800000 in
theorem instruction_effect (operation : CIL.Op) (stack values : List Value) (m result : Memory)
    (h : instruction operation stack m = .ok (result, values)) : InstructionEffect m result := by
  unfold instruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact .unchanged _
      | solve | exact .write (checkedAt_ok (by assumption))
      | solve | exact .snapshot (checkedAt_ok (by assumption))
      | solve | apply memoryInstruction_effect; assumption
      | solve | apply storeValue_effect; assumption
      | cases h
      | split at h

theorem checked_write_preserves_wellFormed (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat) (reference : ManagedReference) (width : Nat)
    (hm : m.WellFormed)
    (h : checkedAt reference width (write m r bytes alignment) = .ok result) :
    result.WellFormed := by
  exact write_preserves_wellFormed _ _ _ _ _ hm (checkedAt_ok h)

theorem storeValue_preserves_wellFormed (m result : Memory) (reference : ManagedReference)
    (value : CIL.Value) (hm : m.WellFormed)
    (h : storeValue m reference value = .ok result) : result.WellFormed := by
  exact (storeValue_effect _ _ _ _ h).wellFormed hm

#print axioms storeValue_preserves_wellFormed

set_option maxHeartbeats 800000 in
theorem memoryInstruction_preserves_wellFormed (operation : CIL.MemoryOp) (stack values : List Value)
    (m result : Memory) (hm : m.WellFormed)
    (h : memoryInstruction operation stack m = .ok (result, values)) : result.WellFormed := by
  exact (memoryInstruction_effect _ _ _ _ _ h).wellFormed hm

#print axioms memoryInstruction_preserves_wellFormed

set_option maxHeartbeats 800000 in
theorem instruction_preserves_wellFormed (operation : CIL.Op) (stack values : List Value)
    (m result : Memory) (hm : m.WellFormed)
    (h : instruction operation stack m = .ok (result, values)) : result.WellFormed := by
  exact (instruction_effect _ _ _ _ _ h).wellFormed hm

#print axioms instruction_preserves_wellFormed

end CIL.Safety
