import CIL.Safety.StaticMemory
import CIL.Safety.InstructionMemoryLemmas
namespace CIL.Safety
theorem cached_static_reference_checked (descriptor : CIL.StaticDescriptor) (m final : Memory)
    (name : Nat) (reference result : Reference)
    (cache : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) = some (name, reference))
    (success : staticReference descriptor m = .ok (final, result)) :
    final = m ∧ result = reference ∧ read m reference descriptor.bytes.length 1 = .ok descriptor.bytes := by
  simp only [staticReference, cache] at success
  cases hl : liveAllocation m reference.allocation with
  | error fault => simp [hl, checkedAt, Except.mapError, Bind.bind, Except.bind] at success
  | ok allocation =>
    simp only [hl, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at success
    split at success
    · cases hr : read m reference descriptor.bytes.length 1 with
      | error fault => simp [hr] at success
      | ok bytes =>
        simp only [hr] at success
        split at success
        · simp only [Except.ok.injEq, Prod.mk.injEq] at success
          have he : bytes = descriptor.bytes := by simpa using (by assumption : (bytes == descriptor.bytes) = true)
          exact ⟨success.1.symm, success.2.symm, congrArg Except.ok he⟩
        · cases success
    · cases success
#print axioms cached_static_reference_checked
theorem staticReference_preserves_wellFormed (descriptor : CIL.StaticDescriptor)
    (m result : Memory) (reference : Reference) (hm : m.WellFormed)
    (h : staticReference descriptor m = .ok (result, reference)) : result.WellFormed := by
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨name, cached⟩ := binding
    obtain ⟨rfl, _, _⟩ := cached_static_reference_checked _ _ _ _ _ _ hc h
    exact hm
  | none =>
    simp only [staticReference, hc] at h
    cases ha : allocate m ⟨.immutableStatic, ⟨descriptor.bytes.length, 1, []⟩,
        true, [descriptor.bytes.length]⟩ <;>
      simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at h
    · cases h
    · rename_i allocated
      obtain ⟨id, memory⟩ := allocated
      cases h
      have hw := allocate_preserves_wellFormed _ _ _ _ hm ha
      refine ⟨hw.1, ?_⟩
      intro view hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · have lookup := allocation_lookup m _ id memory ha
        exact ⟨_, lookup, by simp⟩
      · exact hw.2 view hv

#print axioms staticReference_preserves_wellFormed

theorem staticReference_extends_allocations (descriptor : CIL.StaticDescriptor)
    (m result : Memory) (reference : Reference)
    (h : staticReference descriptor m = .ok (result, reference)) :
    AllocationExtension m result := by
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨name, cached⟩ := binding
    obtain ⟨rfl, _, _⟩ := cached_static_reference_checked _ _ _ _ _ _ hc h
    exact .refl _
  | none =>
    simp only [staticReference, hc] at h
    cases ha : allocate m ⟨.immutableStatic, ⟨descriptor.bytes.length, 1, []⟩,
        true, [descriptor.bytes.length]⟩ <;>
      simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at h
    · cases h
    · rename_i allocated
      obtain ⟨id, memory⟩ := allocated
      cases h
      have ext := allocate_extends_allocations _ _ _ _ ha
      exact ⟨ext.next, ext.lookup⟩

/-- Static instructions either use ordinary memory operations or initialize a
    descriptor selected from this method's extracted static sites. -/
inductive StaticInstructionEffect (body : CIL.Method) : Memory → Memory → Prop where
  | ordinary {m result} (effect : InstructionEffect m result) : StaticInstructionEffect body m result
  | reference {m result pc site descriptor reference}
      (selected : body.staticSites.find? (fun site => site.1 == pc) = some (site, descriptor))
      (h : staticReference descriptor m = .ok (result, reference)) : StaticInstructionEffect body m result

theorem StaticInstructionEffect.wellFormed {body : CIL.Method} {m result : Memory}
    (effect : StaticInstructionEffect body m result) (hm : m.WellFormed) : result.WellFormed := by
  cases effect with
  | ordinary effect => exact effect.wellFormed hm
  | reference _ h => exact staticReference_preserves_wellFormed _ _ _ _ hm h

theorem StaticInstructionEffect.allocations {body : CIL.Method} {m result : Memory}
    (effect : StaticInstructionEffect body m result) : AllocationExtension m result := by
  cases effect with
  | ordinary effect => exact effect.allocations
  | reference _ h => exact staticReference_extends_allocations _ _ _ _ h

theorem staticInstruction_effect (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp)
    (stack values : List Value) (m result : Memory)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    StaticInstructionEffect body m result := by
  unfold staticInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact .ordinary (.unchanged _)
      | solve | exact .reference (by assumption) (by assumption)
      | solve | exact .ordinary (memoryInstruction_effect _ _ _ _ _ (by assumption))
      | cases h
      | split at h

theorem staticInstruction_preserves_wellFormed (body : CIL.Method) (pc : Nat)
    (operation : CIL.MemoryOp) (stack values : List Value) (m result : Memory)
    (hm : m.WellFormed)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) : result.WellFormed := by
  exact (staticInstruction_effect _ _ _ _ _ _ _ h).wellFormed hm

#print axioms staticInstruction_preserves_wellFormed

end CIL.Safety
