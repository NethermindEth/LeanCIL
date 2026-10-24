import CIL.Safety.StaticMemory
import CIL.Safety.InstructionMemoryLemmas

/-!
# Static instruction lemmas

What a successful static instruction guarantees: a cached static binding is returned
unchanged and its bytes match the descriptor, static resolution keeps memory well formed and
only extends allocations, and every static instruction satisfies a
`StaticInstructionContract`. The static world invariant builds on these in
`CIL.Safety.StaticWorld`.
-/

namespace CIL.Safety

/-- A successful resolution through a cached binding leaves memory unchanged, returns the
    cached reference, and implies the binding holds exactly the descriptor's bytes. -/
theorem cached_static_reference_checked (descriptor : CIL.StaticDescriptor) (m final : Memory)
    (name : Nat) (reference result : Reference)
    (cache : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) =
      some (name, reference))
    (success : staticReference descriptor m = .ok (final, result)) :
    final = m ∧ result = reference ∧
      read m reference descriptor.bytes.length 1 = .ok descriptor.bytes := by
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
          have he : bytes = descriptor.bytes := by
            simpa using (by assumption : (bytes == descriptor.bytes) = true)
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
  /-- The effect of an ordinary memory instruction. -/
  | ordinary {m result} (effect : InstructionEffect m result) :
      StaticInstructionEffect body m result
  /-- Resolving the static descriptor extracted for some pc of `body`. -/
  | reference {m result pc site descriptor reference}
      (selected : body.staticSites.find? (fun site => site.1 == pc) = some (site, descriptor))
      (h : staticReference descriptor m = .ok (result, reference)) :
      StaticInstructionEffect body m result

theorem StaticInstructionEffect.wellFormed {body : CIL.Method} {m result : Memory}
    (effect : StaticInstructionEffect body m result) (hm : m.WellFormed) :
    result.WellFormed := by
  cases effect with
  | ordinary effect => exact effect.wellFormed hm
  | reference _ h => exact staticReference_preserves_wellFormed _ _ _ _ hm h

theorem StaticInstructionEffect.allocations {body : CIL.Method} {m result : Memory}
    (effect : StaticInstructionEffect body m result) : AllocationExtension m result := by
  cases effect with
  | ordinary effect => exact effect.allocations
  | reference _ h => exact staticReference_extends_allocations _ _ _ _ h

/-- A reference that passes an access check forms in that memory. -/
theorem access_reference_valid (m : Memory) (r : Reference) (width alignment : Nat)
    (writing : Bool) (h : access m r width alignment writing = .ok ()) : form m r = .ok r := by
  unfold access at h
  cases hf : form m r with
  | error fault => simp [hf, Bind.bind, Except.bind] at h
  | ok formed =>
    have same := form_returns_input _ _ _ hf
    subst formed
    rfl

theorem read_reference_valid (m : Memory) (r : Reference) (width alignment : Nat)
    (bytes : List (BitVec 8)) (h : read m r width alignment = .ok bytes) : form m r = .ok r := by
  unfold read at h
  cases ha : access m r width alignment false with
  | error fault => simp [ha, Bind.bind, Except.bind] at h
  | ok accessed =>
    cases accessed
    exact access_reference_valid _ _ _ _ _ ha

/-- The reference a static resolution returns forms in the resulting memory. -/
theorem staticReference_reference_valid (descriptor : CIL.StaticDescriptor) (m result : Memory)
    (reference : Reference) (h : staticReference descriptor m = .ok (result, reference)) :
    form result reference = .ok reference := by
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨key, cached⟩ := binding
    obtain ⟨rfl, rfl, bytes⟩ := cached_static_reference_checked _ _ _ _ _ _ hc h
    exact read_reference_valid _ _ _ _ _ bytes
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
      have lookup := allocation_lookup m _ id memory ha
      have position : 0 < descriptor.bytes.length ∨ 0 = descriptor.bytes.length := by omega
      simp [form, liveAllocation, lookup, validPosition, nativeLimit, position,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem formValue_reference_valid (m : Memory) (r : ManagedReference) (value : Value)
    (h : formValue m r = .ok value) : (Value.reference r).Valid m := by
  have valid := formValue_result_valid _ _ _ h
  rw [formValue_returns_input _ _ _ h] at valid
  exact valid

/-- What a successful static instruction guarantees: its memory effect is an allowed
    `StaticInstructionEffect`, and the values it leaves are valid whenever its input stack was. -/
structure StaticInstructionContract (body : CIL.Method) (m result : Memory)
    (stack values : List Value) : Prop where
  effect : StaticInstructionEffect body m result
  values : m.WellFormed → ValuesValid m stack → ValuesValid result values

theorem StaticInstructionContract.ordinary {body : CIL.Method} {m result : Memory}
    {stack values : List Value} (contract : InstructionContract m result stack values) :
    StaticInstructionContract body m result stack values :=
  ⟨.ordinary contract.effect, contract.values⟩

/-- An allowed effect plus a proof that valid inputs give valid outputs in the new memory
    yields the contract; validity of the inputs carries over through the effect. -/
theorem StaticInstructionContract.of_effect {body : CIL.Method} {m result : Memory}
    {stack values : List Value} (effect : StaticInstructionEffect body m result)
    (preserve : ValuesValid result stack → ValuesValid result values) :
    StaticInstructionContract body m result stack values :=
  ⟨effect, fun hm valid => preserve (valid.preserve hm effect.allocations)⟩

/-- Every successful static instruction satisfies `StaticInstructionContract`. -/
theorem staticInstruction_contract (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp)
    (stack values : List Value) (m result : Memory)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    StaticInstructionContract body m result stack values := by
  unfold staticInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals repeat' first
    | solve | exact .ordinary (memoryInstruction_contract _ _ _ _ _ (by assumption))
    | solve |
        refine StaticInstructionContract.of_effect ?_ ?_
        · first | exact .ordinary (.unchanged _) | exact .reference (by assumption) (by assumption)
        · intro retained
          apply ValuesValid.cons
          · first
            | exact True.intro
            | rfl
            | exact retained.tail.head
            | exact retained.head
            | apply staticReference_reference_valid; assumption
            | apply formValue_reference_valid; assumption
          · first | exact retained | exact retained.tail | exact retained.tail.tail
    | cases h
    | split at h

theorem staticInstruction_effect (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp)
    (stack values : List Value) (m result : Memory)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    StaticInstructionEffect body m result := (staticInstruction_contract _ _ _ _ _ _ _ h).effect

theorem staticInstruction_preserves_wellFormed (body : CIL.Method) (pc : Nat)
    (operation : CIL.MemoryOp) (stack values : List Value) (m result : Memory)
    (hm : m.WellFormed)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    result.WellFormed := by
  exact (staticInstruction_effect _ _ _ _ _ _ _ h).wellFormed hm

#print axioms staticInstruction_preserves_wellFormed

end CIL.Safety
