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
    cached reference, and implies the binding is readable at the descriptor's width and,
    unless the value is opaque, holds exactly the descriptor's bytes. -/
theorem cached_static_reference_checked (descriptor : CIL.StaticDescriptor) (m final : Memory)
    (name : Nat) (reference result : Reference)
    (cache : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) =
      some (name, reference))
    (success : staticReference descriptor m = .ok (final, result)) :
    final = m ∧ result = reference ∧ ∃ bytes,
      read m reference descriptor.bytes.length 1 = .ok bytes ∧
      (descriptor.opaqueValue = false → bytes = descriptor.bytes) := by
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
          refine ⟨success.1.symm, success.2.symm, bytes, rfl, fun transparent => ?_⟩
          have admitted : (descriptor.opaqueValue || bytes == descriptor.bytes) = true := by
            assumption
          simpa [transparent] using admitted
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
    split at h
    · cases h
    cases ha : allocate m ⟨.immutableStatic,
        ⟨descriptor.bytes.length, descriptor.alignment, []⟩, true, [descriptor.bytes.length]⟩ <;>
      simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at h
    · cases h
    · rename_i allocated
      obtain ⟨id, memory⟩ := allocated
      cases h
      have hw := allocate_preserves_wellFormed _ _ _ _ hm ha
      refine { allocations := hw.allocations, views := ?_, slots := hw.slots }
      intro view hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · have lookup := allocation_lookup m _ id memory ha
        exact ⟨_, lookup, by simp⟩
      · exact hw.views view hv

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
    split at h
    · cases h
    cases ha : allocate m ⟨.immutableStatic,
        ⟨descriptor.bytes.length, descriptor.alignment, []⟩, true, [descriptor.bytes.length]⟩ <;>
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
    obtain ⟨rfl, rfl, bytes, readable, _⟩ := cached_static_reference_checked _ _ _ _ _ _ hc h
    exact read_reference_valid _ _ _ _ _ readable
  | none =>
    simp only [staticReference, hc] at h
    split at h
    · cases h
    cases ha : allocate m ⟨.immutableStatic,
        ⟨descriptor.bytes.length, descriptor.alignment, []⟩, true, [descriptor.bytes.length]⟩ <;>
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

/-- Readonly loads produce scalar data, never a reference requiring a liveness premise. -/
theorem staticLoadedValue_valid (descriptor : CIL.StaticDescriptor) (value : CIL.Value)
    (memory : Memory) (loaded : staticLoadedValue descriptor = some value) :
    (Value.scalar value).Valid memory := by
  unfold staticLoadedValue at loaded
  split at loaded
  · cases loaded; trivial
  · split at loaded <;> cases loaded <;> trivial

#print axioms staticLoadedValue_valid

/-- Every successful static instruction satisfies `StaticInstructionContract`. -/
theorem staticInstruction_contract (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp)
    (stack values : List Value) (m result : Memory)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    StaticInstructionContract body m result stack values := by
  unfold staticInstruction at h
  exact .ordinary (memoryInstruction_contract _ _ _ _ _ h)

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

/-- A descriptor `Method.staticAt` resolves is the one of the method's first site at that pc. -/
theorem staticAt_site {body : CIL.Method} {pc : Nat} {descriptor : CIL.StaticDescriptor}
    (resolved : body.staticAt pc = some descriptor) :
    ∃ site, body.staticSites.find? (fun site => site.1 == pc) = some (site, descriptor) := by
  unfold CIL.Method.staticAt at resolved
  cases found : body.staticSites.find? (fun site => site.1 == pc) with
  | none => simp [found] at resolved
  | some entry =>
    obtain ⟨site, other⟩ := entry
    simp only [found, Option.map_some, Option.some.injEq] at resolved
    exact ⟨site, by rw [resolved]⟩

#print axioms staticAt_site

/-- A successful `ldsfld` satisfies `StaticInstructionContract` for the value it pushes. -/
theorem staticLoad_contract (body : CIL.Method) (pc : Nat) (stack : List Value)
    (m result : Memory) (value : Value) (h : staticLoad body pc m = .ok (result, value)) :
    StaticInstructionContract body m result stack (value :: stack) := by
  unfold staticLoad at h
  cases resolved : body.staticAt pc with
  | none => simp only [resolved] at h; cases h
  | some descriptor =>
    obtain ⟨site, selected⟩ := staticAt_site resolved
    simp only [resolved, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    repeat' first
      | solve |
          refine StaticInstructionContract.of_effect ?_ ?_
          · first | exact .ordinary (.unchanged _) | exact .reference selected (by assumption)
          · intro retained
            apply ValuesValid.cons
            · apply staticLoadedValue_valid; assumption
            · exact retained
      | cases h
      | split at h

#print axioms staticLoad_contract

/-- A successful `ldsflda` or field `ldtoken` satisfies `StaticInstructionContract` for the
    reference it pushes. -/
theorem staticAddress_contract (body : CIL.Method) (pc : Nat) (stack : List Value)
    (m result : Memory) (value : Value) (h : staticAddress body pc m = .ok (result, value)) :
    StaticInstructionContract body m result stack (value :: stack) := by
  unfold staticAddress at h
  cases resolved : body.staticAt pc with
  | none => simp only [resolved] at h; cases h
  | some descriptor =>
    obtain ⟨site, selected⟩ := staticAt_site resolved
    simp only [resolved, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    split at h
    · cases h
    · rename_i resolution referenced
      obtain ⟨memory, reference⟩ := resolution
      cases h
      refine StaticInstructionContract.of_effect (.reference selected referenced) ?_
      intro retained
      apply ValuesValid.cons
      · apply staticReference_reference_valid; exact referenced
      · exact retained

#print axioms staticAddress_contract

/-- `ldsfld` of a descriptor whose initializer was checked pushes the descriptor's value and
    leaves memory unchanged. -/
theorem staticLoad_initialized {body : CIL.Method} {pc : Nat} {descriptor : CIL.StaticDescriptor}
    {memory : Memory} {value : CIL.Value} (site : body.staticAt pc = some descriptor)
    (computed : descriptor.opaqueValue = false)
    (initialized : descriptor.initializer.isSome = true)
    (decoded : staticLoadedValue descriptor = some value) :
    staticLoad body pc memory = .ok (memory, .scalar value) := by
  simp only [staticLoad, site, computed, initialized, decoded, Bool.false_eq_true, ite_false,
    ite_true]
  rfl

#print axioms staticLoad_initialized

/-- `ldsflda` or a field `ldtoken` pushes the reference `staticReference` resolves for the
    descriptor bound to its pc. -/
theorem staticAddress_resolved {body : CIL.Method} {pc : Nat} {descriptor : CIL.StaticDescriptor}
    {memory result : Memory} {reference : Reference} (site : body.staticAt pc = some descriptor)
    (resolved : staticReference descriptor memory = .ok (result, reference)) :
    staticAddress body pc memory = .ok (result, .reference (.address reference)) := by
  simp only [staticAddress, site, resolved, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms staticAddress_resolved

/-- With a descriptor bound to its pc, `staticAddress` resolves that descriptor's storage, so a
    step can rewrite the read without evaluating the site table. -/
theorem staticAddress_site {body : CIL.Method} {pc : Nat} {descriptor : CIL.StaticDescriptor}
    {memory : Memory} (site : body.staticAt pc = some descriptor) :
    staticAddress body pc memory = (do
      let (memory, reference) ← staticReference descriptor memory
      return (memory, .reference (.address reference))) := by
  rw [staticAddress, site]

#print axioms staticAddress_site

/-- A loaded static field value is a scalar, never a home. -/
theorem staticLoad_not_spanHome {body : CIL.Method} {pc : Nat} {memory : Memory}
    {result : Memory × Value} (loaded : staticLoad body pc memory = .ok result) :
    result.2.isHome = false := by
  unfold staticLoad at loaded
  repeat' first
    | (cases loaded <;> rfl)
    | split at loaded
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at loaded

#print axioms staticLoad_not_spanHome

/-- A static field address is a reference, never a home. -/
theorem staticAddress_not_spanHome {body : CIL.Method} {pc : Nat} {memory : Memory}
    {result : Memory × Value} (addressed : staticAddress body pc memory = .ok result) :
    result.2.isHome = false := by
  unfold staticAddress at addressed
  repeat' first
    | (cases addressed <;> rfl)
    | split at addressed
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at addressed

#print axioms staticAddress_not_spanHome

end CIL.Safety
