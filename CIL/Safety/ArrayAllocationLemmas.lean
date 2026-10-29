import CIL.Safety.ArrayAllocation
import CIL.Safety.FrameSetupLemmas

/-! # Freshness and initialized storage evidence for reference-free heap arrays -/

namespace CIL.Safety

/-- Array creation adds one heap allocation without changing frame ownership. -/
inductive ArrayAllocationEffect (memory : Memory) : ArrayView → Memory → Prop where
  | fresh {element length identity allocated}
      (supported : element.allocationSupported = true) (bounded : length < 2^31)
      (allocation : allocate memory
        ⟨.managedHeap, ⟨length * element.width, element.allocationAlignment, []⟩, true,
          [length * element.width]⟩ = .ok (identity, allocated)) :
      ArrayAllocationEffect memory ⟨.address ⟨identity, 0⟩, length, element⟩
        (arrayMemory allocated identity (length * element.width))

/-- Successful allocation retains checked allocation evidence and the supported shape bounds. -/
theorem allocateArray_effect {memory result : Memory} {element : CIL.ArrayElement}
    {length : Nat} {view : ArrayView}
    (success : allocateArray memory element length = .ok (view, result)) :
    ArrayAllocationEffect memory view result := by
  unfold allocateArray at success
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  repeat' first
    | solve |
        exact .fresh (by cases value : element.allocationSupported <;> simp_all)
          (by simp only [maxArrayLength] at *; omega) (checkedAt_ok (by assumption))
    | cases success
    | split at success

#print axioms allocateArray_effect

/-- Length decoding cannot turn a failed allocation into a successful array. -/
theorem newArray_effect {memory result : Memory} {element : CIL.ArrayElement}
    {length : CIL.Value} {view : ArrayView}
    (success : newArray memory element length = .ok (view, result)) :
    ArrayAllocationEffect memory view result := by
  unfold newArray at success
  cases length <;> simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  all_goals repeat' first
    | exact allocateArray_effect success
    | cases success
    | split at success

#print axioms newArray_effect

/-- The old allocation table is preserved and the new identity is fresh. -/
theorem ArrayAllocationEffect.allocations {memory result : Memory} {view : ArrayView}
    (effect : ArrayAllocationEffect memory view result) : AllocationExtension memory result := by
  cases effect with
  | fresh _ _ allocation =>
    have extension := allocate_extends_allocations _ _ _ _ allocation
    exact ⟨extension.next, extension.lookup⟩

#print axioms ArrayAllocationEffect.allocations

/-- Granting the new payload view preserves well-formed memory. -/
theorem ArrayAllocationEffect.wellFormed {memory result : Memory} {view : ArrayView}
    (effect : ArrayAllocationEffect memory view result) (valid : memory.WellFormed) :
    result.WellFormed := by
  cases effect with
  | fresh _ _ allocation =>
    have ready := allocate_preserves_wellFormed _ _ _ _ valid allocation
    refine ⟨ready.1, ?_⟩
    intro permission member
    rcases List.mem_cons.mp member with rfl | member
    · have found := allocation_lookup _ _ _ _ allocation
      exact ⟨_, found, by simp⟩
    · exact ready.2 permission member

#print axioms ArrayAllocationEffect.wellFormed

/-- New array views refer to a live allocation of exactly their payload extent. -/
theorem ArrayAllocationEffect.view_valid {memory result : Memory} {view : ArrayView}
    (effect : ArrayAllocationEffect memory view result) : view.validate result = .ok () := by
  cases effect with
  | fresh supported bounded allocation =>
    have found := allocation_lookup _ _ _ _ allocation
    rename_i element length identity allocated
    have width : 0 < element.width ∧ element.width < 2^16 := by
      simpa [CIL.ArrayElement.allocationSupported] using supported
    have extent : length * element.width < nativeLimit := by
      have := Nat.mul_le_mul (Nat.le_of_lt bounded) (Nat.le_of_lt width.2)
      simp only [nativeLimit]
      omega
    simp only [nativeLimit] at extent
    simp [ArrayView.validate, ArrayView.storage, SpanView.validate, arrayMemory,
      liveAllocation, found, width.1, bounded, extent, nativeLimit,
      show element.width < 2^64 by omega, Pure.pure, Except.pure, Bind.bind, Except.bind]

#print axioms ArrayAllocationEffect.view_valid

/-- Array creation retains every pre-existing byte, authority and allocation descriptor. -/
theorem ArrayAllocationEffect.below {memory result : Memory} {view : ArrayView}
    (effect : ArrayAllocationEffect memory view result) :
    MemoryBelow memory.nextIdentity memory result := by
  cases effect with
  | fresh _ _ allocation =>
    have before := allocate_preserves_memory_below _ _ _ _ allocation
    have fresh := (allocation_identity_fresh _ _ _ _ allocation).1
    refine before.trans ⟨fun _ _ => rfl, ?_, ?_⟩
    · intro identity old offset
      simp only [arrayMemory, fresh, beq_iff_eq, if_neg (Nat.ne_of_lt old)]
    · intro identity old offset writing
      simp [arrayMemory, permitted, viewContains, fresh, Ne.symm (Nat.ne_of_lt old)]

#print axioms ArrayAllocationEffect.below

/-- Array allocation never changes the static field registry. -/
theorem ArrayAllocationEffect.registry {memory result : Memory} {view : ArrayView}
    (effect : ArrayAllocationEffect memory view result) :
    result.staticBindings = memory.staticBindings := by
  cases effect with
  | fresh _ _ allocation =>
    unfold allocate at allocation
    split at allocation <;> try cases allocation
    split at allocation <;> cases allocation
    rfl

#print axioms ArrayAllocationEffect.registry

end CIL.Safety
