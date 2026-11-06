import CIL.Safety.HeapObjects
import CIL.Safety.ArrayAllocationLemmas
import CIL.Safety.MemoryBelow

/-!
# Fresh class instances

What a successful `allocateObject` leaves behind: one new live allocation of object kind, every
older allocation, byte and authority unchanged, and the heap budget reduced by the instance's
size. `CIL/Safety/ExecutionInvariants.lean` classifies the `newobj` step by this effect.
-/

namespace CIL.Safety

/-- Object creation adds one live object allocation with zeroed bytes and authority over them,
    charges its size to the heap budget, and changes no frame. -/
inductive ObjectAllocationEffect (memory : Memory) : Reference → Memory → Prop where
  | fresh {type size identity allocated}
      (affordable : size ≤ memory.heapBudget)
      (allocation : allocate memory ⟨.object type, ⟨size, objectAlignment, []⟩, true, [size]⟩ =
        .ok (identity, allocated)) :
      ObjectAllocationEffect memory ⟨identity, 0⟩
        { arrayMemory allocated identity size with heapBudget := memory.heapBudget - size }

/-- A successful allocation retains its checked allocation evidence and budget. -/
theorem allocateObject_effect {memory result : Memory} {type : RuntimeType} {size : Nat}
    {object : Reference} (success : allocateObject memory type size = .ok (object, result)) :
    ObjectAllocationEffect memory object result := by
  unfold allocateObject at success
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  repeat' first
    | solve | exact .fresh (by omega) (checkedAt_ok (by assumption))
    | cases success
    | split at success

#print axioms allocateObject_effect

/-- The old allocation table is preserved and the new identity is fresh. -/
theorem ObjectAllocationEffect.allocations {memory result : Memory} {object : Reference}
    (effect : ObjectAllocationEffect memory object result) :
    AllocationExtension memory result := by
  cases effect with
  | fresh _ allocation =>
    have extension := allocate_extends_allocations _ _ _ _ allocation
    exact ⟨extension.next, extension.lookup⟩

#print axioms ObjectAllocationEffect.allocations

/-- Granting authority over the new instance preserves well-formed memory. -/
theorem ObjectAllocationEffect.wellFormed {memory result : Memory} {object : Reference}
    (effect : ObjectAllocationEffect memory object result) (valid : memory.WellFormed) :
    result.WellFormed := by
  cases effect with
  | fresh _ allocation =>
    have ready := allocate_preserves_wellFormed _ _ _ _ valid allocation
    refine ⟨ready.1, ?_⟩
    intro permission member
    rcases List.mem_cons.mp member with rfl | member
    · have found := allocation_lookup _ _ _ _ allocation
      exact ⟨_, found, by simp⟩
    · exact ready.2 permission member

#print axioms ObjectAllocationEffect.wellFormed

/-- The new reference names a live instance at offset 0, so it may be held and passed on. -/
theorem ObjectAllocationEffect.object_valid {memory result : Memory} {object : Reference}
    (effect : ObjectAllocationEffect memory object result) :
    formObject result (.address object) = .ok (.object (.address object)) := by
  cases effect with
  | fresh _ allocation =>
    have found := allocation_lookup _ _ _ _ allocation
    simp [formObject, liveAllocation, arrayMemory, found, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms ObjectAllocationEffect.object_valid

/-- Object creation retains every pre-existing byte, authority and allocation descriptor. -/
theorem ObjectAllocationEffect.below {memory result : Memory} {object : Reference}
    (effect : ObjectAllocationEffect memory object result) :
    MemoryBelow memory.nextIdentity memory result := by
  cases effect with
  | fresh _ allocation =>
    have before := allocate_preserves_memory_below _ _ _ _ allocation
    have fresh := (allocation_identity_fresh _ _ _ _ allocation).1
    refine before.trans ⟨fun _ _ => rfl, ?_, ?_⟩
    · intro identity old offset
      simp only [arrayMemory, fresh, beq_iff_eq, Nat.ne_of_lt old, ite_false]
    · intro identity old offset writing
      simp [arrayMemory, permitted, viewContains, fresh, Ne.symm (Nat.ne_of_lt old)]

#print axioms ObjectAllocationEffect.below

/-- Object creation never changes the static field registry. -/
theorem ObjectAllocationEffect.registry {memory result : Memory} {object : Reference}
    (effect : ObjectAllocationEffect memory object result) :
    result.staticBindings = memory.staticBindings := by
  cases effect with
  | fresh _ allocation =>
    unfold allocate at allocation
    split at allocation <;> try cases allocation
    split at allocation <;> cases allocation
    rfl

#print axioms ObjectAllocationEffect.registry

/-- In well-formed memory with budget for it, an instance of fewer than `nativeLimit` bytes is
    allocated at the next identity, giving `objectMemory`. -/
theorem allocateObject_ok {memory : Memory} (formed : memory.WellFormed) (type : RuntimeType)
    {size : Nat} (affordable : size ≤ memory.heapBudget) (bounded : size < nativeLimit) :
    allocateObject memory type size =
      .ok (⟨memory.nextIdentity, 0⟩, objectMemory memory type size) := by
  have unused : memory.allocations memory.nextIdentity = none := by
    cases found : memory.allocations memory.nextIdentity with
    | none => rfl
    | some allocation => exact absurd (formed.1 _ _ found).1 (Nat.lt_irrefl _)
  have aligned : 0 < objectAlignment := by decide
  simp only [allocateObject, allocate, Allocation.valid, objectMemory, arrayMemory, unused,
    bounded, aligned, Nat.not_lt.mpr affordable, checkedAt, Except.mapError, Bind.bind,
    Except.bind, Pure.pure, Except.pure, decide_true, List.all_cons, List.all_nil,
    Nat.le_refl, Bool.and_true, Bool.not_true, Bool.false_eq_true, ite_false,
    Option.isSome_none, Except.ok.injEq, Prod.mk.injEq, true_and]
  congr 1
  funext identity offset
  by_cases same : identity = memory.nextIdentity <;> simp [same]

#print axioms allocateObject_ok

/-- Without budget for it, `newobj` fails with `allocationFailure`, before any allocation. -/
theorem allocateObject_insufficient {memory : Memory} (type : RuntimeType) {size : Nat}
    (insufficient : memory.heapBudget < size) :
    allocateObject memory type size =
      .error (.allocationFailure size memory.heapBudget) := by
  simp [allocateObject, insufficient, Bind.bind, Except.bind]

#print axioms allocateObject_insufficient

end CIL.Safety
