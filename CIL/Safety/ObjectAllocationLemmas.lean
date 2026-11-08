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
inductive ObjectAllocationEffect (memory : Memory) (type : RuntimeType) :
    Reference → Memory → Prop where
  | fresh {size identity allocated}
      (affordable : size ≤ memory.heapBudget)
      (allocation : allocate memory ⟨.object type, ⟨size, objectAlignment, []⟩, true, [size]⟩ =
        .ok (identity, allocated)) :
      ObjectAllocationEffect memory type ⟨identity, 0⟩
        { arrayMemory allocated identity size with heapBudget := memory.heapBudget - size }

/-- A successful allocation retains its checked allocation evidence and budget. -/
theorem allocateObject_effect {memory result : Memory} {type : RuntimeType} {size : Nat}
    {object : Reference} (success : allocateObject memory type size = .ok (object, result)) :
    ObjectAllocationEffect memory type object result := by
  unfold allocateObject at success
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  repeat' first
    | solve | exact .fresh (by omega) (checkedAt_ok (by assumption))
    | cases success
    | split at success

#print axioms allocateObject_effect

/-- The old allocation table is preserved and the new identity is fresh. -/
theorem ObjectAllocationEffect.allocations {memory result : Memory} {type : RuntimeType}
    {object : Reference}
    (effect : ObjectAllocationEffect memory type object result) :
    AllocationExtension memory result := by
  cases effect with
  | fresh _ allocation =>
    have extension := allocate_extends_allocations _ _ _ _ allocation
    exact ⟨extension.next, extension.lookup⟩

#print axioms ObjectAllocationEffect.allocations

/-- The one instance object creation adds is of `type`; every other instance was already there
    with the same runtime type. -/
theorem ObjectAllocationEffect.objects {memory result : Memory} {type : RuntimeType}
    {object : Reference} (effect : ObjectAllocationEffect memory type object result)
    {id : AllocationId} {allocation : Allocation} {created : RuntimeType}
    (present : result.allocations id = some allocation)
    (kind : allocation.kind = .object created) :
    created = type ∨
      ∃ earlier, memory.allocations id = some earlier ∧ earlier.kind = .object created := by
  cases effect with
  | fresh _ allocated =>
    unfold allocate at allocated
    split at allocated
    · cases allocated
    split at allocated
    · cases allocated
    cases allocated
    by_cases fresh : id = memory.nextIdentity
    · simp only [arrayMemory, fresh, ite_true, Option.some.injEq] at present
      subst present
      cases kind
      exact Or.inl rfl
    · simp only [arrayMemory, fresh, ite_false] at present
      exact Or.inr ⟨allocation, present, kind⟩

#print axioms ObjectAllocationEffect.objects

/-- Granting authority over the new instance preserves well-formed memory. -/
theorem ObjectAllocationEffect.wellFormed {memory result : Memory} {type : RuntimeType}
    {object : Reference}
    (effect : ObjectAllocationEffect memory type object result) (valid : memory.WellFormed) :
    result.WellFormed := by
  cases effect with
  | fresh _ allocation =>
    have ready := allocate_preserves_wellFormed _ _ _ _ valid allocation
    refine { allocations := ready.allocations, views := ?_, slots := ready.slots }
    intro permission member
    rcases List.mem_cons.mp member with rfl | member
    · have found := allocation_lookup _ _ _ _ allocation
      exact ⟨_, found, by simp⟩
    · exact ready.views permission member

#print axioms ObjectAllocationEffect.wellFormed

/-- The new reference names a live instance at offset 0, so it may be held and passed on. -/
theorem ObjectAllocationEffect.object_valid {memory result : Memory} {type : RuntimeType}
    {object : Reference}
    (effect : ObjectAllocationEffect memory type object result) :
    formObject result (.address object) = .ok (.object (.address object)) := by
  cases effect with
  | fresh _ allocation =>
    have found := allocation_lookup _ _ _ _ allocation
    simp [formObject, liveAllocation, arrayMemory, found, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms ObjectAllocationEffect.object_valid

/-- Object creation retains every pre-existing byte, authority and allocation descriptor. -/
theorem ObjectAllocationEffect.below {memory result : Memory} {type : RuntimeType}
    {object : Reference}
    (effect : ObjectAllocationEffect memory type object result) :
    MemoryBelow memory.nextIdentity memory result := by
  cases effect with
  | fresh _ allocation =>
    have before := allocate_preserves_memory_below _ _ _ _ allocation
    have fresh := (allocation_identity_fresh _ _ _ _ allocation).1
    refine before.trans ⟨fun _ _ => rfl, ?_, ?_, fun _ _ _ => rfl⟩
    · intro identity old offset
      simp only [arrayMemory, fresh, beq_iff_eq, Nat.ne_of_lt old, ite_false]
    · intro identity old offset writing
      simp [arrayMemory, permitted, viewContains, fresh, Ne.symm (Nat.ne_of_lt old)]

#print axioms ObjectAllocationEffect.below

/-- Object creation never changes the static field registry. -/
theorem ObjectAllocationEffect.registry {memory result : Memory} {type : RuntimeType}
    {object : Reference}
    (effect : ObjectAllocationEffect memory type object result) :
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
    | some allocation => exact absurd (formed.allocations _ _ found).1 (Nat.lt_irrefl _)
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

/-- A successful `newarr` of a class is an allocation of an instance of its array type. -/
theorem newReferenceArray_allocation {memory result : Memory} {element : CIL.Extraction.TypeExpr}
    {length : CIL.Value} {array : Reference}
    (success : newReferenceArray memory element length = .ok (array, result)) :
    ∃ size, allocateObject memory (referenceArrayType element) size = .ok (array, result) := by
  unfold newReferenceArray at success
  cases length <;> simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  all_goals try cases success
  all_goals repeat' split at success
  all_goals first | cases success | exact ⟨_, success⟩

#print axioms newReferenceArray_allocation

/-- `newarr` of a decodable, supported `length` of class references allocates an object of the
    array type with one slot per element; the allocation alone decides success. -/
theorem newReferenceArray_decoded (memory : Memory) (element : CIL.Extraction.TypeExpr)
    {value : CIL.Value} {length : Nat}
    (decoded : value = .i32 (BitVec.ofNat 32 length) ∨ value = .i64 (BitVec.ofNat 64 length))
    (small : length < 2^31) (bounded : length ≤ maxArrayLength) :
    newReferenceArray memory element value =
      allocateObject memory (referenceArrayType element) (objectFieldSlot * length) := by
  have toNat32 : (BitVec.ofNat 32 length).toNat = length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have toNat64 : (BitVec.ofNat 64 length).toNat = length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have toInt32 : (BitVec.ofNat 32 length).toInt = length := by
    rw [BitVec.toInt_eq_toNat_cond, toNat32]; split <;> omega
  have toInt64 : (BitVec.ofNat 64 length).toInt = length := by
    rw [BitVec.toInt_eq_toNat_cond, toNat64]; split <;> omega
  have within : ¬ maxArrayLength < length := Nat.not_lt.mpr bounded
  rcases decoded with rfl | rfl <;>
    simp only [newReferenceArray, toInt32, toInt64, Bind.bind, Except.bind, Pure.pure,
      Except.pure, Int.toNat_natCast, Int.natCast_nonneg, Int.not_lt.mpr, within,
      ite_false, gt_iff_lt]

#print axioms newReferenceArray_decoded

/-- In well-formed memory with budget for it, `newarr` of `length` class references allocates a
    fresh array at the next identity, all of whose slots hold null. -/
theorem newReferenceArray_ok {memory : Memory} (formed : memory.WellFormed)
    (element : CIL.Extraction.TypeExpr) {value : CIL.Value} {length : Nat}
    (decoded : value = .i32 (BitVec.ofNat 32 length) ∨ value = .i64 (BitVec.ofNat 64 length))
    (small : length < 2^31) (bounded : length ≤ maxArrayLength)
    (affordable : objectFieldSlot * length ≤ memory.heapBudget) :
    newReferenceArray memory element value =
      .ok (⟨memory.nextIdentity, 0⟩,
        objectMemory memory (referenceArrayType element) (objectFieldSlot * length)) := by
  have native : objectFieldSlot * length < nativeLimit := by
    simp only [objectFieldSlot, nativeLimit]; omega
  rw [newReferenceArray_decoded memory element decoded small bounded]
  exact allocateObject_ok formed _ affordable native

#print axioms newReferenceArray_ok

/-- Without budget for its slots, `newarr` of `length` class references fails with the model's
    `allocationFailure`, which is not a CLR exception. -/
theorem newReferenceArray_insufficient (memory : Memory) (element : CIL.Extraction.TypeExpr)
    {value : CIL.Value} {length : Nat}
    (decoded : value = .i32 (BitVec.ofNat 32 length) ∨ value = .i64 (BitVec.ofNat 64 length))
    (small : length < 2^31) (bounded : length ≤ maxArrayLength)
    (short : memory.heapBudget < objectFieldSlot * length) :
    newReferenceArray memory element value =
      .error (.allocationFailure (objectFieldSlot * length) memory.heapBudget) := by
  rw [newReferenceArray_decoded memory element decoded small bounded]
  exact allocateObject_insufficient _ short

#print axioms newReferenceArray_insufficient

/-- `newarr` of a class with a negative length throws `OverflowException` before allocating. -/
theorem newReferenceArray_negative (memory : Memory) (element : CIL.Extraction.TypeExpr)
    (bits : BitVec 32) (negative : bits.toInt < 0) :
    newReferenceArray memory element (.i32 bits) =
      .error (.thrown "System.OverflowException") := by
  simp [newReferenceArray, negative, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms newReferenceArray_negative

end CIL.Safety
