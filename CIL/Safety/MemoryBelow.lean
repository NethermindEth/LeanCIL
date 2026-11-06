import CIL.Safety.AllocationExtension

/-!
# Memory below a watermark

`MemoryBelow w before after` says every allocation with identity below `w` looks exactly the
same after an operation: metadata, bytes, authority and field references. Allocating fresh storage and writing
into allocations at or above the watermark preserve it, so a caller's memory survives what a
callee does to its own fresh frame.
-/

namespace CIL.Safety

/-- Exact preservation of earlier allocation metadata, byte values, initialization, both
    read/write authorities and the references fields hold. -/
structure MemoryBelow (watermark : Nat) (before after : Memory) : Prop where
  allocations : ∀ id, id < watermark → after.allocations id = before.allocations id
  cells : ∀ id, id < watermark → ∀ offset, after.cells id offset = before.cells id offset
  permissions : ∀ id, id < watermark → ∀ offset writing,
    permitted after writing ⟨id, offset⟩ = permitted before writing ⟨id, offset⟩
  slots : ∀ id, id < watermark → ∀ offset, after.slots id offset = before.slots id offset

/-- Exact preservation of earlier allocation metadata, bytes and authority, leaving the
    references fields hold uncompared: two executions that allocate different private storage
    can give the same fresh object different identities. -/
structure BytesBelow (watermark : Nat) (before after : Memory) : Prop where
  allocations : ∀ id, id < watermark → after.allocations id = before.allocations id
  cells : ∀ id, id < watermark → ∀ offset, after.cells id offset = before.cells id offset
  permissions : ∀ id, id < watermark → ∀ offset writing,
    permitted after writing ⟨id, offset⟩ = permitted before writing ⟨id, offset⟩

/-- The metadata, bytes and authority part of `MemoryBelow`. -/
theorem MemoryBelow.bytes {watermark : Nat} {before after : Memory}
    (preserved : MemoryBelow watermark before after) : BytesBelow watermark before after :=
  ⟨preserved.allocations, preserved.cells, preserved.permissions⟩
#print axioms MemoryBelow.bytes

theorem BytesBelow.trans {watermark : Nat} {first middle last : Memory}
    (left : BytesBelow watermark first middle) (right : BytesBelow watermark middle last) :
    BytesBelow watermark first last :=
  ⟨fun id bound => (right.allocations id bound).trans (left.allocations id bound),
    fun id bound offset => (right.cells id bound offset).trans (left.cells id bound offset),
    fun id bound offset writing => (right.permissions id bound offset writing).trans
      (left.permissions id bound offset writing)⟩
#print axioms BytesBelow.trans

theorem MemoryBelow.refl (watermark : Nat) (m : Memory) : MemoryBelow watermark m m :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem MemoryBelow.trans {watermark : Nat} {first middle last : Memory}
    (left : MemoryBelow watermark first middle) (right : MemoryBelow watermark middle last) :
    MemoryBelow watermark first last :=
  ⟨fun id bound => (right.allocations id bound).trans (left.allocations id bound),
    fun id bound offset => (right.cells id bound offset).trans (left.cells id bound offset),
    fun id bound offset writing => (right.permissions id bound offset writing).trans
      (left.permissions id bound offset writing),
    fun id bound offset => (right.slots id bound offset).trans (left.slots id bound offset)⟩

theorem MemoryBelow.weaken {lower upper : Nat} {before after : Memory}
    (preserved : MemoryBelow upper before after) (bound : lower ≤ upper) :
    MemoryBelow lower before after :=
  ⟨fun id old => preserved.allocations id (Nat.lt_of_lt_of_le old bound),
    fun id old => preserved.cells id (Nat.lt_of_lt_of_le old bound),
    fun id old => preserved.permissions id (Nat.lt_of_lt_of_le old bound),
    fun id old => preserved.slots id (Nat.lt_of_lt_of_le old bound)⟩

/-- Consecutive calls compose: each keeps the memory below its own entry watermark, and the
    first does not lower the watermark, so together they keep everything below the first's. -/
theorem MemoryBelow.compose {first middle last : Memory}
    (left : MemoryBelow first.nextIdentity first middle)
    (right : MemoryBelow middle.nextIdentity middle last)
    (grows : first.nextIdentity ≤ middle.nextIdentity) :
    MemoryBelow first.nextIdentity first last :=
  left.trans (right.weaken grows)

theorem MemoryBelow.access {watermark : Nat} {m result : Memory}
    (preserved : MemoryBelow watermark m result) (r : Reference) (old : r.allocation < watermark)
    (width alignment : Nat) (writing : Bool) :
    access result r width alignment writing = access m r width alignment writing := by
  simp only [CIL.Safety.access, form, liveAllocation, preserved.allocations _ old]
  simp only [preserved.permissions _ old]

/-- Access checks below the watermark agree where metadata and authority agree. -/
theorem BytesBelow.access {watermark : Nat} {m result : Memory}
    (preserved : BytesBelow watermark m result) (r : Reference) (old : r.allocation < watermark)
    (width alignment : Nat) (writing : Bool) :
    access result r width alignment writing = access m r width alignment writing := by
  simp only [CIL.Safety.access, form, liveAllocation, preserved.allocations _ old]
  simp only [preserved.permissions _ old]
#print axioms BytesBelow.access

theorem MemoryBelow.read {watermark : Nat} {m result : Memory}
    (preserved : MemoryBelow watermark m result) (r : Reference) (old : r.allocation < watermark)
    (width alignment : Nat) : read result r width alignment = read m r width alignment := by
  simp only [CIL.Safety.read, preserved.access r old, preserved.cells _ old]

/-- Allocation leaves every existing allocation untouched. -/
theorem allocate_preserves_memory_below (m result : Memory) (a : Allocation) (id : AllocationId)
    (h : allocate m a = .ok (id, result)) : MemoryBelow m.nextIdentity m result := by
  simp only [allocate] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro other bound
        simp [Nat.ne_of_lt bound]
      · intro other bound offset
        simp [Nat.ne_of_lt bound]
      · intro other bound offset writing
        rfl
      · intro other bound offset
        simp [Nat.ne_of_lt bound]

theorem prepend_view_preserves_memory_below (m : Memory) (view : View) (watermark : Nat)
    (fresh : watermark ≤ view.allocation) :
    MemoryBelow watermark m { m with views := view :: m.views } := by
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, ?_, fun _ _ _ => rfl⟩
  intro id old offset writing
  have different : id ≠ view.allocation := Nat.ne_of_lt (Nat.lt_of_lt_of_le old fresh)
  simp [permitted, viewContains, Ne.symm different]

/-- A write into an allocation at or above the watermark leaves everything below it
    untouched. -/
theorem write_preserves_memory_below (m result : Memory) (r : Reference) (bytes : List (BitVec 8))
    (alignment watermark : Nat) (fresh : watermark ≤ r.allocation)
    (h : write m r bytes alignment = .ok result) : MemoryBelow watermark m result := by
  unfold write at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    refine ⟨fun _ _ => rfl, ?_, ?_, fun _ _ _ => rfl⟩
    · intro id old offset
      have different : id ≠ r.allocation := Nat.ne_of_lt (Nat.lt_of_lt_of_le old fresh)
      simp [different]
    · intro id old offset writing
      have different : id ≠ r.allocation := Nat.ne_of_lt (Nat.lt_of_lt_of_le old fresh)
      change permitted { m with views := writeViews m r bytes.length } writing ⟨id, offset⟩ = _
      rw [writeViews_permitted]
      simp [permitted, viewContains, Ne.symm different]

#print axioms MemoryBelow.compose
#print axioms MemoryBelow.read
#print axioms allocate_preserves_memory_below
#print axioms write_preserves_memory_below

end CIL.Safety
