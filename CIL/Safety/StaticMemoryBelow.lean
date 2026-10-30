import CIL.Safety.MemoryBelow
import CIL.Safety.StaticMemoryLemmas

/-!
# Static resolution keeps older memory

Resolving a readonly static either returns a cached binding unchanged or allocates fresh
storage, so `MemoryBelow` holds at the memory's next identity. Callers use this to carry
facts about existing allocations across a static load.
-/

namespace CIL.Safety

/-- Resolving a readonly static field may allocate its storage, but cannot
    change any earlier caller or private allocation, bytes or permissions. -/
theorem staticReference_preserves_memory_below (descriptor : CIL.StaticDescriptor)
    (memory result : Memory) (reference : Reference)
    (resolved : staticReference descriptor memory = .ok (result, reference)) :
    MemoryBelow memory.nextIdentity memory result := by
  cases cache : memory.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨key, cached⟩ := binding
    obtain ⟨rfl, _, _⟩ := cached_static_reference_checked _ _ _ _ _ _ cache resolved
    exact .refl _ _
  | none =>
    simp only [staticReference, cache] at resolved
    cases allocated : allocate memory ⟨.immutableStatic,
        ⟨descriptor.bytes.length, descriptor.alignment, []⟩, true, [descriptor.bytes.length]⟩ <;>
      simp only [allocated, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at resolved
    · cases resolved
    · rename_i pair
      obtain ⟨id, middle⟩ := pair
      cases resolved
      have retained := allocate_preserves_memory_below _ _ _ _ allocated
      have fresh := (allocation_identity_fresh _ _ _ _ allocated).1
      refine ⟨retained.allocations, ?_, ?_⟩
      · intro other old offset
        have different : other ≠ id := by rw [fresh]; exact Nat.ne_of_lt old
        simpa [different] using retained.cells other old offset
      · intro other old offset writing
        have different : other ≠ id := by rw [fresh]; exact Nat.ne_of_lt old
        simpa [permitted, viewContains, Ne.symm different] using
          retained.permissions other old offset writing

#print axioms staticReference_preserves_memory_below
end CIL.Safety
