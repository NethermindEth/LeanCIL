import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts
import CIL.Safety.ObjectFields
import CIL.Safety.LoopScaffold
import CIL.Safety.Forwarders

/-!
# Renting from an object pool

`ItemPool.Rent()` pops the head of the pool's intrusive free list, or creates a new item while
fewer than `Capacity` are alive, and throws `InvalidOperationException` when every item is
rented out.
-/

open CIL.Safety
open CIL (W32)
open Extracted.Classes
namespace ExampleProof

bind_method rent rentBody := "Examples.PooledItem Examples.ItemPool::Rent()"

bind_entry entry (memory : Memory) (pool : ManagedReference) (wellFormed : memory.WellFormed) :=
  rentBody with [.object pool] from memory allocating wellFormed

/-- Storing a reference that forms, null included, into an owned reference field succeeds,
    confined to the field, and leaves it owned and holding that reference. -/
theorem storeFormed {field : ReferenceField} {memory : Memory} {object : Reference}
    {value : ManagedReference} (owned : field.Owned memory object)
    (formed : formObject memory value = .ok (.object value)) :
    storeSlot memory (field.address object) value =
        .ok (setSlot memory (field.address object) value) ∧
      Confined [field.entry object] memory (setSlot memory (field.address object) value) ∧
      field.Holds (setSlot memory (field.address object) value) object value :=
  ⟨storeSlot_of_access owned.writable formed,
    Confined.setSlot _ (List.mem_singleton_self _) (by decide),
    ⟨{ located := by rw [objectFieldAddress_setSlot]; exact owned.located
       old := owned.old
       readable := owned.readable
       writable := owned.writable }, setSlot_slots_same _ _ _⟩⟩

#print axioms storeFormed

/-- What an item's `NextFree` holds is null or a live item, as in every free list. -/
def Links (memory : Memory) (item : Reference) : Prop :=
  PooledItem.NextFree.of memory item = .null ∨
    ∃ next, PooledItem.NextFree.of memory item = .address next ∧ LiveObject memory next

/-- The reference an item links to still forms in memory that keeps every older allocation. -/
theorem Links.formed {memory after : Memory} {item : Reference} (links : Links memory item)
    (preserved : MemoryBelow memory.nextIdentity memory after)
    (grows : memory.nextIdentity ≤ after.nextIdentity) :
    formObject after (PooledItem.NextFree.of memory item) =
      .ok (.object (PooledItem.NextFree.of memory item)) := by
  rcases links with empty | ⟨next, held, live⟩
  · rw [empty]; rfl
  · rw [held]; exact (live.after_below preserved live.old grows).formed

#print axioms Links.formed

/-- The fields `Rent` may write when it reuses `head`: the free list, the idle count, and the
    head's link and rented flag. -/
def reuseFootprint (pool head : Reference) : List (Reference × Nat) :=
  [ItemPool._free.entry pool, PooledItem.NextFree.entry head, ItemPool._freeCount.entry pool,
    PooledItem.IsRented.entry head]

/-- With a nonempty free list, `Rent` returns its head, advances the free list to what the head
    linked to, unlinks the head, counts one fewer idle item and marks the head rented, and writes
    nothing else the caller holds. -/
theorem rent_reuses (memory : Memory) (pool head : Reference) (wellFormed : memory.WellFormed)
    (free : ItemPool._free.Owned memory pool)
    (heldFree : ItemPool._free.of memory pool = .address head)
    (idle : ItemPool._freeCount.Owned memory pool)
    (link : PooledItem.NextFree.Owned memory head) (links : Links memory head)
    (rented : PooledItem.IsRented.Owned memory head) :
    ∃ fuel final, invoke Extracted.program fuel rent [.object (.address pool)] memory =
        .ok (final, [.object (.address head)]) ∧
      Confined (reuseFootprint pool head) memory final ∧
      ItemPool._free.Holds final pool (PooledItem.NextFree.of memory head) ∧
      PooledItem.NextFree.Holds final head .null ∧
      ItemPool._freeCount.Holds final pool (ItemPool._freeCount.of memory pool - 1) ∧
      PooledItem.IsRented.Holds final head 1 := by
  obtain ⟨home, entered, setup, fresh, entryMemory, -⟩ :=
    entry.checked memory (.address pool) wellFormed
  have keep := entryMemory.kept
  have grown := entryMemory.grown
  -- Frame entry allocates only the frame's own home, so every caller fact carries into it.
  have free0 := free.holds.after_below keep free.old grown
  have idle0 := idle.holds.after_below keep idle.old grown
  have link0 := link.holds.after_below keep link.old grown
  have rented0 := rented.after_below keep rented.old grown
  have headLive := link0.1.live
  have headLoad := free0.1.toReadable.load_live (free0.2.trans heldFree) headLive
  have linkFormed := links.formed keep grown
  have linkLoad := link0.1.toReadable.load.trans (link0.2 ▸ linkFormed)
  rw [link0.2] at linkLoad
  obtain ⟨freeStored, freeFramed, freeHeld⟩ := storeFormed free0.1 linkFormed
  have link1 := link0.1.after_confined freeFramed (apart_of_entries rfl)
  obtain ⟨nullStored, nullFramed, nullHeld⟩ := storeFormed link1 (value := .null) rfl
  have idle2 := ((idle0.after_confined freeFramed (apart_of_entries rfl)).after_confined nullFramed
    (apart_of_entries rfl))
  obtain ⟨counted, countWritten, countFramed, countHeld⟩ :=
    idle2.1.store (ItemPool._freeCount.of memory pool - 1)
  have idleFacts := idle2.2 ▸ idle2.1.facts
  have rented3 := ((rented0.after_confined freeFramed (apart_of_entries rfl)).after_confined
    nullFramed (apart_of_entries rfl)).after_confined countFramed
    (apart_of_entries rfl)
  obtain ⟨marked, markWritten, markFramed, markHeld⟩ := rented3.store 1
  -- Leaving the frame expires only its home, which is younger than every caller object.
  have left := leaveFrame_preserves_memory_below (entry.frame memory home) marked
    memory.nextIdentity (by simpa [entry.frame] using fresh.fresh)
  have changed : Confined (reuseFootprint pool head) memory
      (leaveFrame (entry.frame memory home) marked) :=
    ((((Confined.ofMemoryBelow keep (Nat.le_refl _) grown).trans
      (freeFramed.widen (by simp [reuseFootprint]))).trans
      (nullFramed.widen (by simp [reuseFootprint]))).trans
      (countFramed.widen (by simp [reuseFootprint]))).trans
      (markFramed.widen (by simp [reuseFootprint])) |>.then_below left
      (Nat.le_of_eq (leaveFrame_nextIdentity _ _).symm)
  have past : memory.nextIdentity ≤ (leaveFrame (entry.frame memory home) marked).nextIdentity :=
    changed.grows
  refine ⟨CIL.executionBound Extracted.program rent, _, ?_, changed, ?_, ?_, ?_, ?_⟩
  · cil_checked_steps [setup, entry.frame, free.live.formed, free0.1.live.formed, free0.1.located,
      headLoad, headLive.formed, link0.1.located, linkLoad, freeStored,
      link1.live.formed, link1.located, nullStored, idleFacts, countWritten, rented3.live.formed, rented3.located, markWritten]
    cil_checked_steps 1 [rented3.live.formed, rented3.located, markWritten]
    have headMarked := rented3.live.after_confined markFramed
    have headLeft := (headMarked.after_below left link.old past).formed
    cil_checked_steps 1 [headMarked.formed]
    change run Extracted.program 42 rent 49 _ (entry.frame memory home) _ marked = _
    exact run_return (fuel := 41) rent.found (by rfl)
      (step_return_unchanged rfl rfl
        (by simp [checkedValue, headMarked.formed, List.mapM_cons, List.mapM_nil, Bind.bind,
          Except.bind, Pure.pure, Except.pure]) (by simp [ReturnsUnchanged]))
      (by simp [checkedValue, headLeft, List.mapM_cons, List.mapM_nil, Bind.bind, Except.bind,
        Pure.pure, Except.pure])
  · exact (((freeHeld.after_confined nullFramed (apart_of_entries rfl)).after_confined countFramed
      (apart_of_entries rfl)).after_confined markFramed (apart_of_entries rfl)).after_below left
      free.old past
  · exact ((nullHeld.after_confined countFramed (apart_of_entries rfl)).after_confined markFramed
      (apart_of_entries rfl)).after_below left link.old past
  · exact (countHeld.after_confined markFramed (apart_of_entries rfl)).after_below left
      idle.old past
  · exact markHeld.after_below left rented.old past

#print axioms rent_reuses

/-- With an empty free list and every item the capacity allows alive, `Rent` throws
    `InvalidOperationException` at its `throw`, pc 12, before writing anything. -/
theorem rent_exhausted_throws (memory : Memory) (pool : Reference)
    (wellFormed : memory.WellFormed)
    (free : ItemPool._free.Readable memory pool) (empty : ItemPool._free.of memory pool = .null)
    (live : ItemPool._live.Readable memory pool)
    (capacity : ItemPool._capacity.Readable memory pool)
    (full : ItemPool._live.of memory pool = ItemPool._capacity.of memory pool) :
    ∃ fuel, invoke Extracted.program fuel rent [.object (.address pool)] memory =
      .error ⟨rent, 12, .thrown "System.InvalidOperationException"⟩ := by
  obtain ⟨home, entered, setup, -, entryMemory, -⟩ :=
    entry.checked memory (.address pool) wellFormed
  have keep := entryMemory.kept
  have grown := entryMemory.grown
  have free0 := free.below keep free.old grown
  have live0 := live.below keep live.old grown
  have capacity0 := capacity.below keep capacity.old grown
  have emptyLoad := free0.1.load_null (free0.2.trans empty)
  have liveFacts := live0.2 ▸ live0.1.facts
  have capacityFacts := capacity0.2 ▸ capacity0.1.facts
  refine ⟨CIL.executionBound Extracted.program rent, ?_⟩
  cil_checked_steps [setup, entry.frame, free.live.formed, free0.1.live.formed, free0.1.located,
    emptyLoad, liveFacts, capacityFacts, full]

#print axioms rent_exhausted_throws

/-- Renting from a null pool throws `NullReferenceException` at the first field load, pc 1. -/
theorem rent_null_pool_throws (memory : Memory) (wellFormed : memory.WellFormed) :
    ∃ fuel, invoke Extracted.program fuel rent [.object .null] memory =
      .error ⟨rent, 1, .thrown "System.NullReferenceException"⟩ := by
  obtain ⟨home, entered, setup, rest⟩ := entry.checked memory .null wellFormed
  refine ⟨CIL.executionBound Extracted.program rent, ?_⟩
  cil_checked_steps [setup]

#print axioms rent_null_pool_throws

/-- The reuse path, the exhausted pool and the null pool, audited as one theorem. -/
theorem correctness : type_of% @rent_reuses ∧ type_of% @rent_exhausted_throws ∧
    type_of% @rent_null_pool_throws :=
  ⟨rent_reuses, rent_exhausted_throws, rent_null_pool_throws⟩

#print axioms correctness

end ExampleProof
