import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts
import CIL.Safety.ObjectFields
import CIL.Safety.ClassCatalog
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
  obtain ⟨home, entered, enter⟩ :=
    entry.checked memory (.address pool) wellFormed
  have keep := enter.entryMemory.kept
  have grown := enter.entryMemory.grown
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
  obtain ⟨freeStored, freeFramed, freeHeld⟩ := free0.1.store_formed linkFormed
  have link1 := link0.1.after_confined freeFramed (apart_of_entries rfl)
  obtain ⟨nullStored, nullFramed, nullHeld⟩ := link1.store_formed (value := .null) rfl
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
    memory.nextIdentity (by simpa [entry.frame] using enter.numeric1.fresh)
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
  · have headMarked := rented3.live.after_confined markFramed
    -- The returned head is older than the frame's home, so leaving the frame keeps it.
    have headKept : head.allocation ≠ home.allocation :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le link.old enter.numeric1.fresh)
    cil_checked_steps [enter.setup, entry.frame, headLoad, linkLoad, freeStored, nullStored,
      idleFacts, countWritten, markWritten, headKept]
    rfl
  · exact (((freeHeld.after_confined nullFramed (apart_of_entries rfl)).after_confined countFramed
      (apart_of_entries rfl)).after_confined markFramed (apart_of_entries rfl)).after_below left
      free.old past
  · exact ((nullHeld.after_confined countFramed (apart_of_entries rfl)).after_confined markFramed
      (apart_of_entries rfl)).after_below left link.old past
  · exact (countHeld.after_confined markFramed (apart_of_entries rfl)).after_below left
      idle.old past
  · exact markHeld.after_below left rented.old past

#print axioms rent_reuses

/-- The classes the extraction's methods declare, with their admitted bases: `ItemPool` and
    `PooledItem`, each deriving from `System.Object` directly. -/
abbrev poolClasses : List RuntimeType := declaredClasses Extracted.methodEvidence

/-- In memory whose objects agree with the extraction's classes, a pool and an item are different
    objects, though the item's rented flag and the pool's live count share an offset. -/
theorem pool_ne_item {memory : Memory} (consistent : memory.ClassesConsistent poolClasses)
    {pool item : Reference} (live : ItemPool._live.Readable memory pool)
    (rented : PooledItem.IsRented.Readable memory item) : pool.allocation ≠ item.allocation :=
  consistent.allocation_ne (first := ⟨ItemPool.type, []⟩) (second := ⟨PooledItem.type, []⟩)
    (by decide +kernel) (by decide +kernel) (by decide) live.located rented.located

#print axioms pool_ne_item

/-- Every `newobj` of the extraction creates an instance whose base chain agrees with the
    extraction's classes. -/
theorem pool_sites : ObjectSitesConsistent poolClasses Extracted.program := by decide +kernel

#print axioms pool_sites

/-- A caller that establishes agreement with the extraction's classes once, at entry, keeps it
    across any invocation of the program, whichever objects it creates. -/
theorem invoke_keeps_classes {fuel method : Nat} {args values : List Value}
    {memory final : Memory} (consistent : memory.ClassesConsistent poolClasses)
    (invoked : invoke Extracted.program fuel method args memory = .ok (final, values)) :
    final.ClassesConsistent poolClasses :=
  invoke_preserves_classes pool_sites consistent invoked

#print axioms invoke_keeps_classes

/-- Reusing an item leaves the pool's live count as it was, in memory whose objects agree with
    the extraction's classes. -/
theorem rent_reuses_keeps_live (memory : Memory) (pool head : Reference)
    (wellFormed : memory.WellFormed) (consistent : memory.ClassesConsistent poolClasses)
    (free : ItemPool._free.Owned memory pool)
    (heldFree : ItemPool._free.of memory pool = .address head)
    (idle : ItemPool._freeCount.Owned memory pool)
    (link : PooledItem.NextFree.Owned memory head) (links : Links memory head)
    (rented : PooledItem.IsRented.Owned memory head)
    (live : ItemPool._live.Readable memory pool) :
    ∃ fuel final, invoke Extracted.program fuel rent [.object (.address pool)] memory =
        .ok (final, [.object (.address head)]) ∧
      ItemPool._live.Readable final pool ∧
      ItemPool._live.of final pool = ItemPool._live.of memory pool := by
  obtain ⟨fuel, final, ran, changed, -⟩ :=
    rent_reuses memory pool head wellFormed free heldFree idle link links rented
  have distinct := pool_ne_item consistent live rented.toReadable
  refine ⟨fuel, final, ran, live.frame changed fun entry member => ?_⟩
  simp only [reuseFootprint, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    first
      | exact Or.inl distinct
      | exact apart_of_entries (footprint := [_]) rfl _ (List.mem_singleton_self _)

#print axioms rent_reuses_keeps_live

/-- The runtime type of a `PooledItem`, which derives from `System.Object` directly. -/
abbrev itemType : RuntimeType := ⟨PooledItem.type, []⟩

/-- The model size of a `PooledItem`: one 8-byte slot for each of its five fields. -/
abbrev itemSize : Nat := 40
/-- The pool fields `Rent` may write when it creates an item: the id counter and the live count. -/
def createFootprint (pool : Reference) : List (Reference × Nat) :=
  [ItemPool._nextId.entry pool, ItemPool._live.entry pool]

/-- The fields of a new item that its constructor and `Rent` write. -/
def itemFootprint (item : Reference) : List (Reference × Nat) :=
  [PooledItem.Owner.entry item, PooledItem.Id.entry item, PooledItem.IsRented.entry item]

/-- With an empty free list and fewer items alive than the capacity allows, Rent creates an item
    above everything the caller holds, owned by the pool, numbered with the pool's next id,
    unlinked and marked rented; it advances the id counter and the live count and writes nothing
    else the caller holds. -/
theorem rent_creates (memory : Memory) (pool : Reference) (wellFormed : memory.WellFormed)
    (free : ItemPool._free.Readable memory pool) (empty : ItemPool._free.of memory pool = .null)
    (live : ItemPool._live.Owned memory pool)
    (capacity : ItemPool._capacity.Readable memory pool)
    (room : ItemPool._live.of memory pool ≠ ItemPool._capacity.of memory pool)
    (nextId : ItemPool._nextId.Owned memory pool)
    (budget : itemSize ≤ memory.heapBudget) :
    ∃ fuel final item, invoke Extracted.program fuel rent [.object (.address pool)] memory =
        .ok (final, [.object (.address item)]) ∧
      memory.nextIdentity ≤ item.allocation ∧
      Confined (createFootprint pool) memory final ∧
      ItemPool._nextId.Holds final pool (ItemPool._nextId.of memory pool + 1) ∧
      ItemPool._live.Holds final pool (ItemPool._live.of memory pool + 1) ∧
      PooledItem.Owner.Holds final item (.address pool) ∧
      PooledItem.Id.Holds final item (ItemPool._nextId.of memory pool) ∧
      PooledItem.NextFree.Holds final item .null ∧
      PooledItem.IsRented.Holds final item 1 := by
  obtain ⟨home, entered, enter⟩ :=
    entry.checked memory (.address pool) wellFormed
  have keep := enter.entryMemory.kept
  have grown := enter.entryMemory.grown
  have free0 := free.below keep free.old grown
  have live0 := live.holds.after_below keep live.old grown
  have capacity0 := capacity.below keep capacity.old grown
  have nextId0 := nextId.holds.after_below keep nextId.old grown
  have emptyLoad := free0.1.load_null (free0.2.trans empty)
  have liveFacts := live0.2 ▸ live0.1.facts
  have capacityFacts := capacity0.2 ▸ capacity0.1.facts
  have nextIdFacts := nextId0.2 ▸ nextId0.1.facts
  -- `Rent` keeps the old id in its numeric local, whose home the frame owns.
  obtain ⟨counter, idWritten, idStored, idRead⟩ := store_numeric_local .word32
    (.i32 (ItemPool._nextId.of memory pool)) (ItemPool._nextId.of memory pool).toNat
    (by simp [localNumber, CIL.Value.hasUnspecified]) enter.numeric1.writable
  have idLoaded := load_numeric_local .word32 (.i32 (ItemPool._nextId.of memory pool)) _
    (by simp [localNumber, CIL.Value.hasUnspecified]) idRead
  have counterBelow := write_preserves_memory_below _ _ _ _ _ _ enter.numeric1.fresh idWritten
  have counterNext := write_nextIdentity idWritten
  have nextId1 := nextId0.after_below counterBelow nextId.old (by omega)
  obtain ⟨numbered, nextWritten, nextFramed, nextHeld⟩ :=
    nextId1.1.store (ItemPool._nextId.of memory pool + 1)
  have numberedNext : numbered.nextIdentity = entered.nextIdentity :=
    (write_nextIdentity nextWritten).trans counterNext
  have homeApart : home.allocation ≠ pool.allocation :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le nextId.old enter.numeric1.fresh)
  have idRead2 := write_preserves_disjoint_read nextWritten idRead (Or.inl homeApart)
  have idLoaded2 := load_numeric_local .word32 (.i32 (ItemPool._nextId.of memory pool)) _
    (by simp [localNumber, CIL.Value.hasUnspecified]) idRead2
  have numberedFormed : numbered.WellFormed :=
    write_preserves_wellFormed _ _ _ _ _
      (write_preserves_wellFormed _ _ _ _ _ enter.entryMemory.wellFormed idWritten) nextWritten
  have numberedBudget : itemSize ≤ numbered.heapBudget := by
    rw [write_heapBudget nextWritten, write_heapBudget idWritten, enterFrame_heapBudget enter.setup]
    exact budget
  -- `newobj` creates the item above everything the caller and the frame hold.
  have allocated := allocateObject_ok numberedFormed itemType numberedBudget
    (by decide)
  have created := objectMemory_formObject numbered itemType itemSize
  have poolKept := (allocateObject_effect allocated).below
  have allocatedNext : numbered.nextIdentity ≤
      (objectMemory numbered itemType itemSize).nextIdentity := by
    simp [objectMemory]
  have poolLive3 := nextHeld.1.live.after_below poolKept nextHeld.1.old allocatedNext
  have declared : PooledItem.type ∈ itemType.lineage :=
    RuntimeType.identity_mem_lineage _
  have ownerFresh := ReferenceField.fresh_holds_null (field := PooledItem.Owner)
    (size := itemSize) numbered itemType declared (by decide) (by decide)
  obtain ⟨ownerStored, ownerFramed, ownerHeld⟩ := ownerFresh.1.store_formed poolLive3.formed
  have idOwned := (WordField.fresh_owned (field := PooledItem.Id) (size := itemSize) numbered
    itemType declared (by decide) (by decide) (by decide)).after_confined ownerFramed
    (apart_of_entries rfl)
  obtain ⟨identified, itemIdWritten, itemIdFramed, itemIdHeld⟩ :=
    idOwned.store (ItemPool._nextId.of memory pool)
  -- The pool's live count is apart from every field written so far.
  have live5 := ((((live0.after_below counterBelow live.old (by omega)).after_confined nextFramed
    (apart_of_entries rfl)).after_below poolKept nextHeld.1.old allocatedNext).after_confined
    ownerFramed (apart_of_entries rfl)).after_confined itemIdFramed (apart_of_entries rfl)
  have liveFacts5 := live5.2 ▸ live5.1.facts
  obtain ⟨counted, liveWritten, liveFramed, liveHeld⟩ :=
    live5.1.store (ItemPool._live.of memory pool + 1)
  have itemApart : numbered.nextIdentity ≠ pool.allocation :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le nextHeld.1.old (Nat.le_refl _))
  have rentedOwned := ((((WordField.fresh_owned (field := PooledItem.IsRented) (size := itemSize)
    numbered itemType declared (by decide) (by decide) (by decide)).after_confined
    ownerFramed (apart_of_entries rfl)).after_confined itemIdFramed (apart_of_entries rfl))
    |>.after_confined liveFramed fun entry member => by
      simp only [List.mem_singleton] at member
      subst member
      exact Or.inl itemApart)
  obtain ⟨marked, markWritten, markFramed, markHeld⟩ := rentedOwned.store 1
  have itemHome : numbered.nextIdentity ≠ home.allocation :=
    Nat.ne_of_gt (by rw [numberedNext]; exact enter.numeric1.bounded)
  have itemKept : numbered.nextIdentity ∉ (entry.frame memory home).owned := by
    simpa [entry.frame] using itemHome
  have young : memory.nextIdentity ≤ numbered.nextIdentity := by omega
  -- Leaving the frame expires only its home and keeps the item, which the frame does not own.
  have left := leaveFrame_preserves_memory_below (entry.frame memory home) marked
    memory.nextIdentity (by simpa [entry.frame] using enter.numeric1.fresh)
  have itemLeft := leaveFrame_memoryAt (entry.frame memory home) marked itemKept
  have exited : marked.nextIdentity ≤ (leaveFrame (entry.frame memory home) marked).nextIdentity :=
    Nat.le_of_eq (leaveFrame_nextIdentity _ _).symm
  have itemApartEntry : ∀ {width : Nat} {offset : Nat}, ∀ entry ∈ [ItemPool._live.entry pool],
      Apart ⟨numbered.nextIdentity, offset⟩ width entry := fun entry member => by
    simp only [List.mem_singleton] at member
    subst member
    exact Or.inl itemApart
  have poolApartEntry : ∀ {width : Nat} {offset : Nat},
      ∀ entry ∈ [PooledItem.IsRented.entry ⟨numbered.nextIdentity, 0⟩],
      Apart ⟨pool.allocation, offset⟩ width entry := fun entry member => by
    simp only [List.mem_singleton] at member
    subst member
    exact Or.inl (Ne.symm itemApart)
  have changed : Confined (itemFootprint ⟨numbered.nextIdentity, 0⟩ ++ createFootprint pool)
      memory (leaveFrame (entry.frame memory home) marked) :=
    (((((((Confined.ofMemoryBelow keep (Nat.le_refl _) grown).then_below counterBelow
      (Nat.le_of_eq counterNext.symm)).trans
      (nextFramed.widen (by simp [createFootprint]))).then_below (poolKept.weaken young)
      allocatedNext).trans (ownerFramed.widen (by simp [itemFootprint]))).trans
      (itemIdFramed.widen (by simp [itemFootprint]))).trans
      (liveFramed.widen (by simp [createFootprint]))).trans
      (markFramed.widen (by simp [itemFootprint])) |>.after_leaveFrame
      (by simpa [entry.frame] using enter.numeric1.fresh)
  have past : memory.nextIdentity ≤
      (leaveFrame (entry.frame memory home) marked).nextIdentity := changed.grows
  refine ⟨CIL.executionBound Extracted.program rent, leaveFrame (entry.frame memory home) marked,
    ⟨numbered.nextIdentity, 0⟩, ?_, young,
    changed.forget_fresh fun entry member => by
      simp only [itemFootprint, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact young, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have itemMarked := rentedOwned.live.after_confined markFramed
    cil_checked_steps [enter.setup, entry.frame, emptyLoad, liveFacts, capacityFacts, room,
      nextIdFacts, idStored, idLoaded, nextWritten, idLoaded2, allocated, created, ownerStored,
      itemIdWritten, itemType, itemSize, PooledItem.type, liveFacts5, liveWritten, markWritten,
      itemHome]
    rfl
  · exact ((((nextHeld.after_below poolKept nextHeld.1.old allocatedNext).after_confined
      ownerFramed (apart_of_entries rfl)).after_confined itemIdFramed (apart_of_entries rfl))
      |>.after_confined liveFramed (apart_of_entries rfl)).after_confined markFramed
      (apart_of_entries rfl) |>.after_below left nextId.old past
  · exact (liveHeld.after_confined markFramed poolApartEntry).after_below left live.old past
  · exact (((ownerHeld.after_confined itemIdFramed (apart_of_entries rfl)).after_confined
      liveFramed itemApartEntry).after_confined markFramed (apart_of_entries rfl)).after_kept
      itemLeft exited
  · exact ((itemIdHeld.after_confined liveFramed itemApartEntry).after_confined markFramed
      (apart_of_entries rfl)).after_kept itemLeft exited
  · exact ((((ReferenceField.fresh_holds_null (field := PooledItem.NextFree) (size := itemSize)
      numbered itemType declared (by decide) (by decide)).after_confined
      ownerFramed (apart_of_entries rfl)).after_confined itemIdFramed (apart_of_entries rfl))
      |>.after_confined liveFramed itemApartEntry).after_confined markFramed
      (apart_of_entries rfl) |>.after_kept itemLeft exited
  · exact markHeld.after_kept itemLeft exited

#print axioms rent_creates

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
  obtain ⟨home, entered, enter⟩ :=
    entry.checked memory (.address pool) wellFormed
  have keep := enter.entryMemory.kept
  have grown := enter.entryMemory.grown
  have free0 := free.below keep free.old grown
  have live0 := live.below keep live.old grown
  have capacity0 := capacity.below keep capacity.old grown
  have emptyLoad := free0.1.load_null (free0.2.trans empty)
  have liveFacts := live0.2 ▸ live0.1.facts
  have capacityFacts := capacity0.2 ▸ capacity0.1.facts
  cil_checked_steps [enter.setup, entry.frame, emptyLoad, liveFacts, capacityFacts, full]

#print axioms rent_exhausted_throws

/-- Renting from a null pool throws `NullReferenceException` at the first field load, pc 1. -/
theorem rent_null_pool_throws (memory : Memory) (wellFormed : memory.WellFormed) :
    ∃ fuel, invoke Extracted.program fuel rent [.object .null] memory =
      .error ⟨rent, 1, .thrown "System.NullReferenceException"⟩ := by
  obtain ⟨home, entered, enter⟩ := entry.checked memory .null wellFormed
  cil_checked_steps [enter.setup]

#print axioms rent_null_pool_throws

/-- The reuse and creation paths, the live count a reuse keeps, the exhausted pool and the null
    pool, audited as one theorem. -/
theorem correctness : type_of% @rent_reuses ∧ type_of% @rent_reuses_keeps_live ∧
    type_of% @rent_creates ∧ type_of% @rent_exhausted_throws ∧ type_of% @rent_null_pool_throws :=
  ⟨rent_reuses, rent_reuses_keeps_live, rent_creates, rent_exhausted_throws,
    rent_null_pool_throws⟩

#print axioms correctness

end ExampleProof
