import Extracted
import CIL.Verification
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.ReferenceSegments
import CIL.Safety.LoopScaffold

/-!
# Searching an object pool's free list

`ItemPool.IsIdle(item)` walks the pool's intrusive free list from `_free` through each item's
`NextFree`, returning true at the first node that is `item` and false at the null that ends the
list. The loop's local holds an object reference, replaced at each hop. The caller states the
free list as a `Segment` to null visiting `nodes`; its length is the loop's measure, so the walk
terminates, and the answer is whether `item` is one of `nodes`.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

bind_method isIdle idleBody := "System.Boolean Examples.ItemPool::IsIdle(Examples.PooledItem)"

bind_entry entry (memory : Memory) (pool : Reference) (item : ManagedReference)
    (wellFormed : memory.WellFormed) :=
  idleBody with [.object (.address pool), .object item] from memory allocating wellFormed
bind_loop loop := idleBody

/-- The node the walk is at and the nodes from it to the end of the free list; the frame's only
    local holds the node. -/
private abbrev State (memory : Memory) :=
  FrameState [] memory [.object] (ManagedReference × List Reference)
    (fun values => [.object (some values.1)]) fun _ => [none]

/-- The loop test, with the node on the stack and in the local. -/
bind_cutpoint header (memory : Memory) (state : State memory) :=
  idleBody at loop.latch matching (fun op => op matches .brnonzero _) with
    { entry.frame memory with locals := [.object (some state.values.1)] },
    [.object state.values.1], state.memory

/-- Whether `item` is one of `nodes`. -/
def listed (item : ManagedReference) (nodes : List Reference) : Bool :=
  (nodes.map ManagedReference.address).contains item

/-- `IsIdle(item)` on a pool whose free list visits `nodes` and ends in null answers whether
    `item` is one of them, and writes nothing. `item` may be null or any live instance. -/
def idleContract : MethodContract (Reference × ManagedReference × List Reference) Bool where
  args := fun (pool, item, _) => [.object (.address pool), .object item]
  results idle := [.scalar (.i32 (if idle then 1 else 0))]
  pre := fun (pool, item, nodes) memory => memory.WellFormed ∧
    ItemPool._free.Readable memory pool ∧
    PooledItem.NextFree.Segment memory (ItemPool._free.of memory pool) .null nodes ∧
    ∀ object, item = .address object → LiveObject memory object
  footprint _ := []
  post := fun (_, item, nodes) _ _ idle => idle = listed item nodes

/-- `IsIdle` meets its contract: each hop shortens the rest of the free list by one node. -/
theorem idle_holds : idleContract.Holds Extracted.program isIdle := by
  rintro ⟨pool, item, nodes⟩ memory ⟨wellFormed, free, chain, present⟩
  obtain ⟨entered, enter⟩ := entry.checked memory pool item wellFormed
  have itemFormed : formObject memory item = .ok (.object item) := by
    cases item with
    | null => rfl
    | address object => exact (present object rfl).formed
  have enteredItem : formObject entered item = .ok (.object item) := by
    cases item with
    | null => rfl
    | address object =>
      have live := present object rfl
      exact (live.after_below enter.entryMemory.kept live.old enter.entryMemory.grown).formed
  -- Frame entry keeps the caller's memory, so the free list and its head carry over.
  have enteredFree := free.below enter.entryMemory.kept free.old enter.entryMemory.grown
  have enteredChain :=
    chain.after_below enter.entryMemory.kept (Nat.le_refl _) enter.entryMemory.grown
  rw [← enteredFree.2] at enteredChain
  obtain ⟨fuel, final, invoked, framed⟩ : ∃ fuel final,
      invoke Extracted.program fuel isIdle [.object (.address pool), .object item] memory =
        .ok (final, [.scalar (.i32 (if listed item nodes then 1 else 0))]) ∧
      Confined [] memory final := by
    refine invoke_loop_induction isIdle.found ?_ enter.setup (header memory)
      (fun state => state.memory = entered ∧
        PooledItem.NextFree.Segment entered state.values.1 .null state.values.2 ∧
        listed item state.values.2 = listed item nodes)
      (fun state => state.values.2.length) (fun start => ?_) ?_
    · cil_checked_side [free.live.formed, itemFormed]
    · cil_loop_recurse start (ItemPool._free.of entered pool, nodes)
        [enteredFree.1.load, enteredChain.formed]
      case invariant => exact ⟨rfl, enteredChain, rfl⟩
    rintro ⟨⟨node, rest⟩, current, frame⟩ ⟨same, segment, answer⟩ recurse
    dsimp only at same segment answer recurse
    subst same
    cases node with
    | null =>
      -- The list ended without meeting `item`.
      have empty := segment.null_nil
      subst empty
      rw [← answer]
      cil_loop_finish [enteredItem]
      simp [listed]
    | address node =>
      obtain ⟨tail, rfl, readable, rest⟩ := segment.next
      by_cases hit : item = .address node
      · subst hit
        rw [← answer]
        cil_loop_finish
        simp [listed]
      · -- The local moves to the next node, one shorter list away from the end.
        have differ : ManagedReference.address node ≠ item := fun same => hit same.symm
        cil_loop_recurse recurse (PooledItem.NextFree.of current node, tail)
          [readable.load, rest.formed, enteredItem, differ]
        case invariant =>
          refine ⟨rfl, rest, ?_⟩
          rw [← answer]
          simp [listed, hit]
        case measure => simp
  exact ⟨fuel, final, _, invoked, framed, listed item nodes, rfl, rfl⟩

#print axioms idle_holds

/-- An item pushed onto the free list is idle, whatever follows it. -/
theorem idle_head (node : Reference) (tail : List Reference) :
    listed (.address node) (node :: tail) = true := by
  simp [listed]

#print axioms idle_head

/-- A null item is never idle. -/
theorem null_not_idle (nodes : List Reference) : listed .null nodes = false := by
  simp [listed]

#print axioms null_not_idle

/-- The free-list search contract, audited as the file's theorem. -/
theorem correctness : idleContract.Holds Extracted.program isIdle := idle_holds

#print axioms correctness

end ExampleProof
