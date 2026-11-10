import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts
import CIL.Safety.ObjectFields
import CIL.Safety.ReferenceArrayElements

/-!
# Constructing a class instance holding a struct array and a vector array

`TileArrays.Hold(pairs, lanes)` constructs a `Tiles` and stores `pairs` into its `Pairs` field
and `lanes` into its `Lanes` field. `newobj` zeroes both fields, so each starts owned and null
(`fresh_holds_null`); each store is confined to its own field, so the first survives the second
(`Holds.after_confined`), and both arrays stay whole across the construction and the stores
(`WholeArray.after_below`, `WholeArray.after_confined`). Nothing the caller held changes.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

bind_method hold holdBody :=
  "Examples.Tiles Examples.TileArrays::Hold(Examples.AggregateArrays/Pair[],\
System.Runtime.Intrinsics.Vector128`1<System.UInt64>[])"

/-- The runtime type of a `Tiles` instance; `Tiles` derives from `System.Object` directly. -/
def tiles : RuntimeType := ⟨Tiles.type, []⟩

/-- The model size of a `Tiles`: one reference slot for each of its two array fields. -/
def tilesSize : Nat := 16

/-- With heap budget for a `Tiles`, `Hold(pairs, lanes)` returns a fresh instance whose fields
    hold the two whole arrays it is given, and every allocation, byte and authority the caller
    held is unchanged. -/
theorem correctness (memory : Memory) (formed : memory.WellFormed)
    (budget : tilesSize ≤ memory.heapBudget) (pairs lanes : Reference) (pairCount laneCount : Nat)
    (wholePairs : WholeArray memory Tiles.Pairs.elementType pairs pairCount)
    (wholeLanes : WholeArray memory Tiles.Lanes.elementType lanes laneCount) :
    ∃ fuel final, invoke Extracted.program fuel hold
        [.array ⟨.address pairs, pairCount, Tiles.Pairs.elementType⟩,
          .array ⟨.address lanes, laneCount, Tiles.Lanes.elementType⟩] memory =
        .ok (final, [.object (.address ⟨memory.nextIdentity, 0⟩)]) ∧
      Tiles.Pairs.Holds final ⟨memory.nextIdentity, 0⟩ (.address pairs) ∧
      Tiles.Lanes.Holds final ⟨memory.nextIdentity, 0⟩ (.address lanes) ∧
      MemoryBelow memory.nextIdentity memory final := by
  have bounded : tilesSize < nativeLimit := by decide
  have allocated := allocateObject_ok formed tiles budget bounded
  have created := objectMemory_formObject memory tiles tilesSize
  have declared := tiles.identity_mem_lineage
  have constructed : MemoryBelow memory.nextIdentity memory (objectMemory memory tiles tilesSize) :=
    (allocateObject_effect allocated).below
  have grown : memory.nextIdentity ≤ (objectMemory memory tiles tilesSize).nextIdentity := by
    simp [objectMemory]
  -- `newobj` leaves both fields owned and null, and both arrays whole.
  have pairsFresh := Tiles.Pairs.fresh_holds_null memory tiles declared bounded (by decide)
  have lanesFresh := Tiles.Lanes.fresh_holds_null memory tiles declared bounded (by decide)
  have pairsKept := wholePairs.after_below constructed wholePairs.old grown
  have lanesKept := wholeLanes.after_below constructed wholeLanes.old grown
  -- The `Pairs` store is confined to its slot, apart from `Lanes`.
  obtain ⟨pairsStored, pairsFramed, pairsHeld⟩ := pairsFresh.1.store_whole pairsKept
  have lanesOwned := lanesFresh.1.after_confined pairsFramed (apart_of_entries rfl)
  have lanesWhole := lanesKept.after_confined pairsFramed
  obtain ⟨lanesStored, lanesFramed, lanesHeld⟩ := lanesOwned.store_whole lanesWhole
  have pairsFinal := pairsHeld.after_confined lanesFramed (apart_of_entries rfl)
  refine ⟨CIL.executionBound Extracted.program hold, _, ?_, pairsFinal, lanesHeld,
    constructed.trans ((ReferenceArray.setSlot_below _ (by simp) _).trans
      (ReferenceArray.setSlot_below _ (by simp) _))⟩
  -- The steps see the constructed memory spelled out, so every fact about it is too.
  simp only [tiles, tilesSize] at *
  cil_checked_steps [wholePairs.valid, wholeLanes.valid, allocated, created, pairsKept.valid,
    lanesWhole.valid, pairsStored, lanesStored]

#print axioms correctness

end ExampleProof