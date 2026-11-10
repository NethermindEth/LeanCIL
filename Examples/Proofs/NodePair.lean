import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ReferenceArrayElements

/-!
# An array of class references the method creates

`NodeArrays.Pair(first, second)` allocates a `Node[2]`, stores both nodes and reads element 1
back. The array is a class instance charged to the caller's heap budget: with budget for its
two 8-byte slots the result is `second` and no memory the caller held changes; without, the
`newarr` fails with the model's `allocationFailure`, not a CLR exception.
-/

open CIL.Safety
open CIL (objectFieldSlot)
namespace ExampleProof

/-- The class identity of `Examples.Node`, which derives from `System.Object` directly. -/
def nodeType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Node"

/-- The runtime type of a `Node` instance. -/
def node : RuntimeType := ⟨nodeType, []⟩

bind_method pair pairBody :=
  "Examples.Node Examples.NodeArrays::Pair(Examples.Node,Examples.Node)"

/-- With 16 bytes of heap budget, `Pair(first, second)` returns `second` for any two live nodes,
    the same node or not, and every allocation, byte and reference the caller held is kept. -/
theorem correctness (memory : Memory) (formed : memory.WellFormed)
    (budget : objectFieldSlot * 2 ≤ memory.heapBudget) (first second : Reference)
    (firstLive : LiveObject memory first) (secondLive : LiveObject memory second)
    (firstAllocation secondAllocation : Allocation)
    (firstFound : liveAllocation memory first.allocation = .ok firstAllocation)
    (firstKind : firstAllocation.kind = .object node)
    (secondFound : liveAllocation memory second.allocation = .ok secondAllocation)
    (secondKind : secondAllocation.kind = .object node) :
    ∃ fuel final, invoke Extracted.program fuel pair
        [.object (.address first), .object (.address second)] memory =
        .ok (final, [.object (.address second)]) ∧
      MemoryBelow memory.nextIdentity memory final := by
  have bounded : objectFieldSlot * 2 < nativeLimit := by decide
  have allocated := newReferenceArray_ok formed nodeType (value := .i32 2) (length := 2)
    (Or.inl rfl) (by decide) (by decide) budget
  have created := allocateObject_ok formed (referenceArrayType nodeType) budget bounded
  have below := (allocateObject_effect created).below
  have grows : memory.nextIdentity ≤ (objectMemory memory (referenceArrayType nodeType)
      (objectFieldSlot * 2)).nextIdentity := by simp [objectMemory]
  -- Both nodes stay live and keep their class in the fresh memory.
  have firstFresh := firstLive.after_below below firstLive.old grows
  have secondFresh := secondLive.after_below below secondLive.old grows
  have firstStorable := ReferenceArray.storableIn_of_lineage
    ((ReferenceArray.liveAllocation_below below firstLive.old).trans firstFound) firstKind rfl
    rfl (by decide : nodeType ∈ node.lineage)
  -- The first store fills element 0.
  have zero := ReferenceArray.fresh memory nodeType bounded (index := 0) (by decide)
  obtain ⟨located0, checked0, stored0, framed0, held0⟩ := zero.1.store firstFresh firstStorable
  -- Element 1 is untouched by it, and the second store fills it.
  have one := (ReferenceArray.fresh memory nodeType bounded (index := 1) (by decide)).1.across
    framed0 held0
  simp only [show ¬ (0 = 1) by decide, ite_false] at one
  have secondStorable := ReferenceArray.storableIn_of_lineage
    ((ReferenceArray.liveAllocation_below below secondLive.old).trans secondFound) secondKind
    rfl rfl (by decide : nodeType ∈ node.lineage)
  obtain ⟨located1, checked1, stored1, framed1, held1⟩ :=
    one.1.store (secondFresh.after_confined framed0) secondStorable
  have loaded := held1.1.toReadable.facts held1.2
    ((secondFresh.after_confined framed0).after_confined framed1)
  -- Each argument load re-forms its node in the memory of that point.
  have firstFormed := firstFresh.formed
  have secondFormed := (secondFresh.after_confined framed0).formed
  simp only [nodeType, formObject_setSlot] at firstFormed secondFormed
  refine ⟨CIL.executionBound Extracted.program pair,
    setSlot (setSlot (objectMemory memory (referenceArrayType nodeType) (objectFieldSlot * 2))
        (ReferenceArray.slot ⟨memory.nextIdentity, 0⟩ 0) (.address first))
      (ReferenceArray.slot ⟨memory.nextIdentity, 0⟩ 1) (.address second), ?_, ?_⟩
  · simp only [nodeType]
    cil_checked_steps [allocated, located0, checked0, stored0, located1, checked1, stored1,
      loaded.1, loaded.2, firstFormed, secondFormed, nodeType]
  · exact below.trans
      ((ReferenceArray.setSlot_below (field := ReferenceArray.slot ⟨memory.nextIdentity, 0⟩ 0) _
        (Nat.le_refl _) _).trans
      (ReferenceArray.setSlot_below (field := ReferenceArray.slot ⟨memory.nextIdentity, 0⟩ 1) _
        (Nat.le_refl _) _))

#print axioms correctness

/-- With less than 16 bytes of heap budget, `Pair` fails at its `newarr`, pc 1, with the
    model's resource fault, before any store. -/
theorem insufficient_budget (memory : Memory) (short : memory.heapBudget < objectFieldSlot * 2)
    (first second : ManagedReference) (firstFormed : formObject memory first = .ok (.object first))
    (secondFormed : formObject memory second = .ok (.object second)) :
    ∃ fuel, invoke Extracted.program fuel pair [.object first, .object second] memory =
      .error ⟨pair, 1, .allocationFailure (objectFieldSlot * 2) memory.heapBudget⟩ := by
  have failed := newReferenceArray_insufficient memory nodeType (value := .i32 2) (length := 2)
    (Or.inl rfl) (by decide) (by decide) short
  cil_checked_steps [failed, firstFormed, secondFormed, nodeType]

#print axioms insufficient_budget

end ExampleProof
