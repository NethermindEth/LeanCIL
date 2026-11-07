import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts
import CIL.Safety.MethodContract

/-!
# A method that constructs a class instance

`Objects.Fresh(step)` constructs a `Tally` through its constructor, which sets `Step`, stores 5
into `Count` and returns the sum of both fields. The instance is charged to the caller's heap
budget: with budget for it the result is `5 + step` and no memory the caller held changes;
without, `newobj` fails with the model's `allocationFailure` before the constructor runs.
-/

open CIL.Safety
open CIL (W32)
namespace ExampleProof

/-- The class identity of `Examples.Tally` instances. -/
def tallyType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Tally"

/-- The runtime type of a `Tally` instance; `Tally` derives from `System.Object` directly. -/
def tally : RuntimeType := ⟨tallyType, []⟩

/-- The model size of a `Tally`: one 8-byte slot for each of its two fields. -/
def tallySize : Nat := 16

bind_method fresh freshBody := "System.UInt64 Examples.Objects::Fresh(System.UInt32)"

/-- With 16 bytes of heap budget, `Fresh(step)` returns `5 + step` for every `step`, and every
    allocation, byte and authority the caller held is unchanged. -/
theorem correctness (memory : Memory) (formed : memory.WellFormed)
    (budget : tallySize ≤ memory.heapBudget) (step : W32) :
    ∃ fuel final, invoke Extracted.program fuel fresh [.scalar (.i32 step)] memory =
        .ok (final, [.scalar (.i64 (5 + step.zeroExtend 64))]) ∧
      MemoryBelow memory.nextIdentity memory final := by
  have bounded : tallySize < nativeLimit := by decide
  have allocated := allocateObject_ok formed tally budget bounded
  have created := objectMemory_formObject memory tally tallySize
  have owned := tally.identity_mem_lineage
  have stepField := objectMemory_field memory tally owned bounded (offset := 8) (by decide)
  have countField := objectMemory_field memory tally owned bounded (offset := 0) (by decide)
  -- The constructor writes `Step`, then `Fresh` writes `Count`; both in the fresh instance.
  have stepReady := objectMemory_access memory tally bounded (offset := 8) (width := 4)
    (by decide) (by decide) true
  obtain ⟨afterStep, stepWritten⟩ := write_succeeds (bytes := numberBytes step.toNat 4)
    (alignment := 1) (by simpa only [numberBytes_length] using stepReady)
  have stepFramed : Confined [(⟨memory.nextIdentity, 8⟩, 4)] _ afterStep :=
    Confined.write stepWritten (by simp [numberBytes_length])
  have unborn : memory.nextIdentity < (objectMemory memory tally tallySize).nextIdentity :=
    by simp [objectMemory]
  have countReady : access afterStep ⟨memory.nextIdentity, 0⟩ 8 1 true = .ok () := by
    rw [stepFramed.access_write _ unborn]
    exact objectMemory_access memory tally bounded (by decide) (by decide) true
  obtain ⟨afterCount, countWritten, -, countRead⟩ := store_word64 5 countReady
  have stepAllocations := write_allocations _ _ _ _ _ stepWritten
  have countAllocations := write_allocations _ _ _ _ _ countWritten
  have stepFormed := (formObject_of_allocations stepAllocations _).trans created
  have countFormed :=
    (formObject_of_allocations (countAllocations.trans stepAllocations) _).trans created
  have countFieldAfterStep : objectFieldAddress afterStep (.address ⟨memory.nextIdentity, 0⟩)
      tallyType 0 = .ok ⟨memory.nextIdentity, 0⟩ :=
    (objectFieldAddress_of_allocations stepAllocations _ _ _).trans countField
  have stepFieldAfter : objectFieldAddress afterCount (.address ⟨memory.nextIdentity, 0⟩)
      tallyType 8 = .ok ⟨memory.nextIdentity, 8⟩ := (objectFieldAddress_of_allocations
    (countAllocations.trans stepAllocations) _ _ _).trans stepField
  have countFieldAfter : objectFieldAddress afterCount (.address ⟨memory.nextIdentity, 0⟩)
      tallyType 0 = .ok ⟨memory.nextIdentity, 0⟩ := (objectFieldAddress_of_allocations
    (countAllocations.trans stepAllocations) _ _ _).trans countField
  -- The step writes with the ordinary alignment and the literal's byte encoding.
  have countStored : write afterStep ⟨memory.nextIdentity, 0⟩ (numberBytes 5 8)
      ordinaryAccessAlignment = .ok afterCount := countWritten
  have stepStored := write_readback _ _ _ _ _ stepWritten
  rw [numberBytes_length] at stepStored
  have stepRead := write_preserves_disjoint_read countWritten stepStored
    (Or.inr (Or.inr (by simp [numberBytes_length])))
  have countLoaded := load_word64_of_read countRead
  have stepLoaded := load_scalar_of_read (width := 4) (x := step) (by decide) stepRead
  refine ⟨CIL.executionBound Extracted.program fresh, afterCount, ?_, ?_⟩
  · cil_checked_steps [allocated, created, stepField, stepWritten, stepFormed,
      countFieldAfterStep, countStored, countFormed, countFieldAfter, stepFieldAfter,
      countLoaded, stepLoaded, tally, tallyType, tallySize]
  · exact (allocateObject_effect allocated).below.trans
      ((write_preserves_memory_below _ _ _ _ _ _ (by simp) stepWritten).trans
        (write_preserves_memory_below _ _ _ _ _ _ (by simp) countWritten))

#print axioms correctness

/-- With less than 16 bytes of heap budget, `Fresh` fails at its `newobj` with the model's
    resource fault, which is not a CLR exception, and its constructor never runs. -/
theorem insufficient_budget (memory : Memory) (short : memory.heapBudget < tallySize)
    (step : W32) :
    ∃ fuel, invoke Extracted.program fuel fresh [.scalar (.i32 step)] memory =
      .error ⟨fresh, 1, .allocationFailure tallySize memory.heapBudget⟩ := by
  have failed := allocateObject_insufficient tally short
  refine ⟨CIL.executionBound Extracted.program fresh, ?_⟩
  cil_checked_steps [failed, tally, tallyType, tallySize]

#print axioms insufficient_budget

end ExampleProof
