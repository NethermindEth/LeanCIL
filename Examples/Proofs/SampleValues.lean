import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields

/-!
# An integer array held in a class field

`Examples.Samples` holds its `Values`, an `int[]`, in a field whose slot keeps the origin of the
whole array. `SampleArrays.ValuesOf(samples)` returns `samples.Values`. Proved: when the slot
names a whole live heap array of `length` integers, it returns that array with that length and
changes nothing; when the field holds null it returns the null array.
-/

open CIL.Safety
namespace ExampleProof

/-- The class identity of `Examples.Samples`. -/
@[reducible] def samplesType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Samples"

bind_method valuesOf valuesOfBody :=
  "System.Int32[] Examples.SampleArrays::ValuesOf(Examples.Samples)"

/-- A field naming a whole array of `length` integers returns that array and changes nothing. -/
theorem correctness (memory : Memory) (samples field values : Reference)
    (allocation : Allocation) (length : Nat)
    (formed : formObject memory (.address samples) = .ok (.object (.address samples)))
    (located : objectFieldAddress memory (.address samples) samplesType 0 = .ok field)
    (readable : access memory field CIL.objectFieldSlot ordinaryAccessAlignment false = .ok ())
    (held : memory.slots field.allocation field.offset = .address values)
    (found : liveAllocation memory values.allocation = .ok allocation)
    (heap : allocation.kind = .managedHeap) (origin : values.offset = 0)
    (whole : allocation.layout.size = length * 4)
    (valid : ArrayView.validate ⟨.address values, length, .signed32⟩ memory = .ok ()) :
    ∃ fuel, invoke Extracted.program fuel valuesOf [.object (.address samples)] memory =
      .ok (memory, [.array ⟨.address values, length, .signed32⟩]) := by
  have loaded : loadArraySlot memory field .signed32 =
      .ok (.array ⟨.address values, length, .signed32⟩) := by
    rw [loadArraySlot_of_access readable, held]
    exact arrayOfSlot_whole found heap origin (by decide) whole valid
  refine ⟨CIL.executionBound Extracted.program valuesOf, ?_⟩
  cil_checked_steps [formed, located, loaded, valid, leaveFrame]

#print axioms correctness

/-- A field holding null returns the null array. -/
theorem null_values (memory : Memory) (samples field : Reference)
    (formed : formObject memory (.address samples) = .ok (.object (.address samples)))
    (located : objectFieldAddress memory (.address samples) samplesType 0 = .ok field)
    (readable : access memory field CIL.objectFieldSlot ordinaryAccessAlignment false = .ok ())
    (held : memory.slots field.allocation field.offset = .null) :
    ∃ fuel, invoke Extracted.program fuel valuesOf [.object (.address samples)] memory =
      .ok (memory, [.array ⟨.null, 0, .signed32⟩]) := by
  have loaded : loadArraySlot memory field .signed32 = .ok (.array ⟨.null, 0, .signed32⟩) := by
    rw [loadArraySlot_of_access readable, held]
    rfl
  refine ⟨CIL.executionBound Extracted.program valuesOf, ?_⟩
  cil_checked_steps [formed, located, loaded, leaveFrame]

#print axioms null_values

end ExampleProof
