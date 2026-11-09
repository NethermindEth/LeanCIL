import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields

/-!
# Replacing an integer array held in a class field

`SampleArrays.Refill(samples, values)` stores the `int[]` `values` into `samples.Values`. The
field's slot keeps the array's origin. Proved: for a whole live heap array, the store changes
that slot alone, to the array's origin, and a null receiver throws `NullReferenceException` at
the `stfld`.
-/

open CIL.Safety
namespace ExampleProof

/-- The class identity of `Examples.Samples`. -/
@[reducible] def samplesType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Samples"

bind_method refill refillBody :=
  "System.Void Examples.SampleArrays::Refill(Examples.Samples,System.Int32[])"

/-- Storing a whole array of `length` integers changes only the field's slot, which then holds
    the array's origin. -/
theorem correctness (memory : Memory) (samples field values : Reference)
    (allocation : Allocation) (length : Nat)
    (formed : formObject memory (.address samples) = .ok (.object (.address samples)))
    (located : objectFieldAddress memory (.address samples) samplesType 0 = .ok field)
    (writable : access memory field CIL.objectFieldSlot ordinaryAccessAlignment true = .ok ())
    (found : liveAllocation memory values.allocation = .ok allocation)
    (heap : allocation.kind = .managedHeap) (origin : values.offset = 0)
    (whole : allocation.layout.size = length * 4)
    (valid : ArrayView.validate ⟨.address values, length, .signed32⟩ memory = .ok ()) :
    ∃ fuel, invoke Extracted.program fuel refill
        [.object (.address samples), .array ⟨.address values, length, .signed32⟩] memory =
      .ok (setSlot memory field (.address values), []) := by
  have stored := storeArraySlot_whole (length := length) (element := .signed32) writable found
    heap origin whole
  refine ⟨CIL.executionBound Extracted.program refill, ?_⟩
  cil_checked_steps [formed, located, stored, valid]

#print axioms correctness

/-- A null receiver throws `NullReferenceException` at the `stfld`, pc 2. -/
theorem null_samples (memory : Memory) (values : Reference) (length : Nat)
    (valid : ArrayView.validate ⟨.address values, length, .signed32⟩ memory = .ok ()) :
    ∃ fuel, invoke Extracted.program fuel refill
        [.object .null, .array ⟨.address values, length, .signed32⟩] memory =
      .error ⟨refill, 2, .thrown "System.NullReferenceException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program refill, ?_⟩
  cil_checked_steps [valid]

#print axioms null_samples

end ExampleProof
