import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields

/-!
# Replacing an integer array held in a class field

`SampleArrays.Refill(samples, values)` stores the `int[]` `values` into `samples.Values`, which
the extraction names `Samples.Values`. Proved: its contract, for a whole live heap array, with
the field's slot as its whole footprint and the array's origin as what the field then holds;
and the `NullReferenceException` of a null receiver at the `stfld`.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

bind_method refill refillBody :=
  "System.Void Examples.SampleArrays::Refill(Examples.Samples,System.Int32[])"

/-- `Refill(samples, values)` leaves `samples.Values` holding the origin of the whole array of
    `length` integers it is given, and changes nothing else. -/
def refillContract : MethodContract (Reference × Reference × Nat) where
  args := fun (samples, values, length) =>
    [.object (.address samples), .array ⟨.address values, length, .signed32⟩]
  pre := fun (samples, values, length) memory => Samples.Values.Owned memory samples ∧
    WholeArray memory .signed32 values length
  footprint := fun (samples, _, _) => [Samples.Values.entry samples]
  post := fun (samples, values, _) _ final results => results = [] ∧
    Samples.Values.Holds final samples (.address values)

/-- `Refill` meets its contract: one `stfld` of the field's slot. -/
theorem correctness : refillContract.Holds Extracted.program refill := by
  rintro ⟨samples, values, length⟩ memory ⟨owned, whole⟩
  obtain ⟨stored, framed, held⟩ := owned.store_whole whole
  refine MethodContract.Holds.intro _ []
    ⟨CIL.executionBound Extracted.program refill, ?_⟩ framed ⟨rfl, held⟩
  dsimp only [refillContract]
  cil_checked_steps [owned.live.formed, owned.located, stored, whole.valid]

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
