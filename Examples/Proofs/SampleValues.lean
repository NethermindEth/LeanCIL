import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields

/-!
# An integer array held in a class field

`Examples.Samples` holds its `Values`, an `int[]`, in a field whose slot keeps the origin of the
whole array; the extraction names it `Samples.Values`. `SampleArrays.ValuesOf(samples)` returns
`samples.Values`. Proved: when the field holds a whole live array of `length` integers, it
returns that array with that length and changes nothing; when it holds null it returns the null
array.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

bind_method valuesOf valuesOfBody :=
  "System.Int32[] Examples.SampleArrays::ValuesOf(Examples.Samples)"

/-- A field holding a whole array of `length` integers returns that array and changes nothing. -/
theorem correctness (memory : Memory) (samples values : Reference) (length : Nat)
    (readable : Samples.Values.Readable memory samples)
    (held : Samples.Values.of memory samples = .address values)
    (whole : WholeArray memory .signed32 values length) :
    ∃ fuel, invoke Extracted.program fuel valuesOf [.object (.address samples)] memory =
      .ok (memory, [.array ⟨.address values, length, .signed32⟩]) := by
  obtain ⟨formed, located, loaded⟩ := readable.facts held whole (by decide)
  cil_checked_steps [formed, located, loaded, whole.valid]

#print axioms correctness

/-- A field holding null returns the null array. -/
theorem null_values (memory : Memory) (samples : Reference)
    (readable : Samples.Values.Readable memory samples)
    (held : Samples.Values.of memory samples = .null) :
    ∃ fuel, invoke Extracted.program fuel valuesOf [.object (.address samples)] memory =
      .ok (memory, [.array ⟨.null, 0, .signed32⟩]) := by
  cil_checked_steps [readable.load_null held rfl]

#print axioms null_values

end ExampleProof
