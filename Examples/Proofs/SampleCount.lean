import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields

/-!
# The length of an integer array held in a class field

`SampleArrays.Count(samples)` returns `samples.Values.Length`, which `ldlen` reads from the array
the field holds. Proved: for a whole live array of `length` integers it returns `length` and
changes nothing, and for a null field it throws `NullReferenceException` at the `ldlen`.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

bind_method count countBody := "System.Int32 Examples.SampleArrays::Count(Examples.Samples)"

/-- A field holding a whole array of `length` integers returns `length` and changes nothing. -/
theorem correctness (memory : Memory) (samples values : Reference) (length : Nat)
    (readable : Samples.Values.Readable memory samples)
    (held : Samples.Values.of memory samples = .address values)
    (whole : WholeArray memory .signed32 values length) :
    ∃ fuel, invoke Extracted.program fuel count [.object (.address samples)] memory =
      .ok (memory, [.scalar (.i32 (BitVec.ofNat 32 length))]) := by
  obtain ⟨formed, located, loaded⟩ := readable.facts held whole (by decide)
  cil_checked_steps [formed, located, loaded, whole.valid]

#print axioms correctness

/-- A field holding null throws `NullReferenceException` at the `ldlen`, pc 2. -/
theorem null_values (memory : Memory) (samples : Reference)
    (readable : Samples.Values.Readable memory samples)
    (held : Samples.Values.of memory samples = .null) :
    ∃ fuel, invoke Extracted.program fuel count [.object (.address samples)] memory =
      .error ⟨count, 2, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps [readable.live.formed, readable.located, readable.load_null held rfl]

#print axioms null_values

end ExampleProof
