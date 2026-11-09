import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts

/-!
# A virtual call on an instance the method constructs

`VirtualCalls.DogLegs()` constructs a `Dog` and calls the abstract `Animal.Legs()` on it. The
fresh instance's runtime type is the one `newobj` recorded (`objectMemory_runtimeTypeOf`), so
the call enters `Dog.Legs` and the method returns four. A `Dog` has no fields, so it takes no
heap budget.
-/

open CIL CIL.Safety
namespace ExampleProof

/-- The assembly scope of the example classes. -/
def scope : String := "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- The runtime type of a `Dog` instance, whose only admitted base is `Animal`. -/
def dog : RuntimeType :=
  ⟨.object scope "Examples.Dog", [.object scope "Examples.Animal"]⟩

/-- `DogLegs()` returns four in every well-formed memory, whose only change is the fresh
    instance. -/
theorem correctness (memory : CIL.Safety.Memory) (formed : memory.WellFormed) :
    ∃ fuel, invoke Extracted.program fuel 0 [] memory =
      .ok (objectMemory memory dog 0, [.scalar (.i64 4)]) := by
  have allocated := allocateObject_ok formed dog (Nat.zero_le _) (by decide)
  have created := objectMemory_formObject memory dog 0
  have typed := objectMemory_runtimeTypeOf memory dog 0
  cil_checked_steps [allocated, created, typed, dog, scope]

#print axioms correctness

end ExampleProof
