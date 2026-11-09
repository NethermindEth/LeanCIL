import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts

/-!
# A class cast with `castclass`

`ClassTests.AsDog(animal)` is `(Dog)animal`, which compiles to `castclass Dog`. The cast reads
the instance's runtime lineage: a `Dog` comes back as the same reference, a `Bird` throws
`InvalidCastException` at the cast, and a null reference passes through as null.
-/
open CIL CIL.Safety
namespace ExampleProof

/-- The assembly scope of the example classes. -/
def scope : String := "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- The class identity of the abstract base `Examples.Animal`. -/
def animalType : Extraction.TypeExpr := .object scope "Examples.Animal"

/-- The runtime type of a `Dog` instance. -/
def dog : RuntimeType := ⟨.object scope "Examples.Dog", [animalType]⟩

/-- The runtime type of a `Bird` instance. -/
def bird : RuntimeType := ⟨.object scope "Examples.Bird", [animalType]⟩
/-- A `Dog` casts to itself. -/
theorem dog_casts (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal)))
    (typed : runtimeTypeOf memory animal = .ok dog) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address animal)] memory =
      .ok (memory, [.object (.address animal)]) := by
  cil_checked_steps [formed, typed, dog, scope, RuntimeType.lineage]

#print axioms dog_casts

/-- A `Bird` throws `InvalidCastException` at the cast. -/
theorem bird_throws (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal)))
    (typed : runtimeTypeOf memory animal = .ok bird) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address animal)] memory =
      .error ⟨0, 1, .thrown "System.InvalidCastException"⟩ := by
  cil_checked_steps [formed, typed, bird, scope, animalType, RuntimeType.lineage]

#print axioms bird_throws

/-- Null casts to null. -/
theorem null_casts (memory : CIL.Safety.Memory) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object .null] memory =
      .ok (memory, [.object .null]) := by
  cil_checked_steps

#print axioms null_casts

/-- `AsDog` returns a `Dog` or null as it stands and throws for a `Bird`. -/
theorem correctness (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal))) :
    (runtimeTypeOf memory animal = .ok dog → ∃ fuel,
      invoke Extracted.program fuel 0 [.object (.address animal)] memory =
        .ok (memory, [.object (.address animal)])) ∧
    (runtimeTypeOf memory animal = .ok bird → ∃ fuel,
      invoke Extracted.program fuel 0 [.object (.address animal)] memory =
        .error ⟨0, 1, .thrown "System.InvalidCastException"⟩) ∧
    ∃ fuel, invoke Extracted.program fuel 0 [.object .null] memory =
      .ok (memory, [.object .null]) :=
  ⟨dog_casts memory animal formed, bird_throws memory animal formed, null_casts memory⟩

#print axioms correctness

end ExampleProof