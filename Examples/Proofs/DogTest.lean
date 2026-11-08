import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts

/-!
# A class test with `isinst`

`ClassTests.IsDog(animal)` is `animal is Dog`, which compiles to `isinst Dog` and a comparison
against null. The test reads the instance's runtime lineage: a `Dog` passes, a `Bird` gives
null, and so does a null reference, so the method answers whether the animal is a dog.
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
/-- A `Dog` is a dog. -/
theorem dog_is_dog (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal)))
    (typed : runtimeTypeOf memory animal = .ok dog) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address animal)] memory =
      .ok (memory, [.scalar (.i32 1)]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [formed, typed, dog, scope, RuntimeType.lineage]

#print axioms dog_is_dog

/-- A `Bird` is not a dog. -/
theorem bird_is_not_dog (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal)))
    (typed : runtimeTypeOf memory animal = .ok bird) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address animal)] memory =
      .ok (memory, [.scalar (.i32 0)]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [formed, typed, bird, scope, animalType, RuntimeType.lineage]

#print axioms bird_is_not_dog

/-- Null is not a dog. -/
theorem null_is_not_dog (memory : CIL.Safety.Memory) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object .null] memory =
      .ok (memory, [.scalar (.i32 0)]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps

#print axioms null_is_not_dog

/-- `IsDog` answers one exactly for a `Dog`, and zero for a `Bird` or null. -/
theorem correctness (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal))) :
    (runtimeTypeOf memory animal = .ok dog → ∃ fuel,
      invoke Extracted.program fuel 0 [.object (.address animal)] memory =
        .ok (memory, [.scalar (.i32 1)])) ∧
    (runtimeTypeOf memory animal = .ok bird → ∃ fuel,
      invoke Extracted.program fuel 0 [.object (.address animal)] memory =
        .ok (memory, [.scalar (.i32 0)])) ∧
    ∃ fuel, invoke Extracted.program fuel 0 [.object .null] memory =
      .ok (memory, [.scalar (.i32 0)]) :=
  ⟨dog_is_dog memory animal formed, bird_is_not_dog memory animal formed,
    null_is_not_dog memory⟩

#print axioms correctness

end ExampleProof