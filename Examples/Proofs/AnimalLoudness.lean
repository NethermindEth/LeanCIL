import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts

/-!
# A virtual call that may run an inherited body

`VirtualCalls.LoudnessOf(animal)` calls the virtual `Animal.Loudness()`, whose own body returns
one. `Dog` overrides it to return ten; `Bird` does not, so its table entry is the base body.
Lean rechecked both entries against the catalog: walking `Bird`'s class chain finds no override
before `Animal`, so the runtime selects the inherited body.
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

/-- A `Dog` runs its override and returns ten. -/
theorem dog_loud (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal)))
    (typed : runtimeTypeOf memory animal = .ok dog) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address animal)] memory =
      .ok (memory, [.scalar (.i64 10)]) := by
  cil_checked_steps [formed, typed, dog, scope]

#print axioms dog_loud

/-- A `Bird` inherits `Animal.Loudness` and returns one. -/
theorem bird_quiet (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal)))
    (typed : runtimeTypeOf memory animal = .ok bird) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address animal)] memory =
      .ok (memory, [.scalar (.i64 1)]) := by
  cil_checked_steps [formed, typed, bird, scope]

#print axioms bird_quiet

/-- `LoudnessOf` returns ten for a `Dog`, by its override, and one for a `Bird`, by the body it
    inherits. -/
theorem correctness (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal))) :
    (runtimeTypeOf memory animal = .ok dog → ∃ fuel,
      invoke Extracted.program fuel 0 [.object (.address animal)] memory =
        .ok (memory, [.scalar (.i64 10)])) ∧
    (runtimeTypeOf memory animal = .ok bird → ∃ fuel,
      invoke Extracted.program fuel 0 [.object (.address animal)] memory =
        .ok (memory, [.scalar (.i64 1)])) :=
  ⟨dog_loud memory animal formed, bird_quiet memory animal formed⟩

#print axioms correctness

end ExampleProof
