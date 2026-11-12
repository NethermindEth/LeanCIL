import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts
import CIL.Safety.FuelLemmas

/-!
# A virtual call on an abstract base

`VirtualCalls.LegsOf(animal)` calls the abstract `Animal.Legs()`, which `Dog` and `Bird`
override. The call's dispatch table lists both classes with their overrides, and Lean rechecked
each entry against the extraction's catalog. The receiver's runtime class selects the body:
a `Dog` has four legs and a `Bird` two. A null receiver throws
`NullReferenceException` at the `callvirt`. An instance of any class the table omits, such as a
class from an assembly outside the extraction, is the model fault `outsideDispatchTable`: no
return and no exception is proved for it, so every theorem here names the receiver's class.
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

/-- A live `Dog` runs `Dog.Legs` and returns four, leaving memory as it was. -/
theorem dog_legs (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal)))
    (typed : runtimeTypeOf memory animal = .ok dog) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address animal)] memory =
      .ok (memory, [.scalar (.i64 4)]) := by
  cil_checked_steps [formed, typed, dog, scope]

#print axioms dog_legs

/-- A live `Bird` runs `Bird.Legs` and returns two. -/
theorem bird_legs (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal)))
    (typed : runtimeTypeOf memory animal = .ok bird) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address animal)] memory =
      .ok (memory, [.scalar (.i64 2)]) := by
  cil_checked_steps [formed, typed, bird, scope]

#print axioms bird_legs

/-- A null receiver throws `NullReferenceException` at the `callvirt`, before any body runs. -/
theorem null_throws (memory : CIL.Safety.Memory) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object .null] memory =
      .error ⟨0, 1, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps

#print axioms null_throws

/-- `LegsOf` returns the legs of the receiver's runtime class: four for a `Dog`, two for a
    `Bird`. -/
theorem correctness (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal))) :
    (runtimeTypeOf memory animal = .ok dog → ∃ fuel,
      invoke Extracted.program fuel 0 [.object (.address animal)] memory =
        .ok (memory, [.scalar (.i64 4)])) ∧
    (runtimeTypeOf memory animal = .ok bird → ∃ fuel,
      invoke Extracted.program fuel 0 [.object (.address animal)] memory =
        .ok (memory, [.scalar (.i64 2)])) :=
  ⟨dog_legs memory animal formed, bird_legs memory animal formed⟩

#print axioms correctness

/-- The runtime type of a class from an assembly the extraction does not include, deriving from
    `Animal`; no table entry names it. -/
def plugin : RuntimeType :=
  ⟨.object "Plugins, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Plugins.Cat",
    [animalType]⟩

/-- An instance of a class the table omits stops at the `callvirt` with the model fault, not a
    call and not a CLR exception. -/
theorem outside_faults (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal)))
    (typed : runtimeTypeOf memory animal = .ok plugin) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object (.address animal)] memory =
      .error ⟨0, 1, outsideDispatchTable⟩ := by
  cil_checked_steps [formed, typed, plugin, scope]

#print axioms outside_faults

/-- So for such an instance no fuel proves a return or a thrown exception: every outcome is the
    model fault or running out of fuel. -/
theorem outside_neither_returns_nor_throws (memory : CIL.Safety.Memory) (animal : Reference)
    (formed : formObject memory (.address animal) = .ok (.object (.address animal)))
    (typed : runtimeTypeOf memory animal = .ok plugin) (fuel : Nat) :
    (∀ result, invoke Extracted.program fuel 0 [.object (.address animal)] memory ≠
      .ok result) ∧
    (∀ fault, invoke Extracted.program fuel 0 [.object (.address animal)] memory =
      .error fault → ∀ exception, fault.fault ≠ .thrown exception) := by
  obtain ⟨observed, witness⟩ := outside_faults memory animal formed typed
  have semantic : outsideDispatchTable ≠ .fuelExhausted := by simp [outsideDispatchTable]
  refine ⟨invoke_fault_refutes_success _ observed 0 _ _ _ semantic witness fuel, ?_⟩
  intro fault failed exception thrown
  have settled : Settled
      (Except.error fault : Except LocatedFault (CIL.Safety.Memory × List CIL.Safety.Value)) := by
    simp [Settled, thrown]
  have up := invoke_mono _ fuel observed 0 _ _ _ settled failed
  have down := invoke_mono _ observed fuel 0 _ _ _ (by exact semantic) witness
  rw [Nat.add_comm, up] at down
  cases down
  simp [outsideDispatchTable] at thrown

#print axioms outside_neither_returns_nor_throws

end ExampleProof
