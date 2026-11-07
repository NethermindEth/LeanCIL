import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts

/-!
# A field of a base class

`Objects.IdOf(shape)` reads `Id`, which the abstract class `Shape` declares, through a `Shape`
reference. Any instance whose runtime type has `Shape` in its lineage reaches the field, such as a
`Circle`, whose instances record `Shape` as their base; an instance of a class that does not derive
from `Shape` does not, and null throws `NullReferenceException` at the `ldfld`.
-/

open CIL CIL.Safety
namespace ExampleProof

/-- The class identity of `Examples.Shape`. -/
def shapeType : Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Shape"

/-- The runtime type of a `Circle` instance: `Circle`, deriving from `Shape`. -/
def circle : RuntimeType :=
  ⟨.object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Circle",
    [shapeType]⟩

/-- Reading `Id` of a live shape returns the value its 8 bytes hold and changes nothing. -/
theorem correctness (memory : CIL.Safety.Memory) (shape : ManagedReference) (field : Reference)
    (id : BitVec 64) (formed : formObject memory shape = .ok (.object shape))
    (located : objectFieldAddress memory shape shapeType 0 = .ok field)
    (loaded : loadValue memory (.address field) 8 = .ok (.i64 id)) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object shape] memory =
      .ok (memory, [.scalar (.i64 id)]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [formed, located, loaded, shapeType]

#print axioms correctness

/-- A fresh `Circle` reaches `Shape.Id` at its first slot: the field `correctness` reads. -/
theorem circle_located (memory : CIL.Safety.Memory) :
    objectFieldAddress (objectMemory memory circle 16) (.address ⟨memory.nextIdentity, 0⟩)
      shapeType 0 = .ok ⟨memory.nextIdentity, 0⟩ :=
  objectMemory_field memory circle (by simp [circle, RuntimeType.lineage]) (by decide)
    (by decide)

#print axioms circle_located

/-- An instance whose lineage lacks `Shape` has no `Id`: the access is rejected, not read. -/
theorem unrelated_rejected (memory : CIL.Safety.Memory) (type : RuntimeType)
    (unrelated : shapeType ∉ type.lineage) (size : Nat) :
    objectFieldAddress (objectMemory memory type size) (.address ⟨memory.nextIdentity, 0⟩)
      shapeType 0 =
        .error (.unsupported "Field owner is not the object's class or a base of it") := by
  simp [objectFieldAddress, liveAllocation, objectMemory, checkedAt, Except.mapError, Bind.bind,
    Except.bind, Pure.pure, Except.pure, unrelated]

#print axioms unrelated_rejected

/-- Reading a field of the null reference throws `NullReferenceException` at the `ldfld`. -/
theorem null_throws (memory : CIL.Safety.Memory) :
    ∃ fuel, invoke Extracted.program fuel 0 [.object .null] memory =
      .error ⟨0, 1, .thrown "System.NullReferenceException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [objectFieldAddress]

#print axioms null_throws

end ExampleProof
