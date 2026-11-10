import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts
import CIL.Safety.MethodContract

/-!
# A derived class instance

`Objects.Describe(id, radius)` constructs a `Circle`, which derives from the abstract `Shape`.
`Circle`'s constructor chains to `Shape`'s, which sets `Id`, then sets `Radius`; `Describe` reads
`Id` through `Shape`'s field and `Radius` through `Circle`'s and returns their sum. The instance
records `Circle` with its base `Shape`, so a field `Shape` declares is reached on it, at the first
slot, and `Circle`'s own field follows. `Objects.IdOf(shape)` reads `Id` of any instance whose
class derives from `Shape`, and throws `NullReferenceException` on null.
-/

open CIL.Safety
open CIL (W64)
namespace ExampleProof

/-- The class identity of `Examples.Shape`. -/
def shapeType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Shape"

/-- The class identity of `Examples.Circle`. -/
def circleType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Circle"

/-- The runtime type of a `Circle` instance: `Circle`, deriving from `Shape`. -/
def circle : RuntimeType := ⟨circleType, [shapeType]⟩

/-- The model size of a `Circle`: one 8-byte slot for `Shape.Id`, then one for `Radius`. -/
def circleSize : Nat := 16

bind_method describe describeBody :=
  "System.UInt64 Examples.Objects::Describe(System.UInt64,System.UInt64)"

/-- With 16 bytes of heap budget, `Describe(id, radius)` returns `id + radius`, and every
    allocation, byte and authority the caller held is unchanged. -/
theorem correctness (memory : Memory) (formed : memory.WellFormed)
    (budget : circleSize ≤ memory.heapBudget) (id radius : W64) :
    ∃ fuel final, invoke Extracted.program fuel describe
        [.scalar (.i64 id), .scalar (.i64 radius)] memory =
        .ok (final, [.scalar (.i64 (id + radius))]) ∧
      MemoryBelow memory.nextIdentity memory final := by
  have bounded : circleSize < nativeLimit := by decide
  have allocated := allocateObject_ok formed circle budget bounded
  have created := objectMemory_formObject memory circle circleSize
  have shaped : shapeType ∈ circle.lineage := by simp [circle, RuntimeType.lineage]
  have idField := objectMemory_field memory circle shaped bounded (offset := 0) (by decide)
  have radiusField := objectMemory_field memory circle (circle.identity_mem_lineage) bounded
    (offset := 8) (by decide)
  -- `Shape`'s constructor writes `Id`, then `Circle`'s writes `Radius`; both in the instance.
  have idReady := objectMemory_access memory circle bounded (offset := 0) (width := 8)
    (by decide) (by decide) true
  obtain ⟨afterId, idWritten, -, idRead⟩ := store_word64 id idReady
  have idFramed : Confined [(⟨memory.nextIdentity, 0⟩, 8)] _ afterId :=
    Confined.write idWritten (by simp [numberBytes_length])
  have unborn : memory.nextIdentity < (objectMemory memory circle circleSize).nextIdentity :=
    by simp [objectMemory]
  have radiusReady : access afterId ⟨memory.nextIdentity, 8⟩ 8 1 true = .ok () := by
    rw [idFramed.access_write _ unborn]
    exact objectMemory_access memory circle bounded (by decide) (by decide) true
  obtain ⟨afterRadius, radiusWritten, -, radiusRead⟩ := store_word64 radius radiusReady
  have idAllocations := write_allocations _ _ _ _ _ idWritten
  have radiusAllocations := write_allocations _ _ _ _ _ radiusWritten
  have idFormed := (formObject_of_allocations idAllocations _).trans created
  have radiusFormed :=
    (formObject_of_allocations (radiusAllocations.trans idAllocations) _).trans created
  have radiusFieldAfterId : objectFieldAddress afterId (.address ⟨memory.nextIdentity, 0⟩)
      circleType 8 = .ok ⟨memory.nextIdentity, 8⟩ :=
    (objectFieldAddress_of_allocations idAllocations _ _ _).trans radiusField
  have idFieldAfter : objectFieldAddress afterRadius (.address ⟨memory.nextIdentity, 0⟩)
      shapeType 0 = .ok ⟨memory.nextIdentity, 0⟩ := (objectFieldAddress_of_allocations
    (radiusAllocations.trans idAllocations) _ _ _).trans idField
  have radiusFieldAfter : objectFieldAddress afterRadius (.address ⟨memory.nextIdentity, 0⟩)
      circleType 8 = .ok ⟨memory.nextIdentity, 8⟩ := (objectFieldAddress_of_allocations
    (radiusAllocations.trans idAllocations) _ _ _).trans radiusField
  have idStored : write (objectMemory memory circle circleSize) ⟨memory.nextIdentity, 0⟩
      (numberBytes id.toNat 8) ordinaryAccessAlignment = .ok afterId := idWritten
  have radiusStored : write afterId ⟨memory.nextIdentity, 8⟩ (numberBytes radius.toNat 8)
      ordinaryAccessAlignment = .ok afterRadius := radiusWritten
  have idKept := write_preserves_disjoint_read radiusWritten idRead
    (Or.inr (Or.inl (by simp)))
  have idLoaded := load_word64_of_read idKept
  have radiusLoaded := load_word64_of_read radiusRead
  rw [exists_comm]
  simp only [exists_and_right]
  refine ⟨afterRadius, ?_, ?_⟩
  · cil_checked_steps [allocated, created, idField, idStored, idFormed, radiusFieldAfterId,
      radiusStored, radiusFormed, idFieldAfter, radiusFieldAfter, idLoaded, radiusLoaded,
      circle, circleType, shapeType, circleSize]
  · exact (allocateObject_effect allocated).below.trans
      ((write_preserves_memory_below _ _ _ _ _ _ (by simp) idWritten).trans
        (write_preserves_memory_below _ _ _ _ _ _ (by simp) radiusWritten))

#print axioms correctness

end ExampleProof
