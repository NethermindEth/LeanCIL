import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.HeapObjectFacts
import CIL.Safety.MemoryLemmas

/-!
# Instances of a class with no fields

`Objects.TwoMarkers()` constructs two instances of `Marker`, a class with no fields, and
compares them. A `Marker` occupies no bytes and costs no heap budget, yet the two instances are
distinct allocations, so the comparison reports them different. No byte of a `Marker` can be
read or written, so no field access of any width or offset succeeds on one.
-/

open CIL.Safety
namespace ExampleProof

/-- The class identity of `Examples.Marker` instances. -/
def markerType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Marker"

bind_method twoMarkers twoMarkersBody := "System.Boolean Examples.Objects::TwoMarkers()"

/-- `TwoMarkers()` returns `true` from every well-formed memory, whatever its heap budget: two
    instances of a class with no fields are distinct by identity alone. -/
theorem correctness (memory : Memory) (formed : memory.WellFormed) :
    ∃ fuel final, invoke Extracted.program fuel twoMarkers [] memory =
      .ok (final, [.scalar (.i32 1)]) := by
  have bounded : (0 : Nat) < nativeLimit := by decide
  have first := allocateObject_ok formed ⟨markerType⟩ (Nat.zero_le _) bounded
  have firstFormed := (allocateObject_effect first).wellFormed formed
  have second := allocateObject_ok firstFormed ⟨markerType⟩ (Nat.zero_le _) bounded
  have firstCreated := objectMemory_formObject memory ⟨markerType⟩ 0
  have secondCreated :=
    objectMemory_formObject (objectMemory memory ⟨markerType⟩ 0) ⟨markerType⟩ 0
  -- The second construction leaves the first instance live.
  have firstKept : formObject (objectMemory (objectMemory memory ⟨markerType⟩ 0) ⟨markerType⟩ 0)
      (.address ⟨memory.nextIdentity, 0⟩) = .ok (.object (.address ⟨memory.nextIdentity, 0⟩)) := by
    simp [formObject, liveAllocation, objectMemory, checkedAt, Except.mapError, Bind.bind,
      Except.bind, Pure.pure, Except.pure]
  -- The second instance is a later allocation than the first.
  have distinct : memory.nextIdentity ≠ (objectMemory memory ⟨markerType⟩ 0).nextIdentity := by
    simp [objectMemory]
  simp only [markerType] at first second firstCreated secondCreated firstKept distinct
  refine ⟨CIL.executionBound Extracted.program twoMarkers,
    objectMemory (objectMemory memory ⟨markerType⟩ 0) ⟨markerType⟩ 0, ?_⟩
  simp only [markerType]
  cil_checked_entry [first, second, firstCreated, secondCreated, firstKept, distinct]
  cil_checked_steps 7 [first, second, firstCreated, secondCreated, firstKept, distinct]
  -- `ceq` of the two instances pushed 0, and `ceq` of that with 0 pushes 1.
  simp only [ite_true]
  cil_checked_steps
  rfl

#print axioms correctness

/-- A fresh `Marker` has no byte at any offset: an access of any positive width, alignment and
    direction fails, so every field load and store, which reads or writes through `access`, fails
    on it. -/
theorem no_field_bytes (memory : Memory) (offset width alignment : Nat) (nonempty : 0 < width)
    (writing : Bool) :
    access (objectMemory memory ⟨markerType⟩ 0) ⟨memory.nextIdentity, offset⟩ width alignment
      writing ≠ .ok () := by
  intro granted
  obtain ⟨allocation, found, -, fits⟩ :=
    access_within_allocation _ _ width alignment writing granted
  simp only [objectMemory, ite_true, Option.some.injEq] at found
  subst found
  simp only at fits
  omega

#print axioms no_field_bytes

end ExampleProof
