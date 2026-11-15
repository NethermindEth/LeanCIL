import CIL.Safety.Execution

/-!
# Runtime model tests

A typed static span runs in `memoryInstruction`, so a runtime model's memory operation needs no
static field metadata.
-/

namespace Tests.RuntimeModels
open CIL.Safety

/-- One readable 16-byte immutable static field at allocation 0, aligned to 8, whose bytes
    are all 7. -/
private def staticMemory : Memory := {
  allocations := fun id =>
    if id = 0 then some ⟨.immutableStatic, ⟨16, 8, []⟩, true, [16]⟩ else none
  cells := fun _ _ => ⟨7, true⟩
  views := [⟨0, 0, 16, true, false⟩]
  nextIdentity := 1 }

/-- A typed span over the whole field has one element per four bytes. -/
example : memoryInstruction (.createSpan 4) [.reference (.address ⟨0, 0⟩)] staticMemory =
    .ok (staticMemory, [.span (.address ⟨0, 0⟩) 4]) := rfl

end Tests.RuntimeModels
