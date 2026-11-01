import CIL.Safety.Execution

/-!
Caller memory and argument fixtures shared by the repository's tests. They are test inputs, not
part of the framework, and are not shipped with the tool.
-/

namespace Tests
open CIL.Safety

/-- Caller memory with one readable and writable 8-byte allocation, identity 0. -/
def caller : Memory where
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 8, true, true⟩]
  nextIdentity := 1

/-- A reference to the start of `caller`'s allocation. -/
def reference : Value := .reference (.address ⟨0, 0⟩)

end Tests
