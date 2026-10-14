import CIL.Safety.Execution

namespace Examples
open CIL.Safety

def empty : Memory := {
  allocations := fun _ => none
  cells := fun _ _ => ⟨0, false⟩
  views := []
  nextIdentity := 0
}

def caller : Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 8, true, true⟩]
  nextIdentity := 1
}

def reference : Value := .reference (.address ⟨0, 0⟩)
end Examples
