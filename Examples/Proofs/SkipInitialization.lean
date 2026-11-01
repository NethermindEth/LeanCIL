import Extracted

namespace ExampleProof

/-- Caller memory with one readable and writable 8-byte allocation, identity 0. -/
def callerMemory : CIL.Safety.Memory where
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 8, true, true⟩]
  nextIdentity := 1

/-- A reference to the start of `callerMemory`'s allocation. -/
def callerReference : CIL.Safety.Value := .reference (.address ⟨0, 0⟩)

open CIL.Safety

def uninitialized : Memory := { callerMemory with
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩ else none
  cells := fun _ _ => ⟨37, false⟩
  views := [⟨0, 0, 32, true, true⟩] }

-- The compiled call consumes its reference without changing any caller byte,
-- including initialization flags. It does not initialize an out parameter.
theorem correctness :
    invoke Extracted.program 4 0 [callerReference] uninitialized = .ok (uninitialized, []) := by
  rfl

theorem instruction_preserves (memory : Memory) (reference : ManagedReference) (stack : List Value)
    (valid : ∃ value, formValue memory reference = .ok value) :
    instruction .skipInit (.reference reference :: stack) memory = .ok (memory, stack) := by
  obtain ⟨value, valid⟩ := valid
  simp [instruction, observerCount, unspecifiedOperands, CIL.Safety.Value.hasUnspecified,
    valid, Functor.map, Except.map]

end ExampleProof
