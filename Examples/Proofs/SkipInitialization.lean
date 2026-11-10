import Extracted
import CIL.Safety.SymbolicExecution

/-! Skipping initialization consumes a checked reference without initializing its storage. -/

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

/-- The checked instruction preserves every byte and initialization flag of caller memory. -/
theorem step_preserves (body : CIL.Method) (pc : Nat) (args : List Value)
    (frame : Frame) (memory : Memory) (reference : ManagedReference) (stack : List Value)
    (valid : ∃ value, formValue memory reference = .ok value) :
    step body .skipInit pc args frame (.reference reference :: stack) memory =
      .ok (.next (pc + 1) stack frame memory) := by
  obtain ⟨value, valid⟩ := valid
  rw [step_skipInit_reference_eq, valid]
  rfl

#print axioms correctness
#print axioms step_preserves
end ExampleProof
