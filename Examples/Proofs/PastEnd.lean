import Extracted
import CIL.Safety.FuelLemmas
open CIL.Safety
namespace ExampleProof

/-- Caller memory with one readable and writable 8-byte allocation, identity 0. -/
def callerMemory : CIL.Safety.Memory where
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 8, true, true⟩]
  nextIdentity := 1

/-- A reference to the start of `callerMemory`'s allocation. -/
def callerReference : CIL.Safety.Value := .reference (.address ⟨0, 0⟩)

def fault : LocatedFault := ⟨0, 3, .memory .outsideAllocation (.address ⟨0, 8⟩) 8⟩

theorem witness : invoke Extracted.program 16 0 [callerReference] callerMemory = .error fault := by
  rfl

theorem correctness (fuel : Nat) (result : Memory × List Value) :
    invoke Extracted.program fuel 0 [callerReference] callerMemory ≠ .ok result :=
  invoke_fault_refutes_success _ 16 _ _ _ fault (by decide) witness fuel result
#print axioms correctness
end ExampleProof
