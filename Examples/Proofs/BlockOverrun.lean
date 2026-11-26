import Extracted
import CIL.Safety.FuelLemmas
import CIL.Safety.StepComposition

/-! The compiled unaligned fill faults on a nine-byte write to an eight-byte allocation. -/

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

def arguments : List Value := [callerReference, .scalar (.i32 0), .scalar (.i32 9)]
def fault : LocatedFault := ⟨0, 3, .memory .outsideAllocation (.address ⟨0, 0⟩) 9⟩

/-- The block call faults at pc 3 after loading its destination, byte and count. -/
theorem witness : invoke Extracted.program 16 0 arguments callerMemory = .error fault := by
  change run Extracted.program 13 0 3 arguments ⟨1, [], [], 0, []⟩
    [.scalar (.i32 9), .scalar (.i32 0), callerReference] callerMemory = .error fault
  apply run_fault Extracted.program_method0 Extracted.method0_instruction3
  rw [step_call_model (link := Extracted.method0_link3) (found := Extracted.method0_model3)
    (direct := rfl)] <;> rfl

/-- No fuel choice can make a nine-byte fill succeed in the eight-byte allocation. -/
theorem correctness (fuel : Nat) (result : Memory × List Value) :
    invoke Extracted.program fuel 0 arguments callerMemory ≠ .ok result :=
  invoke_fault_refutes_success _ 16 _ _ _ fault (by decide) witness fuel result

#print axioms witness
#print axioms correctness
end ExampleProof
