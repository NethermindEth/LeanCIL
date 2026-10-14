import Extracted
import Examples.Support
import CIL.Safety.FuelLemmas

open CIL.Safety
namespace ExampleProof

def arguments : List Value := [Examples.reference, .scalar (.i32 0), .scalar (.i32 9)]
def fault : LocatedFault := ⟨0, 3, .memory .outsideAllocation (.address ⟨0, 0⟩) 9⟩

theorem witness : invoke Extracted.program 16 0 arguments Examples.caller = .error fault := by
  rfl

/-- No fuel choice can make a nine-byte fill succeed in the eight-byte allocation. -/
theorem correctness (fuel : Nat) (result : Memory × List Value) :
    invoke Extracted.program fuel 0 arguments Examples.caller ≠ .ok result :=
  invoke_fault_refutes_success _ 16 _ _ _ fault (by decide) witness fuel result

#print axioms correctness
end ExampleProof
