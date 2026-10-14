import Extracted
import Examples.Support
import CIL.Safety.FuelLemmas
open CIL.Safety
namespace ExampleProof

def fault : LocatedFault := ⟨0, 3, .memory .outsideAllocation (.address ⟨0, 8⟩) 8⟩

theorem witness : invoke Extracted.program 16 0 [Examples.reference] Examples.caller = .error fault := by
  rfl

theorem correctness (fuel : Nat) (result : Memory × List Value) :
    invoke Extracted.program fuel 0 [Examples.reference] Examples.caller ≠ .ok result :=
  invoke_fault_refutes_success _ 16 _ _ _ fault (by decide) witness fuel result
#print axioms correctness
end ExampleProof
