import Extracted
import Examples.Support
import CIL.Safety.FuelLemmas
open CIL.Safety
namespace ExampleProof

def fault : LocatedFault := ⟨0, 5, .memory .expiredLifetime (.address ⟨0, 0⟩) 0⟩
theorem witness : invoke Extracted.program 16 0 [] Examples.empty = .error fault := rfl

theorem correctness (fuel : Nat) (result : Memory × List Value) :
    invoke Extracted.program fuel 0 [] Examples.empty ≠ .ok result :=
  invoke_fault_refutes_success _ 16 _ _ _ fault (by decide) witness fuel result
#print axioms correctness
end ExampleProof
