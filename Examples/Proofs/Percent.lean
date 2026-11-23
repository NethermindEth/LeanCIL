import Extracted
import CIL.Safety.RuntimeExceptions

/-! The checked CLR contract for `Examples.Throws.Percent(uint)` at every unsigned input. -/

namespace ExampleProof
open CIL CIL.Safety

/-- Inputs through 100 return unchanged. Larger inputs raise `ArgumentOutOfRangeException`. -/
def contract : OutcomeContract W32 W32 where
  args value := [.scalar (.i32 value)]
  results result := [.scalar (.i32 result)]
  pre _ _ := True
  footprint _ := []
  post value _ _ result := result = value
  raises value _ := if value ≤ 100 then none else some .argumentOutOfRange

/-- The compiled method satisfies the contract from any caller memory. -/
theorem correctness : contract.HoldsCLR Extracted.program 0 := by
  apply OutcomeContract.Holds.clr
  intro value memory _
  by_cases within : value ≤ 100
  · have bound : value ≤ 100#32 := within
    simp only [contract, within, ite_true]
    cil_contract_steps [bound]
    exact ⟨Confined.refl _ memory, _, rfl, rfl⟩
  · have bound : ¬ value ≤ 100#32 := within
    simp only [contract, within, ite_false]
    cil_raise_steps [bound]

#print axioms correctness
end ExampleProof
