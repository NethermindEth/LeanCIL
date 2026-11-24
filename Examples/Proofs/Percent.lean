import Extracted
import CIL.Safety.RuntimeExceptions
import CIL.Safety.LiteralImage

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

/-- The two original literal operands are live string references after loading the extracted
image. Every input above 100 then raises the contract's exception, with zero caller heap quota. -/
theorem loadedException :
    let methods := Extracted.methodEvidence.map (·.original)
    ∃ initial name message first second,
      LiteralImage.initialMemory methods (some 0) = .ok initial ∧
      LiteralImage.operands methods = [name, message] ∧ initial.heapBudget = some 0 ∧
      literalObject initial name = .ok (.object (.address first)) ∧
      literalObject initial message = .ok (.object (.address second)) ∧
      ∀ value : W32, 100 < value →
        RaisesCLR Extracted.program 0 [.scalar (.i32 value)] initial .argumentOutOfRange := by
  let methods := Extracted.methodEvidence.map (·.original)
  let initial := (LiteralImage.initialMemory methods (some 0)).toOption.getD Memory.empty
  let operands := LiteralImage.operands methods
  let name := operands[0]?.getD ""
  let message := operands[1]?.getD ""
  let first := (initial.literals.lookup name).getD ⟨0, 0⟩
  let second := (initial.literals.lookup message).getD ⟨0, 0⟩
  refine ⟨initial, name, message, first, second, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (dsimp only [initial, methods, name, message, operands, first, second]; cil_kernel_rfl)
  intro value outside
  exact correctness.raising (input := value) trivial
    (by simp only [contract, ite_eq_right (BitVec.not_le.mpr outside)])
#print axioms loadedException

end ExampleProof
