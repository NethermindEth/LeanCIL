import Extracted
import Examples.Support
import CIL.Safety.SymbolicExecution
import CIL.Safety.TupleDivision

/-!
# X86Base.X64.DivRem quotient contract

`X86Base.X64.DivRem(lower, upper, divisor).Quotient` is the natural quotient of the 128-bit
dividend `upper:lower` when it fits in 64 bits, and the divide error otherwise.
-/

namespace ExampleProof
open CIL CIL.Safety

/-- The dividend's low and high words and the divisor as stack values. -/
def inputs (lower upper divisor : W64) : List CIL.Safety.Value :=
  [.scalar (.i64 lower), .scalar (.i64 upper), .scalar (.i64 divisor)]

/-- `DivRem(lower, upper, divisor).Quotient` is the natural quotient when it fits, and faults
    otherwise. -/
theorem correctness (lower upper divisor : W64) :
    (upper.toNat < divisor.toNat → ∃ quotient : W64,
      (invoke Extracted.program 8 0 (inputs lower upper divisor) Examples.empty).map Prod.snd =
        .ok [.scalar (.i64 quotient)] ∧
      quotient.toNat = (upper.toNat * 2 ^ 64 + lower.toNat) / divisor.toNat) ∧
    (divisor.toNat ≤ upper.toNat →
      invoke Extracted.program 8 0 (inputs lower upper divisor) Examples.empty =
        .error ⟨0, 3, .arithmetic (if divisor = 0 then .divideByZero else .overflow)⟩) := by
  refine ⟨fun fits => ?_, fun overflows => ?_⟩
  · obtain ⟨quotient, remainder, evaluated, -, -, exact, -⟩ :=
      divRem_fields (lower := lower) fits [] Examples.empty
    refine ⟨quotient, ?_, exact⟩
    have returned : invoke Extracted.program 8 0 (inputs lower upper divisor) Examples.empty =
        .ok (Examples.empty, [.scalar (.i64 quotient)]) := by
      cil_checked_steps [inputs, evaluated, item1_of_tuple]
    rw [returned]
    rfl
  · cil_checked_steps [inputs, divRem_fault (lower := lower) overflows]

#print axioms correctness
end ExampleProof
