import Extracted
import Examples.Support
import CIL.Safety.SymbolicExecution
import CIL.Safety.TupleDivision

/-!
# Math.DivRem quotient contract

`Math.DivRem(left, right).Quotient` on `int` is the truncated quotient, and the call raises
exactly the faults of CIL `div`: `DivideByZeroException` for a zero divisor and
`OverflowException` for `int.MinValue / -1`.
-/

namespace ExampleProof
open CIL CIL.Safety

/-- The two `int` arguments as stack values. -/
def inputs (left right : W32) : List CIL.Safety.Value := [.scalar (.i32 left), .scalar (.i32 right)]

/-- `Math.DivRem(left, right).Quotient` returns the exact truncated quotient whenever `div`
    succeeds, and otherwise raises its divide-by-zero or overflow fault. -/
theorem correctness (left right : W32) :
    (right ≠ 0 → (left ≠ BitVec.intMin 32 ∨ right ≠ -1) → ∃ quotient : W32,
      (invoke Extracted.program 8 0 (inputs left right) Examples.empty).map Prod.snd =
        .ok [.scalar (.i32 quotient)] ∧
      quotient.toInt = left.toInt.tdiv right.toInt) ∧
    invoke Extracted.program 8 0 (inputs left 0) Examples.empty =
      .error ⟨0, 2, .arithmetic .divideByZero⟩ ∧
    invoke Extracted.program 8 0 (inputs (BitVec.intMin 32) (-1)) Examples.empty =
      .error ⟨0, 2, .arithmetic .overflow⟩ := by
  refine ⟨fun nonzero representable => ?_, ?_, ?_⟩
  · obtain ⟨evaluated, exact, -⟩ := divRemBits_signed (by decide) nonzero representable
    refine ⟨left.sdiv right, ?_, exact⟩
    have returned : invoke Extracted.program 8 0 (inputs left right) Examples.empty =
        .ok (Examples.empty, [.scalar (.i32 (left.sdiv right))]) := by
      cil_checked_steps [inputs, mathDivRem32_eq, evaluated, item1_of_int_tuple]
    rw [returned]
    rfl
  · cil_checked_steps [inputs, mathDivRem32_eq, divRemBits_zero true left]
  · cil_checked_steps [inputs, mathDivRem32_eq, divRemBits_overflow (width := 32) (by decide)]

#print axioms correctness
end ExampleProof
