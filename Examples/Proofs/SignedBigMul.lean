import Extracted
import Examples.Support
import CIL.Safety.SymbolicExecution
import CIL.Safety.WideMultiply

/-!
# Signed BigMul contract

`Math.BigMul(long, long, out long)` writes the low word and returns the signed high word, and
the two recompose the exact signed 128-bit product.
-/

namespace ExampleProof
open CIL.Safety

/-- The emitted runtime call writes the low limb and returns the signed high limb, whose
    signed reading with the low limb is exactly `left * right` over `Int`. -/
theorem correctness (memory result : Memory) (reference : Reference) (left right : CIL.W64)
    (formed : form memory reference = .ok reference)
    (stored : write memory reference (numberBytes (left * right).toNat 8) 1 = .ok result) :
    invoke Extracted.program 8 0
        [.scalar (.i64 left), .scalar (.i64 right), .reference (.address reference)] memory =
      .ok (result, [.scalar (.i64 (CIL.WideMultiply.signedHigh64 left right))]) ∧
    (CIL.WideMultiply.signedHigh64 left right).toInt * 2 ^ 64 + ((left * right).toNat : Int) =
      left.toInt * right.toInt := by
  refine ⟨?_, CIL.WideMultiply.signedHigh64_decomposition left right⟩
  have wrote : storeValue memory (.address reference) (.i64 (left * right)) = .ok result := by
    simp only [storeValue, CIL.Value.hasUnspecified, Bool.false_eq_true, ↓reduceIte,
      referenceAt, checkedAt, stored, Except.mapError,
      Bind.bind, Except.bind]
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, formed, instruction,
    staticInstruction, memoryInstruction, wideArithmeticInstruction,
    observerCount, CIL.MemoryOp.argumentCount, unspecifiedOperands,
    Value.hasUnspecified, CIL.Value.hasUnspecified,
    wrote, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms correctness
end ExampleProof
