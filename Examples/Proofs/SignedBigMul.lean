import Extracted
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
  cil_checked_steps [formed, step_bigMul64_signed_of_write stored]

#print axioms correctness
end ExampleProof
