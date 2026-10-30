import Extracted
import Examples.Support
import CIL.Safety.SymbolicExecution
import CIL.Safety.WideMultiply

namespace ExampleProof
open CIL.Safety

/-- The emitted runtime call writes the low limb and returns the high limb.
    The caller supplies only a valid destination and the checked write relation. -/
theorem correctness (memory result : Memory) (reference : Reference) (left right : CIL.W64)
    (formed : form memory reference = .ok reference)
    (stored : write memory reference (numberBytes (left * right).toNat 8) 1 = .ok result) :
    invoke Extracted.program 8 0 [.scalar (.i64 left), .scalar (.i64 right), .reference (.address reference)] memory =
      .ok (result, [.scalar (.i64 (CIL.WideMultiply.high64 left right))]) := by
  have wrote : storeValue memory (.address reference) (.i64 (left * right)) = .ok result := by
    simp only [storeValue, CIL.Value.hasUnspecified, Bool.false_eq_true, ↓reduceIte,
      referenceAt, checkedAt, stored, Except.mapError,
      Bind.bind, Except.bind]
  cil_checked_steps [formed, wrote]

end ExampleProof
