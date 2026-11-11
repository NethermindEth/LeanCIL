import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.WideMultiply

namespace ExampleProof
open CIL.Safety

/-- The emitted runtime call writes the low limb and returns the high limb.
    The caller supplies only a valid destination and the checked write relation. -/
theorem correctness (memory result : Memory) (reference : Reference) (left right : CIL.W64)
    (formed : form memory reference = .ok reference)
    (stored : write memory reference (numberBytes (left * right).toNat 8) 1 = .ok result) :
    invoke Extracted.program 8 0
        [.scalar (.i64 left), .scalar (.i64 right), .reference (.address reference)] memory =
      .ok (result, [.scalar (.i64 (CIL.WideMultiply.high64 left right))]) := by
  cil_checked_steps [formed, step_bigMul64_of_write stored]

#print axioms correctness
end ExampleProof
