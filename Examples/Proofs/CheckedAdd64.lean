import Extracted
import CIL.Safety.SymbolicExecution

open CIL CIL.Safety
namespace ExampleProof

/-- The checked sum equals natural-number addition whenever it fits. -/
theorem correctness (memory : CIL.Safety.Memory) (x y : W64) (fits : x.toNat + y.toNat < 2^64) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0
      [.scalar (.i64 x), .scalar (.i64 y)] memory =
        .ok (memory, [.scalar (.i64 (BitVec.ofNat 64 (x.toNat + y.toNat)))]) := by
  cil_checked_steps [checkedValues_add_unsigned_i64 fits]
  rfl

#print axioms correctness
end ExampleProof