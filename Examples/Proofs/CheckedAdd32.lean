import Extracted
import CIL.Safety.SymbolicExecution

open CIL CIL.Safety
namespace ExampleProof

/-- The checked sum equals natural-number addition whenever it fits. -/
theorem correctness (x y : W32) (fits : x.toNat + y.toNat < 2^32) :
    (CIL.Safety.invoke Extracted.program 4 0
      [.scalar (.i32 x), .scalar (.i32 y)] Memory.empty).map Prod.snd =
        .ok [.scalar (.i32 (BitVec.ofNat 32 (x.toNat + y.toNat)))] := by
  have ran : CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i32 x), .scalar (.i32 y)]
      Memory.empty = .ok (Memory.empty, [.scalar (.i32 (x + y))]) := by
    cil_checked_steps [checkedValues_add_unsigned_i32 fits]
  rw [ran]
  rfl

#print axioms correctness
end ExampleProof