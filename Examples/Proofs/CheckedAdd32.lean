import Extracted
import CIL.Safety.SymbolicExecution

open CIL CIL.Safety
namespace ExampleProof

/-- A fitting checked sum preserves arbitrary caller memory and returns the natural-number sum. -/
theorem correctness_framed (memory : CIL.Safety.Memory) (x y : W32)
    (fits : x.toNat + y.toNat < 2^32) :
    invoke Extracted.program 4 0 [.scalar (.i32 x), .scalar (.i32 y)] memory =
      .ok (memory, [.scalar (.i32 (BitVec.ofNat 32 (x.toNat + y.toNat)))]) := by
  cil_checked_steps [checkedValues_add_unsigned_i32 fits]
  rfl

#print axioms correctness_framed

/-- The checked sum equals natural-number addition whenever it fits. -/
theorem correctness (x y : W32) (fits : x.toNat + y.toNat < 2^32) :
    (CIL.Safety.invoke Extracted.program 4 0
      [.scalar (.i32 x), .scalar (.i32 y)] Memory.empty).map Prod.snd =
        .ok [.scalar (.i32 (BitVec.ofNat 32 (x.toNat + y.toNat)))] := by
  exact congrArg (fun result => result.map Prod.snd) (correctness_framed Memory.empty x y fits)

#print axioms correctness
end ExampleProof
