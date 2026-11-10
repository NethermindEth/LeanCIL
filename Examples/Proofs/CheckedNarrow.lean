import Extracted
import CIL.Safety.SymbolicExecution

open CIL CIL.Safety
namespace ExampleProof

/-- A checked narrowing conversion preserves every representable natural value. -/
theorem correctness (x : W64) (fits : x.toNat < 2^32) :
    (CIL.Safety.invoke Extracted.program 3 0 [.scalar (.i64 x)] Memory.empty).map Prod.snd =
      .ok [.scalar (.i32 (BitVec.ofNat 32 x.toNat))] := by
  have range : 0 ≤ (x.toNat : Int) ∧ (x.toNat : Int) < 2^32 := by omega
  have calculation : convertInteger 32 false true (.i64 x) =
      .ok (.i32 (BitVec.ofNat 32 x.toNat)) := by
    simp only [convertInteger,
      show (32 != 8 && 32 != 16 && 32 != 32 && 32 != 64) = false from rfl,
      Bool.false_eq_true, ite_false, ite_true]
    simp only [convertNumber, Bool.false_eq_true, ite_false]
    rw [ite_eq_left range]
    rfl
  have ran : CIL.Safety.invoke Extracted.program 3 0 [.scalar (.i64 x)] Memory.empty =
      .ok (Memory.empty, [.scalar (.i32 (BitVec.ofNat 32 x.toNat))]) := by
    cil_checked_steps [calculation]
  rw [ran]
  rfl

#print axioms correctness
end ExampleProof
