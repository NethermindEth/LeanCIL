import Extracted
import Examples.Support

/-!
# BigMul(int, int) contract

`Math.BigMul(int, int)` returns the exact signed 64-bit product: the result is never wrapped.
-/

namespace ExampleProof
open CIL.Safety

/-- The call returns `left * right` as a `long`, and its signed reading is the `Int` product. -/
theorem correctness (left right : CIL.W32) :
    (invoke Extracted.program 8 0 [.scalar (.i32 left), .scalar (.i32 right)] Examples.empty).map
        Prod.snd = .ok [.scalar (.i64 (BitVec.ofInt 64 (left.toInt * right.toInt)))] ∧
    (BitVec.ofInt 64 (left.toInt * right.toInt)).toInt = left.toInt * right.toInt := by
  refine ⟨rfl, ?_⟩
  have bounded (word : CIL.W32) : word.toInt.natAbs ≤ 2 ^ 31 := by
    have := BitVec.toInt_lt (x := word)
    have := BitVec.le_toInt (x := word)
    simp only [Nat.reduceSub] at *
    omega
  have magnitude : (left.toInt * right.toInt).natAbs ≤ 2 ^ 62 := by
    rw [Int.natAbs_mul]
    exact Nat.le_trans (Nat.mul_le_mul (bounded left) (bounded right)) (by decide)
  rw [BitVec.toInt_ofInt, Int.bmod_eq_emod]
  split <;> omega

#print axioms correctness
end ExampleProof
