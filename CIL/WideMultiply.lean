import CIL.Types

/-!
# Wide multiplication

The high word of a full 64-by-64-bit product, unsigned and signed. The unsigned word is
shared by `Math.BigMul` and the ARM and BMI2 multiply-high intrinsics, so all three agree by
definition; the signed word is the result of `Math.BigMul(long, long, out long)`.
-/

namespace CIL.WideMultiply

/-- The upper 64 bits of the unsigned 128-bit product `left * right`. -/
def high64 (left right : W64) : W64 :=
  BitVec.ofNat 64 (left.toNat * right.toNat / 2^64)

/-- The upper 64 bits of the signed 128-bit product `left * right`: its floor by `2^64`. -/
def signedHigh64 (left right : W64) : W64 :=
  BitVec.ofInt 64 (left.toInt * right.toInt / 2^64)

/-- A word's unsigned and signed readings agree modulo `2^64`. -/
theorem toNat_emod_eq_toInt_emod (word : W64) :
    (word.toNat : Int) % 2 ^ 64 = word.toInt % 2 ^ 64 := by
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

/-- The signed high word and the wrapped low word recompose the exact signed product, so
    `signedHigh64` is the signed 128-bit high word with no truncation. -/
theorem signedHigh64_decomposition (left right : W64) :
    (signedHigh64 left right).toInt * 2 ^ 64 + ((left * right).toNat : Int) =
      left.toInt * right.toInt := by
  have bounded (word : W64) : word.toInt.natAbs ≤ 2 ^ 63 := by
    have := BitVec.toInt_lt (x := word)
    have := BitVec.le_toInt (x := word)
    simp only [Nat.reduceSub] at *
    omega
  have low : ((left * right).toNat : Int) = left.toInt * right.toInt % 2 ^ 64 := by
    rw [BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul,
      show ((2 ^ 64 : Nat) : Int) = 2 ^ 64 from rfl, Int.mul_emod, toNat_emod_eq_toInt_emod,
      toNat_emod_eq_toInt_emod, ← Int.mul_emod]
  have magnitude : (left.toInt * right.toInt).natAbs ≤ 2 ^ 126 := by
    rw [Int.natAbs_mul]
    exact Nat.le_trans (Nat.mul_le_mul (bounded left) (bounded right)) (by decide)
  have high : (signedHigh64 left right).toInt = left.toInt * right.toInt / 2 ^ 64 := by
    unfold signedHigh64
    rw [BitVec.toInt_ofInt, Int.bmod_eq_emod]
    split <;> omega
  rw [high, low]
  omega

#print axioms toNat_emod_eq_toInt_emod
#print axioms signedHigh64_decomposition

end CIL.WideMultiply
