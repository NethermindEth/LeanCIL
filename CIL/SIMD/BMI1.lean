import CIL.SIMD.Vector

/-!
# BMI1

Bit-field extraction (`BitFieldExtract`).
-/

namespace CIL.Vector

/-- BEXTR: `length` bits of `x` starting at bit `start`, zero-extended; a field running past
    bit 31 is cut off, and a start of 32 or more gives zero. -/
def bextr32 (x : W32) (start length : Nat) : W32 :=
  if start ≥ 32 then 0 else
    (x >>> start) &&& (BitVec.ofNat 32 (2 ^ (min length (32 - start)) - 1))

end CIL.Vector
