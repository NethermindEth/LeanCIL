import CIL.SIMD.Vector
import CIL.ScalarIntrinsics

/-!
# ARM AdvSimd

The `EXT` lane extraction across two 128-bit vectors, and the `REV64` byte reversal within
each 64-bit lane.
-/

namespace CIL.Vector

/-- ARM EXT regards the first operand as the low half of the concatenation. -/
def advExtract64 (low high : V128) (index : Nat) : V128 :=
  (high ++ low).extractLsb' (64 * index) 128

/-- REV64 on byte elements: each 64-bit lane is byte-reversed in place, as
    `BinaryPrimitives.ReverseEndianness` reverses a `ulong`; the lanes do not move. -/
def reverseElement8 (value : V128) : V128 := map128 reverseBytes value

end CIL.Vector
