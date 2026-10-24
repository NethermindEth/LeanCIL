import CIL.SIMD.Vector

/-!
# SSE2 and SSSE3

Byte shifts and byte alignment across 128-bit vectors.
-/

namespace CIL.Vector

/-- SSSE3 PALIGNR regards the second managed operand as the low half. -/
def ssseAlignBytes (high low : V128) (count : Nat) : V128 :=
  (high ++ low).extractLsb' (8 * count) 128

/-- PSLLDQ: `x` shifted left by `count` bytes, filling with zeros. -/
def sseShiftLeftBytes (x : V128) (count : Nat) : V128 := x <<< (8 * count)

end CIL.Vector
