import CIL.Types

/-!
# Wide multiplication

The high word of a full 64-by-64-bit unsigned product, shared by `Math.BigMul` and the
ARM and BMI2 multiply-high intrinsics, so all three agree by definition.
-/

namespace CIL.WideMultiply

/-- The upper 64 bits of the unsigned 128-bit product `left * right`. -/
def high64 (left right : W64) : W64 :=
  BitVec.ofNat 64 (left.toNat * right.toNat / 2^64)

end CIL.WideMultiply
