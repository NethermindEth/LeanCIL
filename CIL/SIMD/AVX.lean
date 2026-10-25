import CIL.SIMD.Vector

/-!
# AVX

Sign-mask extraction from 256-bit vectors (`MoveMask`).
-/

namespace CIL.Vector

/-- Bit `i` is the sign bit of 64-bit lane `i`; the other bits are zero. -/
def moveMask64 (x : V256) : W32 :=
  (List.range 4).foldl (fun acc i =>
    acc ||| (BitVec.ofNat 32 (if (lane64 x i).msb then 1 else 0) <<< i)) 0

/-- Bit `i` is the sign bit of 32-bit lane `i`; the other bits are zero. -/
def moveMask32 (x : V256) : W32 :=
  (List.range 8).foldl (fun acc i =>
    acc ||| (BitVec.ofNat 32 (if (lane32 x i).msb then 1 else 0) <<< i)) 0

end CIL.Vector
