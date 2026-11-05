import CIL.SIMD.Vector

/-!
# SSE2 and SSSE3

Byte shifts, byte alignment, byte shuffles and the widening even-lane multiply on 128-bit vectors.
-/

namespace CIL.Vector

/-- SSSE3 PALIGNR regards the second managed operand as the low half. -/
def ssseAlignBytes (high low : V128) (count : Nat) : V128 :=
  (high ++ low).extractLsb' (8 * count) 128

/-- PSLLDQ: `x` shifted left by `count` bytes, filling with zeros. -/
def sseShiftLeftBytes (x : V128) (count : Nat) : V128 := x <<< (8 * count)

/-- PMULUDQ multiplies the even UInt32 lanes, 0 and 2, and widens each product to UInt64.
https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/X86/Sse2.cs -/
def sseMultiplyEven32 (left right : V128) : V128 :=
  let product (index : Nat) :=
    (lane32 left index).zeroExtend 64 * (lane32 right index).zeroExtend 64
  pack128 (product 0) (product 2)

/-- PSHUFB: byte `i` is zero when bit 7 of control byte `i` is set, else the source byte its
    low four bits select. -/
def shuffleBytes128 (source control : V128) : V128 :=
  (List.range 16).foldl (fun result index =>
    let selector := lane8 control index
    let byte := if selector.msb then 0 else lane8 source (selector.extractLsb' 0 4).toNat
    result ||| (byte.zeroExtend 128 <<< (8 * index))) 0

end CIL.Vector
