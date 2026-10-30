import CIL.SIMD.SSE

/-!
# AVX2

Lane multiplication, permutation, blending and byte shuffles on 256-bit vectors.
-/

namespace CIL.Vector

/-- VPMULUDQ multiplies the even UInt32 lanes and widens each product to UInt64.
https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/X86/Avx2.cs -/
def multiplyEven32 (left right : V256) : V256 :=
  let product (index : Nat) :=
    (lane32 left index).zeroExtend 64 * (lane32 right index).zeroExtend 64
  pack256 (product 0) (product 2) (product 4) (product 6)

/-- VPERMQ: 64-bit lane `i` of the result is the lane of `x` selected by bits `2i` and
    `2i + 1` of `control`. -/
def permute4x64 (x : V256) (control : BitVec 8) : V256 :=
  pack256 (lane64 x ((control.extractLsb' 0 2).toNat))
    (lane64 x ((control.extractLsb' 2 2).toNat))
    (lane64 x ((control.extractLsb' 4 2).toNat))
    (lane64 x ((control.extractLsb' 6 2).toNat))

/-- VPBLENDD: 32-bit lane `i` comes from `b` when bit `i` of `control` is set, else from `a`. -/
def blend32 (a b : V256) (control : BitVec 8) : V256 :=
  let lane := fun i => if control.getLsbD i then lane32 b i else lane32 a i
  ((lane 7 ++ lane 6) ++ (lane 5 ++ lane 4)) ++
    ((lane 3 ++ lane 2) ++ (lane 1 ++ lane 0))

/-- VPSHUFB: PSHUFB on each 128-bit half, so no byte crosses between the halves. -/
def shuffleBytes256 (source control : V256) : V256 :=
  shuffleBytes128 (source.extractLsb' 128 128) (control.extractLsb' 128 128) ++
    shuffleBytes128 (source.extractLsb' 0 128) (control.extractLsb' 0 128)

end CIL.Vector
