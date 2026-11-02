import CIL.SIMD.Vector

/-!
# AVX-512

Lane alignment, three-input bitwise logic and the two-table quadword permutation on 256-bit
vectors (AVX-512F with VL).
-/

namespace CIL.Vector

/-- VALIGNQ's immediate is masked to the lane-count minus one. -/
def alignRight64 (high low : V256) (count : Nat) : V256 :=
  (high ++ low).extractLsb' (64 * (count % 4)) 256

/-- Intel truth-table index is 4*a + 2*b + c at each bit position. -/
def ternaryLogic (a b c : BitVec n) (control : BitVec 8) : BitVec n :=
  (List.range 8).foldl (fun acc i =>
    if control.getLsbD i then
      acc ||| ((if i.testBit 2 then a else ~~~a) &&&
        (if i.testBit 1 then b else ~~~b) &&& (if i.testBit 0 then c else ~~~c))
    else acc) 0

/-- One lane of the 256-bit VPERMI2Q/VPERMT2Q: bits 1:0 of `index` pick a lane and bit 2 picks
    the table, `lower` when clear; the higher index bits are ignored. -/
def permuteLane4x64x2 (lower upper : V256) (index : W64) : W64 :=
  lane64 (if index.getLsbD 2 then upper else lower) (index.toNat % 4)

/-- `Avx512F.VL.PermuteVar4x64x2(lower, indices, upper)`: each result lane is the quadword of
    the eight-lane table `upper:lower` that the same lane of `indices` selects. -/
def permuteVar4x64x2 (lower indices upper : V256) : V256 :=
  map256 (permuteLane4x64x2 lower upper) indices

end CIL.Vector
