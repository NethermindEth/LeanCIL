import CIL.Types

/-!
# Vector model

Vectors are bit vectors; lane `i` of width `w` is bits `w*i` to `w*i + w - 1`, so lane zero
is the lowest-addressed element in little-endian memory. Lanewise operations are written
with `pack`, `map` and `zip` over 64-bit lanes, and the lane lemmas in `VectorLemmas`
reduce them back to scalar operations.
-/

namespace CIL.Vector

/-- A 128-bit vector. -/
abbrev V128 := BitVec 128
/-- A 256-bit vector. -/
abbrev V256 := BitVec 256
/-- A 512-bit vector. -/
abbrev V512 := BitVec 512

/-- Lane zero occupies the least significant bits, matching little-endian byte memory. -/
def lane64 (x : BitVec n) (i : Nat) : W64 := x.extractLsb' (64 * i) 64
/-- 32-bit lane `i`, lane zero least significant. -/
def lane32 (x : BitVec n) (i : Nat) : W32 := x.extractLsb' (32 * i) 32
/-- The 128-bit vector with 64-bit lanes `a0` and `a1`, `a0` lowest. -/
def pack128 (a0 a1 : W64) : V128 := a1 ++ a0
/-- The 256-bit vector with 64-bit lanes `a0` to `a3`, `a0` lowest. -/
def pack256 (a0 a1 a2 a3 : W64) : V256 := (a3 ++ a2) ++ (a1 ++ a0)

/-- `f` applied to each 64-bit lane. -/
def map128 (f : W64 → W64) (x : V128) : V128 :=
  pack128 (f (lane64 x 0)) (f (lane64 x 1))
/-- `f` applied to each 64-bit lane. -/
def map256 (f : W64 → W64) (x : V256) : V256 :=
  pack256 (f (lane64 x 0)) (f (lane64 x 1)) (f (lane64 x 2)) (f (lane64 x 3))
/-- `f` applied to corresponding 64-bit lanes of `x` and `y`. -/
def zip128 (f : W64 → W64 → W64) (x y : V128) : V128 :=
  pack128 (f (lane64 x 0) (lane64 y 0)) (f (lane64 x 1) (lane64 y 1))
/-- `f` applied to corresponding 64-bit lanes of `x` and `y`. -/
def zip256 (f : W64 → W64 → W64) (x y : V256) : V256 :=
  pack256 (f (lane64 x 0) (lane64 y 0)) (f (lane64 x 1) (lane64 y 1))
    (f (lane64 x 2) (lane64 y 2)) (f (lane64 x 3) (lane64 y 3))

/-- The 512-bit vector with 64-bit lanes `a0` to `a7`, `a0` lowest. -/
def pack512 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) : V512 :=
  pack256 a4 a5 a6 a7 ++ pack256 a0 a1 a2 a3

/-- `f` applied to corresponding 64-bit lanes of `x` and `y`. -/
def zip512 (f : W64 → W64 → W64) (x y : V512) : V512 :=
  pack512 (f (lane64 x 0) (lane64 y 0)) (f (lane64 x 1) (lane64 y 1))
    (f (lane64 x 2) (lane64 y 2)) (f (lane64 x 3) (lane64 y 3))
    (f (lane64 x 4) (lane64 y 4)) (f (lane64 x 5) (lane64 y 5))
    (f (lane64 x 6) (lane64 y 6)) (f (lane64 x 7) (lane64 y 7))

/-- Each 64-bit lane shifted left by `count`; a count of 64 or more clears every lane. -/
def shiftLeftCount64 (value : V256) (count : W64) : V256 :=
  if count.toNat >= 64 then 0 else map256 (· <<< count.toNat) value

/-- Each 64-bit lane shifted right logically by `count`; a count of 64 or more clears every
    lane. -/
def shiftRightCount64 (value : V256) (count : W64) : V256 :=
  if count.toNat >= 64 then 0 else map256 (· >>> count.toNat) value

/-- Bit `i` is the sign bit of 64-bit lane `i`; the other bits are zero. -/
def moveMask512 (value : V512) : W32 :=
  (List.range 8).foldl (fun result index =>
    result ||| (BitVec.ofNat 32 (if (lane64 value index).msb then 1 else 0) <<< index)) 0

/-- All ones for true and zero for false: a lanewise comparison result. -/
def mask64 (p : Bool) : W64 := if p then ~~~(0 : W64) else 0
/-- A bit-pattern reinterpretation, which leaves the bits unchanged. -/
def reinterpret (x : BitVec n) : BitVec n := x

end CIL.Vector
