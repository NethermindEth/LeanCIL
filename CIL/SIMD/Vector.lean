import CIL.Types

namespace CIL.Vector

abbrev V128 := BitVec 128
abbrev V256 := BitVec 256
abbrev V512 := BitVec 512

/-- Lane zero occupies the least significant bits, matching little-endian byte memory. -/
def lane64 (x : BitVec n) (i : Nat) : W64 := x.extractLsb' (64 * i) 64
def lane32 (x : BitVec n) (i : Nat) : W32 := x.extractLsb' (32 * i) 32
def pack128 (a0 a1 : W64) : V128 := a1 ++ a0
def pack256 (a0 a1 a2 a3 : W64) : V256 := (a3 ++ a2) ++ (a1 ++ a0)

def map128 (f : W64 → W64) (x : V128) : V128 :=
  pack128 (f (lane64 x 0)) (f (lane64 x 1))
def map256 (f : W64 → W64) (x : V256) : V256 :=
  pack256 (f (lane64 x 0)) (f (lane64 x 1)) (f (lane64 x 2)) (f (lane64 x 3))
def zip128 (f : W64 → W64 → W64) (x y : V128) : V128 :=
  pack128 (f (lane64 x 0) (lane64 y 0)) (f (lane64 x 1) (lane64 y 1))
def zip256 (f : W64 → W64 → W64) (x y : V256) : V256 :=
  pack256 (f (lane64 x 0) (lane64 y 0)) (f (lane64 x 1) (lane64 y 1))
    (f (lane64 x 2) (lane64 y 2)) (f (lane64 x 3) (lane64 y 3))

def pack512 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) : V512 :=
  pack256 a4 a5 a6 a7 ++ pack256 a0 a1 a2 a3

def zip512 (f : W64 → W64 → W64) (x y : V512) : V512 :=
  pack512 (f (lane64 x 0) (lane64 y 0)) (f (lane64 x 1) (lane64 y 1))
    (f (lane64 x 2) (lane64 y 2)) (f (lane64 x 3) (lane64 y 3))
    (f (lane64 x 4) (lane64 y 4)) (f (lane64 x 5) (lane64 y 5))
    (f (lane64 x 6) (lane64 y 6)) (f (lane64 x 7) (lane64 y 7))

def shiftLeftCount64 (value : V256) (count : W64) : V256 :=
  if count.toNat >= 64 then 0 else map256 (· <<< count.toNat) value

def shiftRightCount64 (value : V256) (count : W64) : V256 :=
  if count.toNat >= 64 then 0 else map256 (· >>> count.toNat) value

def moveMask512 (value : V512) : W32 :=
  (List.range 8).foldl (fun result index =>
    result ||| (BitVec.ofNat 32 (if (lane64 value index).msb then 1 else 0) <<< index)) 0

def mask64 (p : Bool) : W64 := if p then ~~~(0 : W64) else 0
def reinterpret (x : BitVec n) : BitVec n := x

end CIL.Vector
