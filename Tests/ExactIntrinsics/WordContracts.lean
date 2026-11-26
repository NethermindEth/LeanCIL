import CIL.Safety.MethodContract

/-! Contracts for comparing four words to a vector and packing eight words in lane order. -/

namespace Tests.ExactIntrinsics.WordContracts
open CIL (W32)
open CIL.Safety

/-- Four 32-bit words and the vector to compare against. -/
structure Comparison where
  a : W32
  b : W32
  c : W32
  d : W32
  expected : BitVec 128

/-- The comparison packs the four words in lane order and preserves caller memory. -/
def equalWords : MethodContract Comparison Bool where
  args w := [.scalar (.i32 w.a), .scalar (.i32 w.b), .scalar (.i32 w.c), .scalar (.i32 w.d),
    .scalar (.v128 w.expected)]
  results equal := [.scalar (.i32 (if equal then 1 else 0))]
  pre _ _ := True
  footprint _ := []
  post w before after equal := after = before ∧
    equal = (((w.d ++ w.c) ++ (w.b ++ w.a)) == w.expected)

/-- The eight input words in argument order. -/
structure Words where
  a : W32
  b : W32
  c : W32
  d : W32
  e : W32
  f : W32
  g : W32
  h : W32

/-- Lane zero contains the first word, and lane seven contains the last. -/
def lanes (w : Words) : BitVec 256 :=
  ((w.h ++ w.g) ++ (w.f ++ w.e)) ++ ((w.d ++ w.c) ++ (w.b ++ w.a))

/-- Creating the vector packs all eight words and preserves caller memory. -/
def createWords : MethodContract Words (BitVec 256) where
  args w := [.scalar (.i32 w.a), .scalar (.i32 w.b), .scalar (.i32 w.c), .scalar (.i32 w.d),
    .scalar (.i32 w.e), .scalar (.i32 w.f), .scalar (.i32 w.g), .scalar (.i32 w.h)]
  results v := [.scalar (.v256 v)]
  pre _ _ := True
  footprint _ := []
  post w before after v := after = before ∧ v = lanes w

end Tests.ExactIntrinsics.WordContracts
