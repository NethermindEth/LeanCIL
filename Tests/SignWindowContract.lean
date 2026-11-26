import CIL.Safety.MethodContract
import CIL.SIMD.PackedLanes

/-! The arithmetic sign window selects each output lane from four source limbs or their sign fill. -/

namespace Tests.SignWindowContract
open CIL (W64)
open CIL.Vector
open CIL.Safety

/-- Four quadwords in least-significant-lane order. -/
structure Limbs where
  a : W64
  b : W64
  c : W64
  d : W64

/-- The sign extension uses the high limb. Bits 1:0 of an index select a limb
    and bit 2 selects the sign extension. Higher index bits have no effect. -/
def selected (value : Limbs) (index : W64) : W64 :=
  if index.getLsbD 2 then mask64 (value.d.slt 0)
  else lane64 (pack256 value.a value.b value.c value.d) (index.toNat % 4)

/-- The public entry returns four selected limbs and preserves all caller memory. -/
def signWindow : MethodContract (Limbs × Limbs) V256 where
  args | (v, i) => [.scalar (.i64 v.a), .scalar (.i64 v.b), .scalar (.i64 v.c),
    .scalar (.i64 v.d), .scalar (.i64 i.a), .scalar (.i64 i.b),
    .scalar (.i64 i.c), .scalar (.i64 i.d)]
  results value := [.scalar (.v256 value)]
  pre _ memory := memory.WellFormed
  footprint _ := []
  post input _ _ result :=
    let (v, i) := input
    result = pack256 (selected v i.a) (selected v i.b) (selected v i.c) (selected v i.d)

/-- Each of the four lanes of the sign-fill table contains the same word. -/
private theorem select_fill (v : Limbs) (index : W64) :
    let fill := mask64 (v.d.slt 0)
    permuteLane4x64x2 (pack256 v.a v.b v.c v.d) (pack256 fill fill fill fill) index =
      selected v index := by
  simp only [permuteLane4x64x2, selected]
  split
  · have bound := Nat.mod_lt index.toNat (by decide : 0 < 4)
    have cases : index.toNat % 4 = 0 ∨ index.toNat % 4 = 1 ∨
        index.toNat % 4 = 2 ∨ index.toNat % 4 = 3 := by omega
    rcases cases with h | h | h | h <;> simp [h]
  · rfl
#print axioms select_fill

/-- The sign broadcast takes lane three of the comparison with zero. -/
private theorem fill_high (v : Limbs) :
    permute4x64 (zip256 (fun x y => mask64 (x.slt y)) (pack256 v.a v.b v.c v.d) 0) 255 =
      let fill := mask64 (v.d.slt 0)
      pack256 fill fill fill fill := by
  change permute4x64 (zip256 _ _ (pack256 0 0 0 0)) _ = _
  rw [zip256_pack256]
  simp [permute4x64]
#print axioms fill_high

/-- The indexed permutation of the computed sign-fill table returns all four selected limbs. -/
theorem signWindow_result (v i : Limbs) :
    let value := pack256 v.a v.b v.c v.d
    let fill := permute4x64 (zip256 (fun x y => mask64 (x.slt y)) value 0) 255
    permuteVar4x64x2 value (pack256 i.a i.b i.c i.d) fill =
      pack256 (selected v i.a) (selected v i.b) (selected v i.c) (selected v i.d) := by
  simp only [fill_high, permuteVar4x64x2, map256_pack256, select_fill]
#print axioms signWindow_result

end Tests.SignWindowContract
