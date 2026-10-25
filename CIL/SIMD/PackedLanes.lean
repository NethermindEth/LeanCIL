import CIL.SIMD.Evaluation256Lemmas
import CIL.SIMD.LaneCarry

/-!
# Packed-lane lemmas for integer intrinsics

Lane forms of the integer intrinsics: lane projections of `pack512`, of bitwise operations, of
lanewise maps and zips and of count shifts; lanewise maps and zips of `pack128` and `pack256`;
the numeric value of a packed vector; `moveMask64` as sign bits, the exact products
of `multiplyEven32`, `permute4x64`, shifts by immediate, `sum64` and the AVX-512DQ `mul64`.
On top of `LaneCarry` they give the carry and borrow repair of a wide addition or subtraction
done lane by lane, in the shapes that stepping `evalIntrinsic` produces.

Only the `pack512` lane projections are `@[simp]`, like the `pack128` and `pack256` ones in
`VectorLemmas`; consumers rewrite with the rest explicitly.
-/

open CIL

namespace CIL.Vector

/-! ### Lanewise operations on packed lanes -/

/-- A lanewise operation on packed lanes applies to each lane. -/
theorem zip256_pack256 (f : W64 → W64 → W64) (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    zip256 f (pack256 a0 a1 a2 a3) (pack256 b0 b1 b2 b3) =
      pack256 (f a0 b0) (f a1 b1) (f a2 b2) (f a3 b3) := by
  simp only [zip256, lane256_0, lane256_1, lane256_2, lane256_3]
#print axioms zip256_pack256

/-- A lanewise map on packed lanes applies to each lane. -/
theorem map256_pack256 (f : W64 → W64) (a0 a1 a2 a3 : W64) :
    map256 f (pack256 a0 a1 a2 a3) = pack256 (f a0) (f a1) (f a2) (f a3) := by
  simp only [map256, lane256_0, lane256_1, lane256_2, lane256_3]
#print axioms map256_pack256

/-- A lanewise operation on packed lanes applies to each lane. -/
theorem zip128_pack128 (f : W64 → W64 → W64) (a0 a1 b0 b1 : W64) :
    zip128 f (pack128 a0 a1) (pack128 b0 b1) = pack128 (f a0 b0) (f a1 b1) := by
  simp only [zip128, lane128_0, lane128_1]
#print axioms zip128_pack128

/-- A lanewise map on packed lanes applies to each lane. -/
theorem map128_pack128 (f : W64 → W64) (a0 a1 : W64) :
    map128 f (pack128 a0 a1) = pack128 (f a0) (f a1) := by
  simp only [map128, lane128_0, lane128_1]
#print axioms map128_pack128

/-- Two 256-bit vectors are equal when their four 64-bit lanes are. -/
theorem eq_of_lane64_eq256 {x y : V256} (lanes : ∀ i < 4, lane64 x i = lane64 y i) : x = y := by
  rw [← pack256_lanes x, ← pack256_lanes y, lanes 0 (by decide), lanes 1 (by decide),
    lanes 2 (by decide), lanes 3 (by decide)]
#print axioms eq_of_lane64_eq256

/-- Two 128-bit vectors are equal when their two 64-bit lanes are. -/
theorem eq_of_lane64_eq128 {x y : V128} (lanes : ∀ i < 2, lane64 x i = lane64 y i) : x = y := by
  rw [← pack128_lanes x, ← pack128_lanes y, lanes 0 (by decide), lanes 1 (by decide)]
#print axioms eq_of_lane64_eq128

/-- Lane `i` of a lanewise operation is the operation on lane `i`. -/
theorem lane64_zip256 (f : W64 → W64 → W64) (x y : V256) {i : Nat} (lane : i < 4) :
    lane64 (zip256 f x y) i = f (lane64 x i) (lane64 y i) := by
  match i, lane with
  | 0, _ => exact lane256_0 _ _ _ _
  | 1, _ => exact lane256_1 _ _ _ _
  | 2, _ => exact lane256_2 _ _ _ _
  | 3, _ => exact lane256_3 _ _ _ _
#print axioms lane64_zip256

/-- Lane `i` of a lanewise map is the map of lane `i`. -/
theorem lane64_map256 (f : W64 → W64) (x : V256) {i : Nat} (lane : i < 4) :
    lane64 (map256 f x) i = f (lane64 x i) := by
  match i, lane with
  | 0, _ => exact lane256_0 _ _ _ _
  | 1, _ => exact lane256_1 _ _ _ _
  | 2, _ => exact lane256_2 _ _ _ _
  | 3, _ => exact lane256_3 _ _ _ _
#print axioms lane64_map256

/-- Lane 0 of `pack512` is its lane-0 argument. -/
@[simp] theorem lane512_0 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 0 = a0 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
#print axioms lane512_0

/-- Lane 1 of `pack512` is its lane-1 argument. -/
@[simp] theorem lane512_1 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 1 = a1 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
#print axioms lane512_1

/-- Lane 2 of `pack512` is its lane-2 argument. -/
@[simp] theorem lane512_2 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 2 = a2 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
#print axioms lane512_2

/-- Lane 3 of `pack512` is its lane-3 argument. -/
@[simp] theorem lane512_3 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 3 = a3 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
#print axioms lane512_3

/-- Lane 4 of `pack512` is its lane-4 argument. -/
@[simp] theorem lane512_4 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 4 = a4 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
#print axioms lane512_4

/-- Lane 5 of `pack512` is its lane-5 argument. -/
@[simp] theorem lane512_5 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 5 = a5 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
#print axioms lane512_5

/-- Lane 6 of `pack512` is its lane-6 argument. -/
@[simp] theorem lane512_6 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 6 = a6 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
#print axioms lane512_6

/-- Lane 7 of `pack512` is its lane-7 argument. -/
@[simp] theorem lane512_7 (a0 a1 a2 a3 a4 a5 a6 a7 : W64) :
    lane64 (pack512 a0 a1 a2 a3 a4 a5 a6 a7) 7 = a7 := by
  simp only [lane64, pack512, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
#print axioms lane512_7

/-- Bitwise and acts lane by lane. -/
theorem lane64_and (x y : BitVec width) {i : Nat} :
    lane64 (x &&& y) i = lane64 x i &&& lane64 y i := by
  ext bit bound
  simp [lane64, BitVec.getElem_extractLsb'] <;> grind
#print axioms lane64_and

/-- Bitwise or acts lane by lane. -/
theorem lane64_or (x y : BitVec width) {i : Nat} :
    lane64 (x ||| y) i = lane64 x i ||| lane64 y i := by
  ext bit bound
  simp [lane64, BitVec.getElem_extractLsb'] <;> grind
#print axioms lane64_or

/-- Bitwise exclusive or acts lane by lane. -/
theorem lane64_xor (x y : BitVec width) {i : Nat} :
    lane64 (x ^^^ y) i = lane64 x i ^^^ lane64 y i := by
  ext bit bound
  simp [lane64, BitVec.getElem_extractLsb'] <;> grind
#print axioms lane64_xor

/-- `andNot` acts lane by lane. -/
theorem lane64_andNot (x y : BitVec width) {i : Nat} :
    lane64 ((~~~x) &&& y) i = (~~~lane64 x i) &&& lane64 y i := by
  ext bit bound
  simp [lane64, BitVec.getElem_extractLsb'] <;> grind
#print axioms lane64_andNot

/-- Lane `i` of a 512-bit lanewise operation is the operation on lane `i`. -/
theorem lane64_zip512 (f : W64 → W64 → W64) (x y : V512) {i : Nat} (lane : i < 8) :
    lane64 (zip512 f x y) i = f (lane64 x i) (lane64 y i) := by
  have alternatives : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [zip512]
#print axioms lane64_zip512

/-- Lane `i` of a left shift by a vector count: cleared for counts of 64 or more, else shifted. -/
theorem lane64_shiftLeftCount64 (value : V256) (count : W64) {i : Nat} (lane : i < 4) :
    lane64 (shiftLeftCount64 value count) i =
      if count.toNat >= 64 then 0 else lane64 value i <<< count.toNat := by
  unfold shiftLeftCount64
  split
  · simp [lane64]
  · exact lane64_map256 _ _ lane
#print axioms lane64_shiftLeftCount64

/-- Lane `i` of a logical right shift by a vector count: cleared for counts of 64 or more, else
    shifted. -/
theorem lane64_shiftRightCount64 (value : V256) (count : W64) {i : Nat} (lane : i < 4) :
    lane64 (shiftRightCount64 value count) i =
      if count.toNat >= 64 then 0 else lane64 value i >>> count.toNat := by
  unfold shiftRightCount64
  split
  · simp [lane64]
  · exact lane64_map256 _ _ lane
#print axioms lane64_shiftRightCount64

/-- Every lane of the all-ones vector is all ones. -/
theorem lane64_allOnes256 {i : Nat} (lane : i < 4) :
    lane64 (~~~0 : V256) i = BitVec.allOnes 64 := by
  rw [show (0 : V256) = 0#256 from rfl, BitVec.not_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro bit below
  simp only [lane64, BitVec.getLsbD_extractLsb', below, decide_true, Bool.true_and,
    BitVec.getLsbD_allOnes]
  exact decide_eq_true (by omega)
#print axioms lane64_allOnes256

/-! ### Numeric value of packed lanes -/

/-- A packed 128-bit vector is the base-`2^64` number with its lanes as digits. -/
theorem toNat_pack128 (a0 a1 : W64) :
    (pack128 a0 a1).toNat = a0.toNat + 2 ^ 64 * a1.toNat := by
  rw [pack128, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt a0.isLt, Nat.shiftLeft_eq]
  omega
#print axioms toNat_pack128

/-- A packed 256-bit vector is the base-`2^64` number with its lanes as digits. -/
theorem toNat_pack256 (a0 a1 a2 a3 : W64) :
    (pack256 a0 a1 a2 a3).toNat =
      a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat := by
  have low := (pack128 a0 a1).isLt
  have high := toNat_pack128 a2 a3
  have lowValue := toNat_pack128 a0 a1
  unfold pack128 at low high lowValue
  rw [pack256, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low, Nat.shiftLeft_eq,
    high, lowValue]
  omega
#print axioms toNat_pack256

/-! ### Sign masks -/

/-- `moveMask64` packs the four lane sign bits into the low bits of a word. -/
theorem moveMask64_eq (x : V256) :
    moveMask64 x = BitVec.ofNat 32 ((lane64 x 0).msb.toNat + 2 * (lane64 x 1).msb.toNat +
      4 * (lane64 x 2).msb.toNat + 8 * (lane64 x 3).msb.toNat) := by
  unfold moveMask64
  simp only [List.range, List.range.loop, List.foldl]
  generalize (lane64 x 0).msb = sign0
  generalize (lane64 x 1).msb = sign1
  generalize (lane64 x 2).msb = sign2
  generalize (lane64 x 3).msb = sign3
  cases sign0 <;> cases sign1 <;> cases sign2 <;> cases sign3 <;> decide
#print axioms moveMask64_eq

/-- Bit `i` of the sign-mask fold is flag `i` for the first `count` flags and clear above. -/
private theorem getLsbD_signFold (flags : Nat → Bool) (count : Nat) (fits : count ≤ 32)
    (i : Nat) :
    ((List.range count).foldl (fun result index =>
      result ||| (BitVec.ofNat 32 (if flags index then 1 else 0) <<< index)) 0).getLsbD i =
      (decide (i < count) && flags i) := by
  induction count with
  | zero => simp
  | succ count previous =>
    have shifted : (BitVec.ofNat 32 (if flags count then 1 else 0) <<< count).getLsbD i =
        (decide (i = count) && flags count) := by
      cases flags count
      · simp
      · simp only [ite_true, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, Bool.and_true]
        by_cases atCount : i = count
        · subst atCount
          simp
          omega
        · simp only [atCount, decide_false, Bool.and_eq_false_imp, Bool.and_eq_true,
            decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, and_imp]
          intro _ above _
          rw [show i - count = (i - count - 1) + 1 by omega, Nat.testBit_add_one]
          simp
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      previous (by omega), shifted]
    by_cases atCount : i = count
    · subst atCount
      simp
    · have below : decide (i < count + 1) = decide (i < count) :=
        decide_eq_decide.mpr (by omega)
      simp [atCount, below]
#print axioms getLsbD_signFold

/-- Bit `i` of `moveMask64` is the sign bit of lane `i`; bits 4 and above are clear. -/
theorem getLsbD_moveMask64 (x : V256) (i : Nat) :
    (moveMask64 x).getLsbD i = (decide (i < 4) && (lane64 x i).msb) :=
  getLsbD_signFold (fun index => (lane64 x index).msb) 4 (by decide) i
#print axioms getLsbD_moveMask64

/-- Bit `i` of `moveMask64` is the sign bit of lane `i`. -/
theorem getLsbD_moveMask64_of_lt (x : V256) {i : Nat} (lane : i < 4) :
    (moveMask64 x).getLsbD i = (lane64 x i).msb := by
  rw [getLsbD_moveMask64, decide_eq_true lane, Bool.true_and]
#print axioms getLsbD_moveMask64_of_lt

/-- Bit `i` of `moveMask512` is the sign bit of lane `i`; bits 8 and above are clear. -/
theorem getLsbD_moveMask512 (x : V512) (i : Nat) :
    (moveMask512 x).getLsbD i = (decide (i < 8) && (lane64 x i).msb) :=
  getLsbD_signFold (fun index => (lane64 x index).msb) 8 (by decide) i
#print axioms getLsbD_moveMask512

/-- Bit `i` of the sign mask of a lanewise comparison is the comparison on lane `i`. -/
theorem getLsbD_moveMask64_compare (compare : W64 → W64 → Bool) (x y : V256) {i : Nat}
    (lane : i < 4) :
    (moveMask64 (zip256 (fun a b => mask64 (compare a b)) x y)).getLsbD i =
      compare (lane64 x i) (lane64 y i) := by
  rw [getLsbD_moveMask64_of_lt _ lane, lane64_zip256 _ _ _ lane, msb_mask64]
#print axioms getLsbD_moveMask64_compare

/-- The sign mask of four comparison results is the 4-bit flag word. -/
theorem moveMask64_pack256_mask64 (p0 p1 p2 p3 : Bool) :
    moveMask64 (pack256 (mask64 p0) (mask64 p1) (mask64 p2) (mask64 p3)) =
      BitVec.ofNat 32 (p0.toNat + 2 * p1.toNat + 4 * p2.toNat + 8 * p3.toNat) := by
  rw [moveMask64_eq]
  simp only [lane256_0, lane256_1, lane256_2, lane256_3, msb_mask64]
#print axioms moveMask64_pack256_mask64

/-! ### Lane carries of wide sums and differences -/

/-- A 256-bit sum is the lane sums plus the carries out of the lanes below. -/
theorem add256_lanes (x y : V256) :
    x + y = zip256 (· + ·) (zip256 (· + ·) x y)
      (pack256 0 (if BitVec.carry 64 x y false then 1 else 0)
        (if BitVec.carry 128 x y false then 1 else 0)
        (if BitVec.carry 192 x y false then 1 else 0)) := by
  apply eq_of_lane64_eq256
  intro i lane
  rw [lane64_add x y i (by omega), lane64_zip256 _ _ _ lane, lane64_zip256 _ _ _ lane]
  match i, lane with
  | 0, _ => simp only [carry_lane_zero, lane256_0]; rfl
  | 1, _ => rw [lane256_1]
  | 2, _ => rw [lane256_2]
  | 3, _ => rw [lane256_3]
#print axioms add256_lanes

/-- A 256-bit difference is the lane differences less the borrows out of the lanes below. -/
theorem sub256_lanes (x y : V256) :
    x - y = zip256 (· - ·) (zip256 (· - ·) x y)
      (pack256 0 (if subBorrow 64 x y then 1 else 0) (if subBorrow 128 x y then 1 else 0)
        (if subBorrow 192 x y then 1 else 0)) := by
  apply eq_of_lane64_eq256
  intro i lane
  rw [lane64_sub x y i (by omega), lane64_zip256 _ _ _ lane, lane64_zip256 _ _ _ lane]
  match i, lane with
  | 0, _ => simp only [subBorrow_lane_zero, lane256_0]; rfl
  | 1, _ => rw [lane256_1]
  | 2, _ => rw [lane256_2]
  | 3, _ => rw [lane256_3]
#print axioms sub256_lanes

/-- A 128-bit sum is the lane sums plus the carry out of the low lane. -/
theorem add128_lanes (x y : V128) :
    x + y = zip128 (· + ·) (zip128 (· + ·) x y)
      (pack128 0 (if BitVec.carry 64 x y false then 1 else 0)) := by
  apply eq_of_lane64_eq128
  intro i lane
  rw [lane64_add x y i (by omega)]
  match i, lane with
  | 0, _ => simp only [carry_lane_zero, zip128, lane128_0]; rfl
  | 1, _ => simp only [zip128, lane128_1]
#print axioms add128_lanes

/-- A 128-bit difference is the lane differences less the borrow out of the low lane. -/
theorem sub128_lanes (x y : V128) :
    x - y = zip128 (· - ·) (zip128 (· - ·) x y)
      (pack128 0 (if subBorrow 64 x y then 1 else 0)) := by
  apply eq_of_lane64_eq128
  intro i lane
  rw [lane64_sub x y i (by omega)]
  match i, lane with
  | 0, _ => simp only [subBorrow_lane_zero, zip128, lane128_0]; rfl
  | 1, _ => simp only [zip128, lane128_1]
#print axioms sub128_lanes

/-- The lane carries of a 256-bit sum from the intrinsic masks: `generate` marks lanes whose
    sum compares below `x`, `propagate` lanes whose sum equals the all-ones vector, and bit `i`
    of the cascade is the carry into lane `i`; bit 4 is the carry out of the whole sum. AVX-512
    `.ltu64` and portable `.vector (.ltu64 256)` produce the `generate` comparison, and AVX2
    `.eq64` and portable `.vector (.eq64 256)` the `propagate` one. -/
theorem cascade_add256 (x y : V256) {i : Nat} (lane : i ≤ 4) :
    let sum := zip256 (· + ·) x y
    let generate := moveMask64 (zip256 (fun a b => mask64 (a.ult b)) sum x)
    let propagate := moveMask64 (zip256 (fun a b => mask64 (a == b)) sum (~~~0))
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD i =
      BitVec.carry (64 * i) x y false := by
  intro sum generate propagate
  apply cascade_add_flags x y generate propagate 4 _ _ i lane (by omega)
  · intro j below
    rw [getLsbD_moveMask64_compare _ _ _ below, lane64_zip256 _ _ _ below]
  · intro j below
    rw [getLsbD_moveMask64_compare _ _ _ below, lane64_zip256 _ _ _ below,
      lane64_allOnes256 below]
#print axioms cascade_add256

/-- The lane borrows of a 256-bit difference from the intrinsic masks: `generate` marks lanes
    where `x` compares below `y`, `propagate` lanes where they are equal, and bit `i` of the
    cascade is the borrow into lane `i`; bit 4 is the borrow out of the whole difference. The
    same `.ltu64` and `.eq64` intrinsics as for `cascade_add256` produce the comparisons. -/
theorem cascade_sub256 (x y : V256) {i : Nat} (lane : i ≤ 4) :
    let generate := moveMask64 (zip256 (fun a b => mask64 (a.ult b)) x y)
    let propagate := moveMask64 (zip256 (fun a b => mask64 (a == b)) x y)
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD i = subBorrow (64 * i) x y := by
  intro generate propagate
  apply cascade_sub_flags x y generate propagate 4 _ _ i lane (by omega)
  · intro j below
    rw [getLsbD_moveMask64_compare _ _ _ below]
  · intro j below
    rw [getLsbD_moveMask64_compare _ _ _ below]
#print axioms cascade_sub256

/-- A 256-bit sum is the lane sums plus the carry-in vector decoded from the cascade bits of
    the intrinsic masks, as a vector routine computes it. -/
theorem add256_cascade (x y : V256) :
    let sum := zip256 (· + ·) x y
    let generate := moveMask64 (zip256 (fun a b => mask64 (a.ult b)) sum x)
    let propagate := moveMask64 (zip256 (fun a b => mask64 (a == b)) sum (~~~0))
    let carries := propagate ^^^ (propagate + (generate <<< 1))
    x + y = zip256 (· + ·) sum (pack256 0 (if carries.getLsbD 1 then 1 else 0)
      (if carries.getLsbD 2 then 1 else 0) (if carries.getLsbD 3 then 1 else 0)) := by
  intro sum generate propagate carries
  rw [show carries.getLsbD 1 = _ from cascade_add256 x y (i := 1) (by decide),
    show carries.getLsbD 2 = _ from cascade_add256 x y (i := 2) (by decide),
    show carries.getLsbD 3 = _ from cascade_add256 x y (i := 3) (by decide)]
  exact add256_lanes x y
#print axioms add256_cascade

/-- A 256-bit difference is the lane differences less the borrow-in vector decoded from the
    cascade bits of the intrinsic masks, as a vector routine computes it. -/
theorem sub256_cascade (x y : V256) :
    let generate := moveMask64 (zip256 (fun a b => mask64 (a.ult b)) x y)
    let propagate := moveMask64 (zip256 (fun a b => mask64 (a == b)) x y)
    let borrows := propagate ^^^ (propagate + (generate <<< 1))
    x - y = zip256 (· - ·) (zip256 (· - ·) x y) (pack256 0 (if borrows.getLsbD 1 then 1 else 0)
      (if borrows.getLsbD 2 then 1 else 0) (if borrows.getLsbD 3 then 1 else 0)) := by
  intro generate propagate borrows
  rw [show borrows.getLsbD 1 = _ from cascade_sub256 x y (i := 1) (by decide),
    show borrows.getLsbD 2 = _ from cascade_sub256 x y (i := 2) (by decide),
    show borrows.getLsbD 3 = _ from cascade_sub256 x y (i := 3) (by decide)]
  exact sub256_lanes x y
#print axioms sub256_cascade

/-- Every lane of the 512-bit all-ones vector is all ones. -/
theorem lane64_allOnes512 {index : Nat} (lane : index < 8) :
    lane64 (~~~0 : V512) index = BitVec.allOnes 64 := by
  rw [show (0 : V512) = 0#512 from rfl, BitVec.not_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro bit below
  simp only [lane64, BitVec.getLsbD_extractLsb', below, decide_true, Bool.true_and,
    BitVec.getLsbD_allOnes]
  exact decide_eq_true (by omega)
#print axioms lane64_allOnes512

/-- A comparison mask bit below lane eight is exactly that lane's comparison result. -/
theorem getLsbD_moveMask512_compare (compare : W64 → W64 → Bool) (left right : V512)
    {index : Nat} (lane : index < 8) :
    (moveMask512 (zip512 (fun a b => mask64 (compare a b)) left right)).getLsbD index =
      compare (lane64 left index) (lane64 right index) := by
  rw [getLsbD_moveMask512, decide_eq_true lane, Bool.true_and,
    lane64_zip512 _ _ _ lane, msb_mask64]
#print axioms getLsbD_moveMask512_compare

/-- Cascade bit eight is the carry out of a 512-bit sum; lower bits are lane carry-ins. -/
theorem cascade_add512 (left right : V512) {index : Nat} (lane : index ≤ 8) :
    let sum := zip512 (· + ·) left right
    let generate := moveMask512 (zip512 (fun a b => mask64 (a.ult b)) sum left)
    let propagate := moveMask512 (zip512 (fun a b => mask64 (a == b)) sum (~~~0))
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD index =
      BitVec.carry (64 * index) left right false := by
  intro sum generate propagate
  apply cascade_add_flags left right generate propagate 8 _ _ index lane (by omega)
  · intro index below
    rw [getLsbD_moveMask512_compare _ _ _ below, lane64_zip512 _ _ _ below]
  · intro index below
    rw [getLsbD_moveMask512_compare _ _ _ below, lane64_zip512 _ _ _ below,
      lane64_allOnes512 below]
#print axioms cascade_add512

/-- Cascade bit eight is the borrow out of a 512-bit difference; lower bits are borrow-ins. -/
theorem cascade_sub512 (left right : V512) {index : Nat} (lane : index ≤ 8) :
    let generate := moveMask512 (zip512 (fun a b => mask64 (a.ult b)) left right)
    let propagate := moveMask512 (zip512 (fun a b => mask64 (a == b)) left right)
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD index =
      subBorrow (64 * index) left right := by
  intro generate propagate
  apply cascade_sub_flags left right generate propagate 8 _ _ index lane (by omega)
  · intro index below
    rw [getLsbD_moveMask512_compare _ _ _ below]
  · intro index below
    rw [getLsbD_moveMask512_compare _ _ _ below]
#print axioms cascade_sub512

/-- Equal 64-bit lanes determine all 512 bits of a vector. -/
theorem eq_of_lane64_eq512 {left right : V512}
    (lanes : ∀ index < 8, lane64 left index = lane64 right index) : left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit below
  have equal := congrArg (fun value : W64 => value.getLsbD (bit % 64))
    (lanes (bit / 64) (by omega))
  have position : 64 * (bit / 64) + bit % 64 = bit := by omega
  simpa only [lane64, BitVec.getLsbD_extractLsb',
    decide_eq_true (Nat.mod_lt bit (by decide : 0 < 64)), Bool.true_and, position] using equal
#print axioms eq_of_lane64_eq512
/-- A 512-bit sum is the independent lane sums repaired by decoded cascade carry-ins. -/
theorem add512_cascade (left right : V512) :
    let sum := zip512 (· + ·) left right
    let generate := moveMask512 (zip512 (fun a b => mask64 (a.ult b)) sum left)
    let propagate := moveMask512 (zip512 (fun a b => mask64 (a == b)) sum (~~~0))
    let carries := propagate ^^^ (propagate + (generate <<< 1))
    left + right = zip512 (· + ·) sum
      (pack512 0 (if carries.getLsbD 1 then 1 else 0) (if carries.getLsbD 2 then 1 else 0)
        (if carries.getLsbD 3 then 1 else 0) (if carries.getLsbD 4 then 1 else 0)
        (if carries.getLsbD 5 then 1 else 0) (if carries.getLsbD 6 then 1 else 0)
        (if carries.getLsbD 7 then 1 else 0)) := by
  intro sum generate propagate carries
  apply eq_of_lane64_eq512
  intro index below
  rw [lane64_add left right index (by omega), lane64_zip512 _ _ _ below,
    lane64_zip512 _ _ _ below]
  match index, below with
  | 0, _ => simp only [carry_lane_zero, lane512_0]; rfl
  | 1, _ => rw [lane512_1, show carries.getLsbD 1 = _ from
      cascade_add512 left right (index := 1) (by decide)]
  | 2, _ => rw [lane512_2, show carries.getLsbD 2 = _ from
      cascade_add512 left right (index := 2) (by decide)]
  | 3, _ => rw [lane512_3, show carries.getLsbD 3 = _ from
      cascade_add512 left right (index := 3) (by decide)]
  | 4, _ => rw [lane512_4, show carries.getLsbD 4 = _ from
      cascade_add512 left right (index := 4) (by decide)]
  | 5, _ => rw [lane512_5, show carries.getLsbD 5 = _ from
      cascade_add512 left right (index := 5) (by decide)]
  | 6, _ => rw [lane512_6, show carries.getLsbD 6 = _ from
      cascade_add512 left right (index := 6) (by decide)]
  | 7, _ => rw [lane512_7, show carries.getLsbD 7 = _ from
      cascade_add512 left right (index := 7) (by decide)]
#print axioms add512_cascade

/-- A 512-bit difference is the lane differences repaired by decoded cascade borrow-ins. -/
theorem sub512_cascade (left right : V512) :
    let difference := zip512 (· - ·) left right
    let generate := moveMask512 (zip512 (fun a b => mask64 (a.ult b)) left right)
    let propagate := moveMask512 (zip512 (fun a b => mask64 (a == b)) left right)
    let borrows := propagate ^^^ (propagate + (generate <<< 1))
    left - right = zip512 (· - ·) difference
      (pack512 0 (if borrows.getLsbD 1 then 1 else 0) (if borrows.getLsbD 2 then 1 else 0)
        (if borrows.getLsbD 3 then 1 else 0) (if borrows.getLsbD 4 then 1 else 0)
        (if borrows.getLsbD 5 then 1 else 0) (if borrows.getLsbD 6 then 1 else 0)
        (if borrows.getLsbD 7 then 1 else 0)) := by
  intro difference generate propagate borrows
  apply eq_of_lane64_eq512
  intro index below
  rw [lane64_sub left right index (by omega), lane64_zip512 _ _ _ below,
    lane64_zip512 _ _ _ below]
  match index, below with
  | 0, _ => simp only [subBorrow_lane_zero, lane512_0]; rfl
  | 1, _ => rw [lane512_1, show borrows.getLsbD 1 = _ from
      cascade_sub512 left right (index := 1) (by decide)]
  | 2, _ => rw [lane512_2, show borrows.getLsbD 2 = _ from
      cascade_sub512 left right (index := 2) (by decide)]
  | 3, _ => rw [lane512_3, show borrows.getLsbD 3 = _ from
      cascade_sub512 left right (index := 3) (by decide)]
  | 4, _ => rw [lane512_4, show borrows.getLsbD 4 = _ from
      cascade_sub512 left right (index := 4) (by decide)]
  | 5, _ => rw [lane512_5, show borrows.getLsbD 5 = _ from
      cascade_sub512 left right (index := 5) (by decide)]
  | 6, _ => rw [lane512_6, show borrows.getLsbD 6 = _ from
      cascade_sub512 left right (index := 6) (by decide)]
  | 7, _ => rw [lane512_7, show borrows.getLsbD 7 = _ from
      cascade_sub512 left right (index := 7) (by decide)]
#print axioms sub512_cascade

/-- Testing the second addend above the wrapped lane sum gives the same carry cascade. -/
theorem cascade_add256_gtu (left right : V256) {index : Nat} (lane : index ≤ 4) :
    let sum := zip256 (· + ·) left right
    let generate := moveMask64 (zip256 (fun a b => mask64 (b.ult a)) right sum)
    let propagate := moveMask64 (zip256 (fun a b => mask64 (a == b)) sum (~~~0))
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD index =
      BitVec.carry (64 * index) left right false := by
  have sums : zip256 (· + ·) right left = zip256 (· + ·) left right := by
    apply eq_of_lane64_eq256
    intro index below
    rw [lane64_zip256 _ _ _ below, lane64_zip256 _ _ _ below, BitVec.add_comm]
  have comparison :
      zip256 (fun a b => mask64 (a.ult b)) (zip256 (· + ·) left right) right =
      zip256 (fun a b => mask64 (b.ult a)) right (zip256 (· + ·) left right) := by
    apply eq_of_lane64_eq256
    intro index below
    simp only [lane64_zip256 _ _ _ below]
  simpa only [sums, comparison, BitVec.carry, Nat.add_comm] using
    cascade_add256 right left lane
#print axioms cascade_add256_gtu

/-- Broadcasting the all-ones 64-bit word gives the 256-bit all-ones comparand. -/
theorem pack256_allOnes :
    pack256 (~~~0) (~~~0) (~~~0) (~~~0) = (~~~0 : V256) := by
  apply eq_of_lane64_eq256
  intro index below
  rw [lane64_allOnes256 below]
  match index, below with
  | 0, _ => rw [lane256_0]; rfl
  | 1, _ => rw [lane256_1]; rfl
  | 2, _ => rw [lane256_2]; rfl
  | 3, _ => rw [lane256_3]; rfl
#print axioms pack256_allOnes

/-- The addition cascade accepts the comparand emitted by a broadcast `create64`. -/
theorem cascade_add256_broadcast (left right : V256) {index : Nat} (lane : index ≤ 4) :
    let sum := zip256 (· + ·) left right
    let generate := moveMask64 (zip256 (fun a b => mask64 (a.ult b)) sum left)
    let propagate := moveMask64 (zip256 (fun a b => mask64 (a == b)) sum
      (pack256 (~~~0) (~~~0) (~~~0) (~~~0)))
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD index =
      BitVec.carry (64 * index) left right false := by
  simpa only [pack256_allOnes] using cascade_add256 left right lane
#print axioms cascade_add256_broadcast

/-- Broadcast propagation and operand-swapped greater-than generation compose directly. -/
theorem cascade_add256_gtu_broadcast (left right : V256) {index : Nat} (lane : index ≤ 4) :
    let sum := zip256 (· + ·) left right
    let generate := moveMask64 (zip256 (fun a b => mask64 (b.ult a)) right sum)
    let propagate := moveMask64 (zip256 (fun a b => mask64 (a == b)) sum
      (pack256 (~~~0) (~~~0) (~~~0) (~~~0)))
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD index =
      BitVec.carry (64 * index) left right false := by
  simpa only [pack256_allOnes] using cascade_add256_gtu left right lane
#print axioms cascade_add256_gtu_broadcast

/-! ### Multiplication -/

/-- An even 32-bit lane is the low half of the 64-bit lane that holds it. -/
theorem lane32_even (x : BitVec w) (i : Nat) : lane32 x (2 * i) = (lane64 x i).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit below
  simp only [lane32, lane64, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, below,
    decide_true, Bool.true_and]
  rw [show 32 * (2 * i) + bit = 64 * i + bit by omega]
  simp only [show bit < 64 by omega, decide_true, Bool.true_and]
#print axioms lane32_even

/-- `multiplyEven32` lane product: the low halves of two lanes, widened and multiplied. -/
theorem lane64_multiplyEven32 (x y : V256) {i : Nat} (lane : i < 4) :
    lane64 (multiplyEven32 x y) i =
      ((lane64 x i).setWidth 32).zeroExtend 64 * ((lane64 y i).setWidth 32).zeroExtend 64 := by
  rw [← lane32_even, ← lane32_even]
  match i, lane with
  | 0, _ => exact lane256_0 _ _ _ _
  | 1, _ => exact lane256_1 _ _ _ _
  | 2, _ => exact lane256_2 _ _ _ _
  | 3, _ => exact lane256_3 _ _ _ _
#print axioms lane64_multiplyEven32

/-- `multiplyEven32` on packed lanes multiplies their widened low halves. -/
theorem multiplyEven32_pack256 (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    multiplyEven32 (pack256 a0 a1 a2 a3) (pack256 b0 b1 b2 b3) =
      pack256 ((a0.setWidth 32).zeroExtend 64 * (b0.setWidth 32).zeroExtend 64)
        ((a1.setWidth 32).zeroExtend 64 * (b1.setWidth 32).zeroExtend 64)
        ((a2.setWidth 32).zeroExtend 64 * (b2.setWidth 32).zeroExtend 64)
        ((a3.setWidth 32).zeroExtend 64 * (b3.setWidth 32).zeroExtend 64) := by
  apply eq_of_lane64_eq256
  intro i lane
  rw [lane64_multiplyEven32 _ _ lane]
  match i, lane with
  | 0, _ => simp only [lane256_0]
  | 1, _ => simp only [lane256_1]
  | 2, _ => simp only [lane256_2]
  | 3, _ => simp only [lane256_3]
#print axioms multiplyEven32_pack256

/-- The product of two widened 32-bit halves never wraps: it is the exact natural product. -/
theorem toNat_even_product (a b : W64) :
    ((a.setWidth 32).zeroExtend 64 * (b.setWidth 32).zeroExtend 64).toNat =
      a.toNat % 2 ^ 32 * (b.toNat % 2 ^ 32) := by
  have aLow := Nat.mod_lt a.toNat (Nat.two_pow_pos 32)
  have bLow := Nat.mod_lt b.toNat (Nat.two_pow_pos 32)
  have bound : a.toNat % 2 ^ 32 * (b.toNat % 2 ^ 32) < 2 ^ 64 :=
    calc a.toNat % 2 ^ 32 * (b.toNat % 2 ^ 32) < 2 ^ 32 * 2 ^ 32 :=
          Nat.mul_lt_mul_of_lt_of_lt aLow bLow
      _ = 2 ^ 64 := by decide
  simp only [BitVec.toNat_mul, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : a.toNat % 2 ^ 32 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : b.toNat % 2 ^ 32 < 2 ^ 64), Nat.mod_eq_of_lt bound]
#print axioms toNat_even_product

/-- Lane `i` of the AVX-512DQ low product is the wrapped product of lane `i`. -/
theorem lane64_multiplyLow64 (x y : V256) {i : Nat} (lane : i < 4) :
    lane64 (multiplyLow64 x y) i = lane64 x i * lane64 y i :=
  lane64_zip256 _ _ _ lane
#print axioms lane64_multiplyLow64

/-- The AVX-512DQ low product on packed lanes multiplies each lane. -/
theorem multiplyLow64_pack256 (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    multiplyLow64 (pack256 a0 a1 a2 a3) (pack256 b0 b1 b2 b3) =
      pack256 (a0 * b0) (a1 * b1) (a2 * b2) (a3 * b3) :=
  zip256_pack256 _ _ _ _ _ _ _ _ _
#print axioms multiplyLow64_pack256

/-! ### Lane permutation -/

/-- Lane `i` of `permute4x64` is the lane of `x` that bits `2i` and `2i + 1` of `control`
    select. -/
theorem lane64_permute4x64 (x : V256) (control : BitVec 8) {i : Nat} (lane : i < 4) :
    lane64 (permute4x64 x control) i = lane64 x (control.extractLsb' (2 * i) 2).toNat := by
  match i, lane with
  | 0, _ => exact lane256_0 _ _ _ _
  | 1, _ => exact lane256_1 _ _ _ _
  | 2, _ => exact lane256_2 _ _ _ _
  | 3, _ => exact lane256_3 _ _ _ _
#print axioms lane64_permute4x64

/-! ### Evaluation with an immediate operand -/

/-- An `i32` immediate below 256 is read as that byte. -/
private theorem immediate_byte {count : Nat} (small : count < 256) :
    (if (BitVec.ofNat 32 count).toNat < 256 then some ((BitVec.ofNat 32 count).setWidth 8)
      else none) = some (BitVec.ofNat 8 count) := by
  have narrow : (BitVec.ofNat 32 count).toNat = count := by
    rw [BitVec.toNat_ofNat]
    omega
  simp only [narrow, small, ↓reduceIte, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, narrow, BitVec.toNat_ofNat]
#print axioms immediate_byte

/-- `Avx2.ShiftLeftLogical` by an immediate shifts every lane; counts of 64 or more clear it. -/
theorem intrinsic_shl256 (x : V256) {count : Nat} (small : count < 256) :
    evalIntrinsic (.avx2 .shl64) [.v256 x, .i32 (BitVec.ofNat 32 count)] =
      some (.v256 (map256 (· <<< count) x)) := by
  show bind (if (BitVec.ofNat 32 count).toNat < 256 then
      some ((BitVec.ofNat 32 count).setWidth 8) else none)
    (fun byte => some (Value.v256 (map256 (· <<< byte.toNat) x))) = _
  rw [immediate_byte small]
  show some (Value.v256 (map256 (· <<< (BitVec.ofNat 8 count).toNat) x)) = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
#print axioms intrinsic_shl256

/-- `Avx2.ShiftRightLogical` by an immediate shifts every lane; counts of 64 or more clear
    it. -/
theorem intrinsic_shr256 (x : V256) {count : Nat} (small : count < 256) :
    evalIntrinsic (.avx2 .shr64) [.v256 x, .i32 (BitVec.ofNat 32 count)] =
      some (.v256 (map256 (· >>> count) x)) := by
  show bind (if (BitVec.ofNat 32 count).toNat < 256 then
      some ((BitVec.ofNat 32 count).setWidth 8) else none)
    (fun byte => some (Value.v256 (map256 (· >>> byte.toNat) x))) = _
  rw [immediate_byte small]
  show some (Value.v256 (map256 (· >>> (BitVec.ofNat 8 count).toNat) x)) = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
#print axioms intrinsic_shr256

/-- `Avx2.Permute4x64` with an immediate control below 256. -/
theorem intrinsic_permute4x64 (x : V256) {control : Nat} (small : control < 256) :
    evalIntrinsic (.avx2 .permute4x64) [.v256 x, .i32 (BitVec.ofNat 32 control)] =
      some (.v256 (permute4x64 x (BitVec.ofNat 8 control))) := by
  show bind (if (BitVec.ofNat 32 control).toNat < 256 then
      some ((BitVec.ofNat 32 control).setWidth 8) else none)
    (fun byte => some (Value.v256 (permute4x64 x byte))) = _
  rw [immediate_byte small]
  rfl
#print axioms intrinsic_permute4x64

/-! ### Evaluation of the remaining integer intrinsics -/

/-- `Avx2.Add` adds lanewise. -/
theorem intrinsic_avx2_add256 (x y : V256) :
    evalIntrinsic (.avx2 .add64) [.v256 x, .v256 y] = some (.v256 (zip256 (· + ·) x y)) := rfl
#print axioms intrinsic_avx2_add256

/-- `Avx2.CompareEqual` gives a lanewise equality mask. -/
theorem intrinsic_avx2_eq256 (x y : V256) :
    evalIntrinsic (.avx2 .eq64) [.v256 x, .v256 y] =
      some (.v256 (zip256 (fun a b => mask64 (a == b)) x y)) := rfl
#print axioms intrinsic_avx2_eq256

/-- AVX-512 `CompareLessThan` on unsigned lanes gives a lanewise mask. -/
theorem intrinsic_avx512_ltu256 (x y : V256) :
    evalIntrinsic (.avx512 .ltu64) [.v256 x, .v256 y] =
      some (.v256 (zip256 (fun a b => mask64 (a.ult b)) x y)) := rfl
#print axioms intrinsic_avx512_ltu256

/-- `Avx2.CompareGreaterThan` on signed lanes gives a lanewise mask of `x > y` as integers. -/
theorem intrinsic_avx2_signedgt256 (x y : V256) :
    evalIntrinsic (.avx2 .signedgt64) [.v256 x, .v256 y] =
      some (.v256 (zip256 (fun a b => mask64 (decide (b.toInt < a.toInt))) x y)) := rfl
#print axioms intrinsic_avx2_signedgt256

/-- Lane `i` of the signed greater-than mask: all ones exactly when lane `i` of `x` exceeds that
    of `y` as a signed integer. -/
theorem lane64_signedgt256 (x y : V256) {i : Nat} (lane : i < 4) :
    lane64 (zip256 (fun a b => mask64 (decide (b.toInt < a.toInt))) x y) i =
      mask64 (decide ((lane64 y i).toInt < (lane64 x i).toInt)) :=
  lane64_zip256 _ _ _ lane
#print axioms lane64_signedgt256

/-- `Avx2.Multiply` on unsigned lanes multiplies the even 32-bit lanes into 64-bit products. -/
theorem intrinsic_multiplyEven32 (x y : V256) :
    evalIntrinsic (.avx2 .multiplyEven32) [.v256 x, .v256 y] =
      some (.v256 (multiplyEven32 x y)) := rfl
#print axioms intrinsic_multiplyEven32

/-- AVX-512DQ `MultiplyLow` keeps the low 64 bits of each lane product. -/
theorem intrinsic_avx512dq_mul256 (x y : V256) :
    evalIntrinsic (.avx512DQ .mul64) [.v256 x, .v256 y] = some (.v256 (multiplyLow64 x y)) :=
  rfl
#print axioms intrinsic_avx512dq_mul256

/-- Portable `Vector256` multiplication keeps the low 64 bits of each lane product. -/
theorem intrinsic_mul256 (x y : V256) :
    evalIntrinsic (.vector (.mul64 256)) [.v256 x, .v256 y] =
      some (.v256 (zip256 (· * ·) x y)) := rfl
#print axioms intrinsic_mul256

/-- AVX-512DQ `MoveMask` gives the lane sign bits, like the AVX form. -/
theorem intrinsic_avx512dq_movemask256 (x : V256) :
    evalIntrinsic (.avx512DQ .moveMask64) [.v256 x] = some (.i32 (moveMask64 x)) := rfl
#print axioms intrinsic_avx512dq_movemask256

/-- `Vector256.Sum` adds the four lanes with wrapping. -/
theorem intrinsic_sum256 (x : V256) :
    evalIntrinsic (.vector (.sum64 256)) [.v256 x] =
      some (.i64 (lane64 x 0 + lane64 x 1 + lane64 x 2 + lane64 x 3)) := rfl
#print axioms intrinsic_sum256

/-- `Vector128.Sum` adds the two lanes with wrapping. -/
theorem intrinsic_sum128 (x : V128) :
    evalIntrinsic (.vector (.sum64 128)) [.v128 x] = some (.i64 (lane64 x 0 + lane64 x 1)) :=
  rfl
#print axioms intrinsic_sum128

/-- `Vector256.Sum` of packed lanes. -/
theorem intrinsic_sum256_pack256 (a0 a1 a2 a3 : W64) :
    evalIntrinsic (.vector (.sum64 256)) [.v256 (pack256 a0 a1 a2 a3)] =
      some (.i64 (a0 + a1 + a2 + a3)) := by
  rw [intrinsic_sum256, lane256_0, lane256_1, lane256_2, lane256_3]
#print axioms intrinsic_sum256_pack256

/-- `Vector128.Sum` of packed lanes. -/
theorem intrinsic_sum128_pack128 (a0 a1 : W64) :
    evalIntrinsic (.vector (.sum64 128)) [.v128 (pack128 a0 a1)] = some (.i64 (a0 + a1)) := by
  rw [intrinsic_sum128, lane128_0, lane128_1]
#print axioms intrinsic_sum128_pack128

/-! ### Carry and borrow sign bits from `ternaryLogic` -/

/-- The sign bit of truth table `0xD4` on `a`, `b` and `a + b` is the carry out of `a + b`. -/
theorem msb_ternary_add (a b : W64) :
    (ternaryLogic a b (a + b) 0xD4).msb = (a + b).ult a := by
  rw [ternary_add]
  simp only [BitVec.msb_or, BitVec.msb_and, BitVec.msb_not]
  simp only [BitVec.msb_eq_decide, Nat.reduceSub]
  have := a.isLt
  have := b.isLt
  by_cases aHigh : 2 ^ 63 ≤ a.toNat <;> by_cases bHigh : 2 ^ 63 ≤ b.toNat <;>
    by_cases highSum : 2 ^ 63 ≤ (a + b).toNat
  all_goals simp only [aHigh, bHigh, highSum, decide_true, decide_false]
  all_goals simp [BitVec.ult_eq_decide_lt, BitVec.lt_def]
  all_goals simp only [BitVec.toNat_add] at highSum ⊢
  all_goals omega
#print axioms msb_ternary_add

/-- The sign bit of truth table `0x8E` on `a`, `b` and `a - b` is the borrow out of `a - b`. -/
theorem msb_ternary_subtract (a b : W64) :
    (ternaryLogic a b (a - b) 0x8E).msb = a.ult b := by
  rw [ternary_subtract]
  simp only [BitVec.msb_or, BitVec.msb_and, BitVec.msb_not, BitVec.msb_xor]
  simp only [BitVec.msb_eq_decide, Nat.reduceSub]
  have := a.isLt
  have := b.isLt
  by_cases aHigh : 2 ^ 63 ≤ a.toNat <;> by_cases bHigh : 2 ^ 63 ≤ b.toNat <;>
    by_cases highDifference : 2 ^ 63 ≤ (a - b).toNat
  all_goals simp only [aHigh, bHigh, highDifference, decide_true, decide_false]
  all_goals simp [BitVec.ult_eq_decide_lt, BitVec.lt_def]
  all_goals simp only [BitVec.toNat_sub] at highDifference ⊢
  all_goals omega
#print axioms msb_ternary_subtract

end CIL.Vector
