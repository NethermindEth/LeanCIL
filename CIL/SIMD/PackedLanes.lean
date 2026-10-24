import CIL.SIMD.Evaluation256Lemmas
import CIL.SIMD.LaneCarry

/-!
# Packed-lane lemmas for integer intrinsics

Lane forms of the 128- and 256-bit integer intrinsics: lanewise maps and zips of `pack128` and
`pack256`, the numeric value of a packed vector, `moveMask64` as sign bits, the exact products
of `multiplyEven32`, `permute4x64`, shifts by immediate, `sum64` and the AVX-512DQ `mul64`.
On top of `LaneCarry` they give the carry and borrow repair of a wide addition or subtraction
done lane by lane, in the shapes that stepping `evalIntrinsic` produces.

None of these lemmas is `@[simp]`; consumers rewrite with them explicitly.
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
  | succ count ih =>
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
      ih (by omega), shifted]
    by_cases atCount : i = count
    · subst atCount
      simp
    · have below : decide (i < count + 1) = decide (i < count) :=
        decide_eq_decide.mpr (by omega)
      simp [atCount, below]

/-- Bit `i` of `moveMask64` is the sign bit of lane `i`; bits 4 and above are clear. -/
theorem getLsbD_moveMask64_eq (x : V256) (i : Nat) :
    (moveMask64 x).getLsbD i = (decide (i < 4) && (lane64 x i).msb) :=
  getLsbD_signFold (fun index => (lane64 x index).msb) 4 (by decide) i
#print axioms getLsbD_moveMask64_eq

/-- Bit `i` of `moveMask64` is the sign bit of lane `i`. -/
theorem getLsbD_moveMask64 (x : V256) {i : Nat} (lane : i < 4) :
    (moveMask64 x).getLsbD i = (lane64 x i).msb := by
  rw [getLsbD_moveMask64_eq, decide_eq_true lane, Bool.true_and]
#print axioms getLsbD_moveMask64

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
  rw [getLsbD_moveMask64 _ lane, lane64_zip256 _ _ _ lane, msb_mask64]
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
    sum compares below `x` (AVX-512 `CompareLessThan`), `propagate` lanes whose sum equals the
    all-ones vector (`CompareEqual`), and bit `i` of the cascade is the carry into lane `i`;
    bit 4 is the carry out of the whole sum. -/
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
    cascade is the borrow into lane `i`; bit 4 is the borrow out of the whole difference. -/
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

/-! ### Multiplication -/

/-- An even 32-bit lane is the low half of the 64-bit lane that holds it. -/
theorem lane32_even (x : BitVec n) (i : Nat) : lane32 x (2 * i) = (lane64 x i).setWidth 32 := by
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

/-- Control `0x1B` reverses the four lanes. -/
theorem permute4x64_reverse (a0 a1 a2 a3 : W64) :
    permute4x64 (pack256 a0 a1 a2 a3) (BitVec.ofNat 8 0x1B) = pack256 a3 a2 a1 a0 := by
  simp [permute4x64]
#print axioms permute4x64_reverse

/-- Control `0x4E` swaps the 128-bit halves. -/
theorem permute4x64_swap_halves (a0 a1 a2 a3 : W64) :
    permute4x64 (pack256 a0 a1 a2 a3) (BitVec.ofNat 8 0x4E) = pack256 a2 a3 a0 a1 := by
  simp [permute4x64]
#print axioms permute4x64_swap_halves

/-- Control `0x93` moves every lane up one place, the top lane wrapping to lane 0. -/
theorem permute4x64_rotate_up (a0 a1 a2 a3 : W64) :
    permute4x64 (pack256 a0 a1 a2 a3) (BitVec.ofNat 8 0x93) = pack256 a3 a0 a1 a2 := by
  simp [permute4x64]
#print axioms permute4x64_rotate_up

/-- Control `0x39` moves every lane down one place, lane 0 wrapping to the top. -/
theorem permute4x64_rotate_down (a0 a1 a2 a3 : W64) :
    permute4x64 (pack256 a0 a1 a2 a3) (BitVec.ofNat 8 0x39) = pack256 a1 a2 a3 a0 := by
  simp [permute4x64]
#print axioms permute4x64_rotate_down

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
