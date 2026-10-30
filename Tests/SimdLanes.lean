import CIL.Safety.SymbolicExecution
import CIL.SIMD.PackedLanes

/-!
# SIMD lane lemma tests

Checks the lane lemmas the way a multi-limb vector routine uses them: the carry cascade built
from intrinsic comparison masks reproduces the 256-bit sum and difference on concrete inputs
where a single repair hop is wrong and on symbolic inputs; intrinsic results on packed lanes
rewrite to their lane values; and a method steps through shift and multiply with them as facts.
The byte shuffles are pinned on concrete vectors that a bit-7 or lane-crossing mutant fails.
-/

open CIL CIL.Vector

namespace Tests.SimdLanes

/-- All ones in a 64-bit lane. -/
private abbrev ones : W64 := BitVec.allOnes 64

/-- A 0-or-1 lane from a flag bit. -/
private def bit (flag : Bool) : W64 := if flag then 1 else 0

/-- The lane sums of `x + y`, as `Avx2.Add` computes them. -/
private def laneSums (x y : V256) : V256 := zip256 (· + ·) x y

/-- Lanes whose sum wraps, as AVX-512 `CompareLessThan` against `x` marks them. -/
private def generated (x y : V256) : W32 :=
  moveMask64 (zip256 (fun a b => mask64 (a.ult b)) (laneSums x y) x)

/-- Lanes whose sum is all ones, as `CompareEqual` against `Vector256.AllBitsSet` marks them. -/
private def propagated (x y : V256) : W32 :=
  moveMask64 (zip256 (fun a b => mask64 (a == b)) (laneSums x y) (~~~0))

/-- The packed-flag carry lookahead: bit `i` is the carry into lane `i`. -/
private def cascade (x y : V256) : W32 :=
  propagated x y ^^^ (propagated x y + (generated x y <<< 1))

/-- The vector routine: lane sums plus the cascaded carries. -/
private def rippleSum (x y : V256) : V256 :=
  zip256 (· + ·) (laneSums x y) (pack256 0 (bit ((cascade x y).getLsbD 1))
    (bit ((cascade x y).getLsbD 2)) (bit ((cascade x y).getLsbD 3)))

/-- A single repair hop: lane sums less the shifted carry masks, without the cascade. -/
private def singleHopSum (x y : V256) : V256 :=
  zip256 (· - ·) (laneSums x y)
    (pack256 0 (mask64 ((lane64 x 0 + lane64 y 0).ult (lane64 x 0)))
      (mask64 ((lane64 x 1 + lane64 y 1).ult (lane64 x 1)))
      (mask64 ((lane64 x 2 + lane64 y 2).ult (lane64 x 2))))

/-- Two all-ones low lanes: adding one carries out of lane 0, across lane 1, into lane 2. -/
private def cascading : V256 := pack256 ones ones 5 0
/-- One, which carries out of lane 0 of `cascading`. -/
private def increment : V256 := pack256 1 0 0 0

-- The cascade reaches lane 2, which the single hop misses: the lookahead is what is correct.
example : (cascade cascading increment).getLsbD 2 = true := by decide +kernel
example : rippleSum cascading increment = cascading + increment := by decide +kernel
example : singleHopSum cascading increment ≠ cascading + increment := by decide +kernel
-- The cascade agrees with the true lane carry, so the lemma is not vacuous here.
example : BitVec.carry 128 cascading increment false = true := by decide +kernel

/-- For every input the cascade from intrinsic masks gives the 256-bit sum. -/
theorem rippleSum_eq_add (x y : V256) : rippleSum x y = x + y :=
  (add256_cascade x y).symm
/--
info: 'Tests.SimdLanes.rippleSum_eq_add' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rippleSum_eq_add

/-- Bit 4 of the cascade is the unsigned overflow of the 256-bit sum. -/
theorem cascade_overflow (x y : V256) :
    (cascade x y).getLsbD 4 = decide (2 ^ 256 ≤ x.toNat + y.toNat) := by
  rw [show (cascade x y).getLsbD 4 = _ from cascade_add256 x y (i := 4) (by decide)]
  exact carry_width x y
#print axioms cascade_overflow

/-- The vector subtraction routine: lane differences less the cascaded borrows. -/
private def rippleDifference (x y : V256) : V256 :=
  let generate := moveMask64 (zip256 (fun a b => mask64 (a.ult b)) x y)
  let propagate := moveMask64 (zip256 (fun a b => mask64 (a == b)) x y)
  let borrows := propagate ^^^ (propagate + (generate <<< 1))
  zip256 (· - ·) (zip256 (· - ·) x y)
    (pack256 0 (bit (borrows.getLsbD 1)) (bit (borrows.getLsbD 2)) (bit (borrows.getLsbD 3)))

-- A borrow out of lane 0 crosses the equal lane 1 into lane 2.
example : rippleDifference (pack256 0 7 9 1) (pack256 1 7 3 0) =
    pack256 0 7 9 1 - pack256 1 7 3 0 := by decide +kernel

/-- For every input the cascade from intrinsic masks gives the 256-bit difference. -/
theorem rippleDifference_eq_sub (x y : V256) : rippleDifference x y = x - y :=
  (sub256_cascade x y).symm
/--
info: 'Tests.SimdLanes.rippleDifference_eq_sub' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rippleDifference_eq_sub

/-- The final borrow is the unsigned comparison of the whole vectors. -/
example (x y : V256) :
    (moveMask64 (zip256 (fun a b => mask64 (a == b)) x y) ^^^
      (moveMask64 (zip256 (fun a b => mask64 (a == b)) x y) +
        (moveMask64 (zip256 (fun a b => mask64 (a.ult b)) x y) <<< 1))).getLsbD 4 =
      x.ult y := by
  rw [cascade_sub256 x y (i := 4) (by decide)]
  exact subBorrow_width x y

/-- Packed lanes are digits: the lane recipe's value is the wide sum's value. -/
example (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    (pack256 a0 a1 a2 a3 + pack256 b0 b1 b2 b3).toNat =
      (a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat +
        (b0.toNat + 2 ^ 64 * b1.toNat + 2 ^ 128 * b2.toNat + 2 ^ 192 * b3.toNat)) % 2 ^ 256 := by
  rw [BitVec.toNat_add, toNat_pack256, toNat_pack256]

/-! ### Stepped intrinsic results on packed lanes -/

/-- Shifting each lane by an immediate, as stepping leaves it. -/
example (a0 a1 a2 a3 : W64) :
    evalIntrinsic (.avx2 .shr64) [.v256 (pack256 a0 a1 a2 a3), .i32 (BitVec.ofNat 32 32)] =
      some (.v256 (pack256 (a0 >>> 32) (a1 >>> 32) (a2 >>> 32) (a3 >>> 32))) := by
  rw [intrinsic_shr256 _ (by decide), map256_pack256]

example (a0 a1 a2 a3 : W64) :
    evalIntrinsic (.avx2 .shl64) [.v256 (pack256 a0 a1 a2 a3), .i32 (BitVec.ofNat 32 32)] =
      some (.v256 (pack256 (a0 <<< 32) (a1 <<< 32) (a2 <<< 32) (a3 <<< 32))) := by
  rw [intrinsic_shl256 _ (by decide), map256_pack256]

-- A count of 64 or more clears the lane rather than wrapping the count.
example : evalIntrinsic (.avx2 .shl64) [.v256 (pack256 1 2 3 4), .i32 (BitVec.ofNat 32 64)] =
    some (.v256 0) := by decide +kernel

/-- Reversing the lanes with `Permute4x64`. -/
example (a0 a1 a2 a3 : W64) :
    evalIntrinsic (.avx2 .permute4x64) [.v256 (pack256 a0 a1 a2 a3), .i32 (BitVec.ofNat 32 27)] =
      some (.v256 (pack256 a3 a2 a1 a0)) := by
  rw [intrinsic_permute4x64 _ (by decide), permute4x64_reverse]

/-- `Vector256.Sum` of packed lanes. -/
example (a0 a1 a2 a3 : W64) :
    evalIntrinsic (.vector (.sum64 256)) [.v256 (pack256 a0 a1 a2 a3)] =
      some (.i64 (a0 + a1 + a2 + a3)) :=
  intrinsic_sum256_pack256 a0 a1 a2 a3

/-- AVX-512DQ lane products on packed lanes. -/
example (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    evalIntrinsic (.avx512DQ .mul64) [.v256 (pack256 a0 a1 a2 a3), .v256 (pack256 b0 b1 b2 b3)] =
      some (.v256 (pack256 (a0 * b0) (a1 * b1) (a2 * b2) (a3 * b3))) := by
  rw [intrinsic_avx512dq_mul256, multiplyLow64_pack256]

/-- The even-lane product is exact: a 32-by-32-bit partial product never wraps. -/
theorem even_product_exact (x y : V256) {i : Nat} (lane : i < 4) :
    (lane64 (multiplyEven32 x y) i).toNat =
      (lane64 x i).toNat % 2 ^ 32 * ((lane64 y i).toNat % 2 ^ 32) := by
  rw [lane64_multiplyEven32 x y lane, toNat_even_product]
#print axioms even_product_exact

-- The low 32-bit halves multiply to more than 2^63, so the product fills the 64-bit lane.
example : multiplyEven32 (pack256 0xFFFFFFFF 0 0 0) (pack256 0xFFFFFFFF 0 0 0) =
    pack256 0xFFFFFFFE00000001 0 0 0 := by decide +kernel

/-- Sign masks of comparison results are the flag bits. -/
example (p0 p1 p2 p3 : Bool) :
    (moveMask64 (pack256 (mask64 p0) (mask64 p1) (mask64 p2) (mask64 p3))).getLsbD 2 = p2 := by
  rw [getLsbD_moveMask64_of_lt _ (by decide), lane256_2, msb_mask64]

/-- The 512-bit sign mask has one bit per lane and nothing above lane 7. -/
example (x : V512) : (moveMask512 x).getLsbD 8 = false := by
  rw [getLsbD_moveMask512]
  rfl

/-- The AVX-512 carry sign from `TernaryLogic` table `0xD4` broadcast to a lane mask. -/
example (a b : W64) :
    (ternaryLogic a b (a + b) 0xD4).sshiftRight 63 = mask64 ((a + b).ult a) := by
  rw [arithmetic_sign_mask, msb_ternary_add]

/-- Subtracting a shifted carry mask adds the carry. -/
example (sum : W64) (a b : W64) :
    sum - mask64 ((a + b).ult a) = sum + bit (decide (2 ^ 64 ≤ a.toNat + b.toNat)) := by
  rw [sub_mask64, add_ult_eq_overflow]
  rfl

/-! ### Lane projections -/

/-- 128-bit lanewise operations and maps on packed lanes. -/
example (a0 a1 b0 b1 : W64) :
    zip128 (· * ·) (pack128 a0 a1) (pack128 b0 b1) = pack128 (a0 * b0) (a1 * b1) :=
  zip128_pack128 _ a0 a1 b0 b1

example (a0 a1 : W64) : map128 (· >>> 1) (pack128 a0 a1) = pack128 (a0 >>> 1) (a1 >>> 1) :=
  map128_pack128 _ a0 a1

/-- `Vector128.Sum` of packed lanes. -/
example (a0 a1 : W64) :
    evalIntrinsic (.vector (.sum64 128)) [.v128 (pack128 a0 a1)] = some (.i64 (a0 + a1)) :=
  intrinsic_sum128_pack128 a0 a1

/-- The sign mask of four comparisons is their 4-bit flag word. -/
example : moveMask64 (pack256 (mask64 true) (mask64 false) (mask64 true) (mask64 true)) =
    BitVec.ofNat 32 13 := by
  rw [moveMask64_pack256_mask64]
  rfl

/-- AVX-512DQ lane products, lane by lane. -/
example (x y : V256) : lane64 (multiplyLow64 x y) 3 = lane64 x 3 * lane64 y 3 :=
  lane64_multiplyLow64 x y (by decide)

/-- 512-bit lanewise operations, lane by lane. -/
example (x y : V512) : lane64 (zip512 (· + ·) x y) 7 = lane64 x 7 + lane64 y 7 :=
  lane64_zip512 _ x y (by decide)

/-- Bitwise operations act lane by lane. -/
example (x y : V256) :
    lane64 (x ^^^ (x &&& y)) 1 = lane64 x 1 ^^^ (lane64 x 1 &&& lane64 y 1) := by
  rw [lane64_xor, lane64_and]

/-- A shift by a vector count of 64 or more clears the lane. -/
example (x : V256) : lane64 (shiftLeftCount64 x 64) 2 = 0 := by
  rw [lane64_shiftLeftCount64 _ _ (by decide)]
  rfl

example (x : V256) : lane64 (shiftRightCount64 x 3) 2 = lane64 x 2 >>> 3 := by
  rw [lane64_shiftRightCount64 _ _ (by decide)]
  rfl

/-- A shift by a vector count under 64 shifts the lane. -/
example (x : V256) : lane64 (shiftLeftCount64 x 5) 1 = lane64 x 1 <<< 5 := by
  rw [lane64_shiftLeftCount64 _ _ (by decide)]
  rfl

/-- A logical right shift by a vector count of 64 clears the lane. -/
example (x : V256) : lane64 (shiftRightCount64 x 64) 0 = 0 := by
  rw [lane64_shiftRightCount64 _ _ (by decide)]
  rfl

/-- Or and and-not act lane by lane, as a mask blend `(m &&& a) ||| (~~~m &&& b)` needs. -/
example (mask x y : V256) :
    lane64 ((mask &&& x) ||| ((~~~mask) &&& y)) 3 =
      (lane64 mask 3 &&& lane64 x 3) ||| ((~~~lane64 mask 3) &&& lane64 y 3) := by
  rw [lane64_or, lane64_and, lane64_andNot]

/-! ### Lane carries, borrows and masks -/

/-- The 128-bit sum through its lane form: the high lane takes the low lane's carry. -/
example (x y : V128) :
    lane64 (x + y) 1 = lane64 x 1 + lane64 y 1 + (if BitVec.carry 64 x y false then 1 else 0) := by
  rw [add128_lanes, zip128, zip128, lane128_1, lane128_1, lane128_1]

/-- The 128-bit difference through its lane form: the high lane pays the low lane's borrow. -/
example (x y : V128) :
    lane64 (x - y) 1 = lane64 x 1 - lane64 y 1 - (if subBorrow 64 x y then 1 else 0) := by
  rw [sub128_lanes, zip128, zip128, lane128_1, lane128_1, lane128_1]

-- A 128-bit carry out of the low lane, concretely.
example : (pack128 (BitVec.allOnes 64) 4 + pack128 1 0) = pack128 0 5 := by decide +kernel

/-- Without an all-ones lane on the way, one repair hop gives the next carry. -/
example (x y : V256) (notFull : (lane64 x 1 + lane64 y 1 == BitVec.allOnes 64) = false) :
    BitVec.carry (64 * (1 + 1)) x y false = (lane64 x 1 + lane64 y 1).ult (lane64 x 1) :=
  carry_lane_succ_of_isolated x y 1 (by rw [notFull, Bool.false_and])

/-- Without an equal lane on the way, one repair hop gives the next borrow. -/
example (x y : V256) (differ : (lane64 x 1 == lane64 y 1) = false) :
    subBorrow (64 * (1 + 1)) x y = (lane64 x 1).ult (lane64 y 1) :=
  subBorrow_lane_succ_of_isolated x y 1 (by rw [differ, Bool.false_and])

/-- Adding a borrow mask subtracts the borrow. -/
example (difference a b : W64) :
    difference + mask64 (a.ult b) = difference - bit (a.ult b) := by
  rw [add_mask64]
  rfl

/-- Masking a propagate mask with a generate mask keeps lanes that do both. -/
example (p q : Bool) : mask64 p &&& mask64 q = mask64 (p && q) := mask64_and_mask64 p q

-- The doubled generate word, as C# writes `generate * 2`, gives the same cascade.
example (x y : V256) :
    (propagated x y ^^^ (propagated x y + 2 * generated x y)).getLsbD 2 =
      BitVec.carry 128 x y false := by
  rw [two_mul_eq_shiftLeft]
  exact cascade_add256 x y (i := 2) (by decide)

/-- The borrow sign from `TernaryLogic` table `0x8E` broadcast to a lane mask. -/
example (a b : W64) : (ternaryLogic a b (a - b) 0x8E).sshiftRight 63 = mask64 (a.ult b) := by
  rw [arithmetic_sign_mask, msb_ternary_subtract]

/-- Lane `i` of `Permute4x64` reads the lane its control bits name. -/
example (x : V256) : lane64 (permute4x64 x (BitVec.ofNat 8 0x1B)) 0 = lane64 x 3 := by
  rw [lane64_permute4x64 _ _ (by decide)]
  rfl

/-- Signed comparison of lanes, as `Avx2.CompareGreaterThan` produces it. -/
example (x y : V256) :
    lane64 (zip256 (fun a b => mask64 (decide (b.toInt < a.toInt))) x y) 2 =
      mask64 (decide ((lane64 y 2).toInt < (lane64 x 2).toInt)) :=
  lane64_signedgt256 x y (by decide)

-- The signed mask differs from the unsigned one on a lane with its top bit set.
example : zip256 (fun a b => mask64 (decide (b.toInt < a.toInt))) (pack256 (BitVec.allOnes 64)
    0 0 0) 0 = 0 := by decide +kernel

/-! ### Intrinsic evaluation on packed lanes -/

/-- AVX2 lane addition evaluates to the lanewise sums of packed operands. -/
example (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    evalIntrinsic (.avx2 .add64) [.v256 (pack256 a0 a1 a2 a3), .v256 (pack256 b0 b1 b2 b3)] =
      some (.v256 (pack256 (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3))) := by
  rw [intrinsic_avx2_add256, zip256_pack256]

/-- AVX2 equality evaluates to one all-ones or zero mask per packed lane. -/
example (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    evalIntrinsic (.avx2 .eq64) [.v256 (pack256 a0 a1 a2 a3), .v256 (pack256 b0 b1 b2 b3)] =
      some (.v256 (pack256 (mask64 (a0 == b0)) (mask64 (a1 == b1))
        (mask64 (a2 == b2)) (mask64 (a3 == b3)))) := by
  rw [intrinsic_avx2_eq256, zip256_pack256]

/-- AVX-512 unsigned less-than evaluates to one mask per packed lane. -/
example (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    evalIntrinsic (.avx512 .ltu64)
        [.v256 (pack256 a0 a1 a2 a3), .v256 (pack256 b0 b1 b2 b3)] =
      some (.v256 (pack256 (mask64 (a0.ult b0)) (mask64 (a1.ult b1))
        (mask64 (a2.ult b2)) (mask64 (a3.ult b3)))) := by
  rw [intrinsic_avx512_ltu256, zip256_pack256]

/-- AVX2 signed greater-than masks exactly the lanes where the first operand is larger. -/
example (x y : V256) {i : Nat} (lane : i < 4) (value : V256)
    (evaluated : evalIntrinsic (.avx2 .signedgt64) [.v256 x, .v256 y] = some (.v256 value)) :
    lane64 value i = mask64 (decide ((lane64 y i).toInt < (lane64 x i).toInt)) := by
  rw [intrinsic_avx2_signedgt256] at evaluated
  cases evaluated
  exact lane64_signedgt256 x y lane

/-- The portable lane multiply evaluates to the wrapping lanewise products. -/
example (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    evalIntrinsic (.vector (.mul64 256))
        [.v256 (pack256 a0 a1 a2 a3), .v256 (pack256 b0 b1 b2 b3)] =
      some (.v256 (pack256 (a0 * b0) (a1 * b1) (a2 * b2) (a3 * b3))) := by
  rw [intrinsic_mul256, zip256_pack256]

/-- AVX-512DQ `MoveMask` of a packed mask vector gathers the four conditions as bits. -/
example (lane0 lane1 lane2 lane3 : Bool) :
    evalIntrinsic (.avx512DQ .moveMask64)
        [.v256 (pack256 (mask64 lane0) (mask64 lane1) (mask64 lane2) (mask64 lane3))] =
      some (.i32 (BitVec.ofNat 32
        (lane0.toNat + 2 * lane1.toNat + 4 * lane2.toNat + 8 * lane3.toNat))) := by
  rw [intrinsic_avx512dq_movemask256, moveMask64_pack256_mask64]

/-! ### Stepping a method through the intrinsics -/

/-- Shifts the high halves of one vector down and multiplies them by the low halves of
    another: one partial-product row of a multi-limb multiply. -/
@[cil_code] def partialProductMethod : CIL.Method := {
  profile := { architecture := .x64, avx2 := true }
  code := [.intrinsic (.avx2 .shr64) 2, .intrinsic (.avx2 .multiplyEven32) 2, .ret]
  locals := [], returnsValue := true }

/-- The program holding `partialProductMethod`. -/
@[cil_code] def partialProductProgram : CIL.Program := [partialProductMethod]

/-- Stepping the method on packed lanes with the lane lemmas as facts leaves the lanewise
    products of low halves by shifted high halves on the stack. -/
theorem partial_product_steps (a0 a1 a2 a3 b0 b1 b2 b3 : W64) (memory : CIL.Safety.Memory)
    (finish : Except CIL.Safety.LocatedFault (CIL.Safety.Memory × List CIL.Safety.Value))
    (rest : CIL.Safety.run partialProductProgram 1 0 2 []
      { activation := 0, locals := [], owned := [] }
      [.scalar (.v256 (pack256
        ((a0.setWidth 32).zeroExtend 64 * ((b0 >>> 32).setWidth 32).zeroExtend 64)
        ((a1.setWidth 32).zeroExtend 64 * ((b1 >>> 32).setWidth 32).zeroExtend 64)
        ((a2.setWidth 32).zeroExtend 64 * ((b2 >>> 32).setWidth 32).zeroExtend 64)
        ((a3.setWidth 32).zeroExtend 64 * ((b3 >>> 32).setWidth 32).zeroExtend 64)))]
      memory = finish) :
    CIL.Safety.run partialProductProgram 3 0 0 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.i32 (BitVec.ofInt 32 32)), .scalar (.v256 (pack256 b0 b1 b2 b3)),
        .scalar (.v256 (pack256 a0 a1 a2 a3))] memory = finish := by
  cil_checked_run_step [intrinsic_shr256 (pack256 b0 b1 b2 b3) (count := 32) (by decide),
    map256_pack256]
  cil_checked_run_step [intrinsic_multiplyEven32, multiplyEven32_pack256]
  with_reducible exact rest
#print axioms partial_product_steps

/-! ### Wide carry cascades and broadcast sources -/

/-- A carry generated in lane zero propagates through all eight lanes and out of the word. -/
theorem cascade512_full_carry :
    let left : V512 := ~~~0
    let right := pack512 1 0 0 0 0 0 0 0
    let sum := zip512 (· + ·) left right
    let generate := moveMask512 (zip512 (fun a b => mask64 (a.ult b)) sum left)
    let propagate := moveMask512 (zip512 (fun a b => mask64 (a == b)) sum (~~~0))
    (propagate ^^^ (propagate + (generate <<< 1))) = 510 := by
  decide +kernel
#print axioms cascade512_full_carry

/-- Subtracting one from zero borrows through all eight lanes, including the outgoing bit. -/
theorem cascade512_full_borrow :
    let left : V512 := 0
    let right := pack512 1 0 0 0 0 0 0 0
    let generate := moveMask512 (zip512 (fun a b => mask64 (a.ult b)) left right)
    let propagate := moveMask512 (zip512 (fun a b => mask64 (a == b)) left right)
    (propagate ^^^ (propagate + (generate <<< 1))) = 510 := by
  decide +kernel
#print axioms cascade512_full_borrow

/-- A generated carry is not a carry-in to the lane that generated it. -/
theorem cascade_rejects_unshifted_generate :
    let generate : W32 := 1
    let propagate : W32 := 254
    propagate ^^^ (propagate + generate) ≠
      propagate ^^^ (propagate + (generate <<< 1)) := by
  decide +kernel
#print axioms cascade_rejects_unshifted_generate

/-- Lane-local sums without overflow produce no cascade bits. -/
theorem cascade512_no_carry :
    let left := pack512 1 2 3 4 5 6 7 8
    let right := pack512 8 7 6 5 4 3 2 1
    let sum := zip512 (· + ·) left right
    let generate := moveMask512 (zip512 (fun a b => mask64 (a.ult b)) sum left)
    let propagate := moveMask512 (zip512 (fun a b => mask64 (a == b)) sum (~~~0))
    (propagate ^^^ (propagate + (generate <<< 1))) = 0 := by
  decide +kernel
#print axioms cascade512_no_carry

/-- A broadcast `create64` produces exactly the all-ones propagate comparand. -/
theorem broadcast_all_ones :
    evalIntrinsic (.vector (.create64 256)) [.i64 (~~~0)] = some (.v256 (~~~0)) := by
  change some (CIL.Value.v256 (pack256 (~~~0) (~~~0) (~~~0) (~~~0))) = _
  rw [pack256_allOnes]
#print axioms broadcast_all_ones

/-- The greater-than source and broadcast comparand recover the outgoing 256-bit carry. -/
theorem broadcast_gtu_outgoing (left right : V256) :
    let sum := zip256 (· + ·) left right
    let generate := moveMask64 (zip256 (fun a b => mask64 (b.ult a)) right sum)
    let propagate := moveMask64 (zip256 (fun a b => mask64 (a == b)) sum
      (pack256 (~~~0) (~~~0) (~~~0) (~~~0)))
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD 4 =
      BitVec.carry 256 left right false := by
  exact cascade_add256_gtu_broadcast left right (by decide)
#print axioms broadcast_gtu_outgoing

/-- The existing AVX-512 greater-than intrinsic supplies the operand-swapped generate mask. -/
theorem gtu_intrinsic_cascade (left right comparison : V256)
    (evaluated : evalIntrinsic (.avx512 .gtu64)
      [.v256 right, .v256 (zip256 (· + ·) left right)] = some (.v256 comparison)) :
    let propagate := moveMask64 (zip256 (fun a b => mask64 (a == b))
      (zip256 (· + ·) left right) (pack256 (~~~0) (~~~0) (~~~0) (~~~0)))
    (propagate ^^^ (propagate + (moveMask64 comparison <<< 1))).getLsbD 4 =
      BitVec.carry 256 left right false := by
  change some (CIL.Value.v256
    (zip256 (fun a b => mask64 (b.ult a)) right (zip256 (· + ·) left right))) =
      some (.v256 comparison) at evaluated
  cases evaluated
  exact cascade_add256_gtu_broadcast left right (by decide)
#print axioms gtu_intrinsic_cascade

/-- Bytes `0` to `31` in order: byte `i` of the vector is `i`. -/
private def ascending : V256 :=
  BitVec.ofNat 256 0x1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100

/-- Control bytes `0` to `15` in each half; a lane-crossing shuffle reads the low half twice. -/
private def laneIdentity : V256 :=
  BitVec.ofNat 256 0x0f0e0d0c0b0a090807060504030201000f0e0d0c0b0a09080706050403020100

/-- Even control bytes set bit 7 over a reversing index; odd bytes keep the bare index. -/
private def evenZeroed : V256 :=
  BitVec.ofNat 256 0x8102830485068708890a8b0c8d0e8f008102830485068708890a8b0c8d0e8f

/-- The int256 big-endian control: indices 31 down to 0, whose bit 4 the shuffle ignores. -/
private def int256Reversal : V256 :=
  pack256 0x18191a1b1c1d1e1f 0x1011121314151617 0x08090a0b0c0d0e0f 0x0001020304050607

/-- Bytes 31 down to 0. -/
private def descending : V256 :=
  BitVec.ofNat 256 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f

/-- A shuffle that drops the bit-7 zeroing rule. -/
private def ignoreBit7 (source control : V256) : V256 :=
  (List.range 32).foldl (fun result index =>
    let half := index / 16
    let selector := (lane8 control index).extractLsb' 0 4
    let byte := lane8 source (16 * half + selector.toNat)
    result ||| (byte.zeroExtend 256 <<< (8 * index))) 0

/-- A shuffle that indexes all 32 bytes with five control bits, crossing the halves. -/
private def crossLane (source control : V256) : V256 :=
  (List.range 32).foldl (fun result index =>
    let selector := lane8 control index
    let byte := if selector.msb then 0 else lane8 source (selector.extractLsb' 0 5).toNat
    result ||| (byte.zeroExtend 256 <<< (8 * index))) 0

/-- Each half selects within itself: the upper half of the result reads source bytes 16-31. -/
theorem shuffle_lane_identity : shuffleBytes256 ascending laneIdentity = ascending := by
  decide +kernel
#print axioms shuffle_lane_identity

/-- A set bit 7 zeroes its byte; a clear one selects by the low four bits. -/
theorem shuffle_bit7_zeroes : shuffleBytes256 ascending evenZeroed = BitVec.ofNat 256
    0x100012001400160018001a001c001e00000002000400060008000a000c000e00 := by
  decide +kernel
#print axioms shuffle_bit7_zeroes

/-- int256's control reverses each half; swapping the halves completes the 32-byte reversal. -/
theorem shuffle_int256_reversal :
    permute4x64 (shuffleBytes256 ascending int256Reversal) 0x4E = descending := by
  decide +kernel
#print axioms shuffle_int256_reversal

/-- `Avx2.Shuffle` and `Ssse3.Shuffle` evaluate to the shared per-half model. -/
theorem shuffle_intrinsics :
    evalIntrinsic (.avx2 .shuffleBytes) [.v256 ascending, .v256 evenZeroed] =
      some (.v256 (BitVec.ofNat 256
        0x100012001400160018001a001c001e00000002000400060008000a000c000e00)) ∧
    evalIntrinsic (.sse .shuffleBytes)
      [.v128 (ascending.extractLsb' 0 128), .v128 (evenZeroed.extractLsb' 0 128)] =
      some (.v128 0x2000400060008000a000c000e00) := by
  decide +kernel
#print axioms shuffle_intrinsics

/-- The pinned vectors reject a model that ignores bit 7 or crosses halves. -/
theorem shuffle_mutants_rejected :
    ignoreBit7 ascending evenZeroed ≠ shuffleBytes256 ascending evenZeroed ∧
    crossLane ascending laneIdentity ≠ shuffleBytes256 ascending laneIdentity ∧
    crossLane ascending int256Reversal ≠ shuffleBytes256 ascending int256Reversal := by
  decide +kernel
#print axioms shuffle_mutants_rejected

/-- The low half of a concatenation is its second operand. -/
private theorem append_low (high low : V128) : (high ++ low).extractLsb' 0 128 = low := by
  ext i hi
  rw [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  simp [hi, BitVec.getLsbD_eq_getElem]
#print axioms append_low

/-- The high half of a concatenation is its first operand. -/
private theorem append_high (high low : V128) : (high ++ low).extractLsb' 128 128 = high := by
  ext i hi
  rw [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  simp [hi, BitVec.getLsbD_eq_getElem]
#print axioms append_high

/-- The low result half depends only on the low source and control halves. -/
theorem shuffle_low_half (source control : V256) :
    (shuffleBytes256 source control).extractLsb' 0 128 =
      shuffleBytes128 (source.extractLsb' 0 128) (control.extractLsb' 0 128) :=
  append_low _ _
#print axioms shuffle_low_half

/-- The high result half depends only on the high source and control halves. -/
theorem shuffle_high_half (source control : V256) :
    (shuffleBytes256 source control).extractLsb' 128 128 =
      shuffleBytes128 (source.extractLsb' 128 128) (control.extractLsb' 128 128) :=
  append_high _ _
#print axioms shuffle_high_half

end Tests.SimdLanes
