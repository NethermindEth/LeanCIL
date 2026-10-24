import CIL.Safety.SymbolicExecution
import CIL.SIMD.PackedLanes

/-!
# SIMD lane lemma tests

Checks the lane lemmas the way a multi-limb vector routine uses them: the carry cascade built
from intrinsic comparison masks reproduces the 256-bit sum and difference on concrete inputs
where a single repair hop is wrong and on symbolic inputs; intrinsic results on packed lanes
rewrite to their lane values; and a method steps through shift and multiply with them as facts.
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
example : (cascade cascading increment).getLsbD 2 = true := by decide
example : rippleSum cascading increment = cascading + increment := by decide
example : singleHopSum cascading increment ≠ cascading + increment := by decide
-- The cascade agrees with the true lane carry, so the lemma is not vacuous here.
example : BitVec.carry 128 cascading increment false = true := by decide

/-- For every input the cascade from intrinsic masks gives the 256-bit sum. -/
theorem rippleSum_eq_add (x y : V256) : rippleSum x y = x + y := by
  rw [add256_lanes x y, rippleSum, laneSums, show (cascade x y).getLsbD 1 = _ from
    cascade_add256 x y (i := 1) (by decide), show (cascade x y).getLsbD 2 = _ from
    cascade_add256 x y (i := 2) (by decide), show (cascade x y).getLsbD 3 = _ from
    cascade_add256 x y (i := 3) (by decide)]
  rfl
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
    pack256 0 7 9 1 - pack256 1 7 3 0 := by decide

/-- For every input the cascade from intrinsic masks gives the 256-bit difference. -/
theorem rippleDifference_eq_sub (x y : V256) : rippleDifference x y = x - y := by
  rw [sub256_lanes x y, rippleDifference, cascade_sub256 x y (i := 1) (by decide),
    cascade_sub256 x y (i := 2) (by decide), cascade_sub256 x y (i := 3) (by decide)]
  rfl
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
    some (.v256 0) := by decide

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
    pack256 0xFFFFFFFE00000001 0 0 0 := by decide

/-- Sign masks of comparison results are the flag bits. -/
example (p0 p1 p2 p3 : Bool) :
    (moveMask64 (pack256 (mask64 p0) (mask64 p1) (mask64 p2) (mask64 p3))).getLsbD 2 = p2 := by
  rw [getLsbD_moveMask64 _ (by decide), lane256_2, msb_mask64]

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

end Tests.SimdLanes
