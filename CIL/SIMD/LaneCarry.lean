import CIL.SIMD.Vector

/-!
# Carries and borrows across 64-bit lanes

Multi-limb arithmetic on vectors adds or subtracts 64-bit lanes independently and then repairs
each lane with the carry or borrow out of the lanes below it. This file states that repair on
the model's own terms: the lanes of a wide `x + y` or `x - y` are the lane sums or differences
corrected by `BitVec.carry` or `subBorrow` at the lane boundary; that correction obeys the
generate/propagate recurrence (a lane generates when its sum wraps, and propagates when its sum
is all ones); and the packed-flag form `propagate ^^^ (propagate + (generate <<< 1))` computes
the whole cascade at once. The `mask64` identities turn comparison masks into those corrections.

None of these lemmas is `@[simp]`; consumers rewrite with them explicitly.
-/

namespace CIL.Vector

/-! ### Lane values -/

/-- A 64-bit lane is the corresponding base-`2^64` digit of the whole vector. -/
theorem toNat_lane64 (x : BitVec w) (i : Nat) :
    (lane64 x i).toNat = x.toNat / 2 ^ (64 * i) % 2 ^ 64 := by
  simp [lane64, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
#print axioms toNat_lane64

/-- The low `a + 64` bits of `n` are its low `a` bits plus the 64-bit digit above them. -/
private theorem mod_two_pow_add_lane (n a : Nat) :
    n % 2 ^ (a + 64) = n % 2 ^ a + 2 ^ a * (n / 2 ^ a % 2 ^ 64) := by
  rw [Nat.pow_add]
  exact Nat.mod_mul
#print axioms mod_two_pow_add_lane

/-- Comparing whole multiples of `scale` against a value whose remainder is below `scale`. -/
private theorem scale_le_iff {scale low needed held : Nat} (small : low < scale) :
    scale * needed ≤ low + scale * held ↔ needed ≤ held := by
  constructor
  · intro bound
    apply Nat.le_of_not_lt
    intro above
    have := Nat.mul_le_mul_left scale (Nat.succ_le_of_lt above)
    rw [Nat.mul_succ] at this
    omega
  · intro bound
    have := Nat.mul_le_mul_left scale bound
    omega
#print axioms scale_le_iff

/-- The carry out of digit `i` given the carry into it. -/
theorem carry_lane_succ (x y : BitVec w) (i : Nat) :
    BitVec.carry (64 * (i + 1)) x y false =
      ((lane64 x i + lane64 y i).ult (lane64 x i) ||
        (lane64 x i + lane64 y i == BitVec.allOnes 64 && BitVec.carry (64 * i) x y false)) := by
  have positive : 0 < 2 ^ (64 * i) := Nat.two_pow_pos _
  have xLowBound := Nat.mod_lt x.toNat positive
  have yLowBound := Nat.mod_lt y.toNat positive
  have xDigitBound := Nat.mod_lt (x.toNat / 2 ^ (64 * i)) (Nat.two_pow_pos 64)
  have yDigitBound := Nat.mod_lt (y.toNat / 2 ^ (64 * i)) (Nat.two_pow_pos 64)
  have allOnes : ∀ v : W64, (v == BitVec.allOnes 64) = decide (v.toNat = 2 ^ 64 - 1) := by
    intro v
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj,
      BitVec.toNat_allOnes]
  unfold BitVec.carry
  rw [Nat.mul_succ, mod_two_pow_add_lane x.toNat, mod_two_pow_add_lane y.toNat, allOnes]
  simp only [BitVec.ult_eq_decide_lt, BitVec.lt_def, BitVec.toNat_add, toNat_lane64,
    Bool.toNat_false, Nat.add_zero, Nat.pow_add]
  generalize x.toNat % 2 ^ (64 * i) = xLow at *
  generalize y.toNat % 2 ^ (64 * i) = yLow at *
  generalize x.toNat / 2 ^ (64 * i) % 2 ^ 64 = xDigit at *
  generalize y.toNat / 2 ^ (64 * i) % 2 ^ 64 = yDigit at *
  generalize 2 ^ (64 * i) = scale at *
  simp only [ge_iff_le]
  by_cases wraps : scale ≤ xLow + yLow
  · have split : xLow + scale * xDigit + (yLow + scale * yDigit) =
        (xLow + yLow - scale) + scale * (xDigit + yDigit + 1) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
    simp only [split, scale_le_iff (show xLow + yLow - scale < scale by omega), wraps,
      decide_true, Bool.and_true]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_iff]
    omega
  · have split : xLow + scale * xDigit + (yLow + scale * yDigit) =
        (xLow + yLow) + scale * (xDigit + yDigit) := by
      rw [Nat.mul_add]
      omega
    simp only [split, scale_le_iff (show xLow + yLow < scale by omega), wraps, decide_false,
      Bool.and_false, Bool.or_false]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    omega
#print axioms carry_lane_succ

/-- The digits of `x + y` above weight `scale`: digit sums plus the carry out of the low part. -/
private theorem add_div_scale (x y scale : Nat) (positive : 0 < scale) :
    (x + y) / scale = (x % scale + y % scale) / scale + (x / scale + y / scale) := by
  conv => lhs; rw [← Nat.mod_add_div x scale, ← Nat.mod_add_div y scale]
  rw [show x % scale + scale * (x / scale) + (y % scale + scale * (y / scale)) =
    (x % scale + y % scale) + scale * (x / scale + y / scale) by rw [Nat.mul_add]; omega,
    Nat.add_mul_div_left _ _ positive]
#print axioms add_div_scale

/-- The quotient of a sum of two remainders is the carry bit between them. -/
private theorem low_sum_div (xLow yLow scale : Nat) (xSmall : xLow < scale)
    (ySmall : yLow < scale) :
    (xLow + yLow) / scale = if scale ≤ xLow + yLow then 1 else 0 := by
  split
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)
#print axioms low_sum_div

/-- A 0-or-1 word built from a condition. -/
private theorem toNat_bit (condition : Bool) :
    (if condition then (1 : W64) else 0).toNat = if condition then 1 else 0 := by
  cases condition <;> rfl
#print axioms toNat_bit

/-- Lane `i` of a wide sum is the lane sum plus the carry out of the lanes below it. -/
theorem lane64_add (x y : BitVec w) (i : Nat) (fits : 64 * i + 64 ≤ w) :
    lane64 (x + y) i = lane64 x i + lane64 y i +
      (if BitVec.carry (64 * i) x y false then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  have positive : 0 < 2 ^ (64 * i) := Nat.two_pow_pos _
  have width : 2 ^ w = 2 ^ (64 * i) * (2 ^ 64 * 2 ^ (w - 64 * i - 64)) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  rw [toNat_lane64, BitVec.toNat_add, width, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right _ _), add_div_scale _ _ _ positive,
    low_sum_div _ _ _ (Nat.mod_lt _ positive) (Nat.mod_lt _ positive)]
  simp only [BitVec.toNat_add, toNat_lane64, toNat_bit, BitVec.carry, Bool.toNat_false,
    Nat.add_zero, ge_iff_le]
  split <;> simp only [decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true,
    *] <;> omega
#print axioms lane64_add

/-- Whether `x - y` borrows out of its low `i` bits, the borrow into bit `i`; the subtraction
    counterpart of `BitVec.carry i x y false`. -/
def subBorrow (i : Nat) (x y : BitVec w) : Bool :=
  decide (x.toNat % 2 ^ i < y.toNat % 2 ^ i)

/-- Comparing two-digit numbers whose low digits are below `scale`: high digits first. -/
private theorem digits_lt_iff {scale xLow yLow xHigh yHigh : Nat} (xSmall : xLow < scale)
    (ySmall : yLow < scale) :
    xLow + scale * xHigh < yLow + scale * yHigh ↔
      xHigh < yHigh ∨ (xHigh = yHigh ∧ xLow < yLow) := by
  rcases Nat.lt_trichotomy xHigh yHigh with below | same | above
  · have := Nat.mul_le_mul_left scale (Nat.succ_le_of_lt below)
    rw [Nat.mul_succ] at this
    omega
  · subst same
    omega
  · have := Nat.mul_le_mul_left scale (Nat.succ_le_of_lt above)
    rw [Nat.mul_succ] at this
    omega
#print axioms digits_lt_iff

/-- The borrow out of digit `i` given the borrow into it. -/
theorem subBorrow_lane_succ (x y : BitVec w) (i : Nat) :
    subBorrow (64 * (i + 1)) x y =
      ((lane64 x i).ult (lane64 y i) ||
        (lane64 x i == lane64 y i && subBorrow (64 * i) x y)) := by
  have positive : 0 < 2 ^ (64 * i) := Nat.two_pow_pos _
  unfold subBorrow
  rw [Nat.mul_succ, mod_two_pow_add_lane x.toNat, mod_two_pow_add_lane y.toNat,
    Bool.eq_iff_iff]
  simp only [decide_eq_true_iff, digits_lt_iff (Nat.mod_lt _ positive) (Nat.mod_lt _ positive),
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, BitVec.ult_eq_decide_lt, BitVec.lt_def,
    ← BitVec.toNat_inj, toNat_lane64]
#print axioms subBorrow_lane_succ

/-- Adding `y` back to `x - y` carries out of the low `a` bits exactly when `x - y` borrows. -/
theorem carry_sub_add (x y : BitVec w) (a : Nat) (fits : a ≤ w) :
    BitVec.carry a (x - y) y false = subBorrow a x y := by
  have positive : 0 < 2 ^ a := Nat.two_pow_pos _
  have restored : x.toNat % 2 ^ a = ((x - y).toNat % 2 ^ a + y.toNat % 2 ^ a) % 2 ^ a := by
    conv => lhs; rw [← BitVec.sub_add_cancel x y]
    rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 fits), Nat.add_mod]
  have difference := Nat.mod_lt (x - y).toNat positive
  have subtrahend := Nat.mod_lt y.toNat positive
  unfold BitVec.carry subBorrow
  rw [restored]
  generalize (x - y).toNat % 2 ^ a = differenceLow at *
  generalize y.toNat % 2 ^ a = subtrahendLow at *
  generalize 2 ^ a = scale at *
  simp only [Bool.toNat_false, Nat.add_zero, ge_iff_le]
  by_cases wraps : scale ≤ differenceLow + subtrahendLow
  · rw [Nat.mod_eq_sub_mod wraps, Nat.mod_eq_of_lt (by omega)]
    simp only [wraps, decide_true]
    exact (decide_eq_true (by omega)).symm
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [wraps, decide_false]
    exact (decide_eq_false (by omega)).symm
#print axioms carry_sub_add

/-- Lane `i` of a wide difference is the lane difference less the borrow out of the lanes below
    it. -/
theorem lane64_sub (x y : BitVec w) (i : Nat) (fits : 64 * i + 64 ≤ w) :
    lane64 (x - y) i = lane64 x i - lane64 y i -
      (if subBorrow (64 * i) x y then 1 else 0) := by
  have sum := lane64_add (x - y) y i fits
  rw [BitVec.sub_add_cancel, carry_sub_add x y _ (by omega)] at sum
  rw [sum, BitVec.sub_sub, BitVec.add_assoc, BitVec.add_sub_cancel]
#print axioms lane64_sub

/-- The carry out of the whole width is the unsigned overflow of `x + y`. -/
theorem carry_width (x y : BitVec w) :
    BitVec.carry w x y false = decide (2 ^ w ≤ x.toNat + y.toNat) := by
  simp [BitVec.carry, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt]
#print axioms carry_width

/-- The borrow out of the whole width is the unsigned comparison `x < y`. -/
theorem subBorrow_width (x y : BitVec w) : subBorrow w x y = x.ult y := by
  simp [subBorrow, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt, BitVec.ult_eq_decide_lt,
    BitVec.lt_def]
#print axioms subBorrow_width

/-- Nothing carries into the lowest lane. -/
theorem carry_lane_zero (x y : BitVec w) : BitVec.carry (64 * 0) x y false = false := by
  simp
#print axioms carry_lane_zero

/-- Nothing borrows into the lowest lane. -/
theorem subBorrow_lane_zero (x y : BitVec w) : subBorrow (64 * 0) x y = false := by
  simp [subBorrow, Nat.mod_one]
#print axioms subBorrow_lane_zero

/-- Without a carry passing through an all-ones lane, the carry out of lane `i` is whether
    lane `i` itself wraps: the single-hop correction is exact. -/
theorem carry_lane_succ_of_isolated (x y : BitVec w) (i : Nat)
    (isolated : (lane64 x i + lane64 y i == BitVec.allOnes 64 &&
      BitVec.carry (64 * i) x y false) = false) :
    BitVec.carry (64 * (i + 1)) x y false = (lane64 x i + lane64 y i).ult (lane64 x i) := by
  rw [carry_lane_succ, isolated, Bool.or_false]
#print axioms carry_lane_succ_of_isolated

/-- Without a borrow passing through an equal lane, the borrow out of lane `i` is whether
    lane `i` itself borrows: the single-hop correction is exact. -/
theorem subBorrow_lane_succ_of_isolated (x y : BitVec w) (i : Nat)
    (isolated : (lane64 x i == lane64 y i && subBorrow (64 * i) x y) = false) :
    subBorrow (64 * (i + 1)) x y = (lane64 x i).ult (lane64 y i) := by
  rw [subBorrow_lane_succ, isolated, Bool.or_false]
#print axioms subBorrow_lane_succ_of_isolated

/-! ### Generate and propagate flags -/

/-- A sum compares below its first operand exactly when it wraps. -/
theorem add_ult_eq_overflow (a b : BitVec w) :
    (a + b).ult a = decide (2 ^ w ≤ a.toNat + b.toNat) := by
  have := a.isLt
  have := b.isLt
  rw [Bool.eq_iff_iff]
  simp only [BitVec.ult_eq_decide_lt, BitVec.lt_def, BitVec.toNat_add, decide_eq_true_iff]
  constructor
  · intro wrapped
    apply Nat.le_of_not_lt
    intro fits
    rw [Nat.mod_eq_of_lt fits] at wrapped
    omega
  · intro wraps
    rw [Nat.mod_eq_sub_mod wraps, Nat.mod_eq_of_lt (by omega)]
    omega
#print axioms add_ult_eq_overflow

/-- A lane that generates a carry cannot also propagate one: its wrapped sum is not all ones. -/
theorem generate_not_propagate (a b : BitVec w) (generated : (a + b).ult a = true) :
    (a + b == BitVec.allOnes w) = false := by
  rw [add_ult_eq_overflow, decide_eq_true_iff] at generated
  have := a.isLt
  have := b.isLt
  simp only [beq_eq_false_iff_ne, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_add,
    BitVec.toNat_allOnes]
  rw [Nat.mod_eq_sub_mod generated, Nat.mod_eq_of_lt (by omega)]
  omega
#print axioms generate_not_propagate

/-- A lane that generates a borrow cannot also propagate one: its operands differ. -/
theorem borrow_not_propagate (a b : BitVec w) (generated : a.ult b = true) :
    (a == b) = false := by
  simp only [BitVec.ult_eq_decide_lt, decide_eq_true_iff] at generated
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro same
  subst same
  exact BitVec.lt_irrefl a generated
#print axioms borrow_not_propagate

/-! ### Comparison masks -/

/-- The sign bit of a comparison mask is the comparison. -/
theorem msb_mask64 (p : Bool) : (mask64 p).msb = p := by
  cases p <;> decide
#print axioms msb_mask64

/-- Subtracting a comparison mask adds the comparison as a 0-or-1 carry. -/
theorem sub_mask64 (x : W64) (p : Bool) : x - mask64 p = x + (if p then 1 else 0) := by
  cases p
  · simp [mask64]
  · change x - BitVec.allOnes 64 = x + 1
    rw [BitVec.sub_eq_add_neg, ← BitVec.neg_one_eq_allOnes, BitVec.neg_neg]
    rfl
#print axioms sub_mask64

/-- Adding a comparison mask subtracts the comparison as a 0-or-1 borrow. -/
theorem add_mask64 (x : W64) (p : Bool) : x + mask64 p = x - (if p then 1 else 0) := by
  cases p
  · simp [mask64]
  · change x + BitVec.allOnes 64 = x - 1
    rw [BitVec.sub_eq_add_neg]
    rfl
#print axioms add_mask64

/-- Conjunction of comparison masks. -/
theorem mask64_and_mask64 (p q : Bool) : mask64 p &&& mask64 q = mask64 (p && q) := by
  cases p <;> cases q <;> decide
#print axioms mask64_and_mask64

/-! ### Carry lookahead on packed flags -/

/-- The carry into position `i` of a ripple in which position `j` generates a carry when bit `j`
    of `generate` is set and passes an incoming carry on when bit `j` of `propagate` is set. -/
def rippleCarry (generate propagate : BitVec w) : Nat → Bool
  | 0 => false
  | i + 1 => generate.getLsbD i || (propagate.getLsbD i && rippleCarry generate propagate i)

/-- In `propagate + (generate <<< 1)`, the shifted generate bit and the adder's own carry never
    meet at bit `i`, and together they are the ripple carry into `i`. -/
private theorem cascade_carry (generate propagate : BitVec w) (i : Nat) (inWord : i < w)
    (disjoint : ∀ j < i, generate.getLsbD j = true → propagate.getLsbD j = false) :
    ((generate <<< 1).getLsbD i && BitVec.carry i propagate (generate <<< 1) false) = false ∧
    ((generate <<< 1).getLsbD i ^^ BitVec.carry i propagate (generate <<< 1) false) =
      rippleCarry generate propagate i := by
  induction i with
  | zero => simp [rippleCarry]
  | succ i previous =>
    obtain ⟨apart, together⟩ := previous (by omega) (fun j below => disjoint j (by omega))
    have shifted : (generate <<< 1).getLsbD (i + 1) = generate.getLsbD i := by
      rw [BitVec.getLsbD_shiftLeft]
      simp [show i + 1 < w from inWord]
    have own := disjoint i (by omega)
    rw [BitVec.carry_succ, shifted]
    simp only [rippleCarry, ← together]
    revert apart own
    generalize generate.getLsbD i = generated
    generalize propagate.getLsbD i = propagated
    generalize (generate <<< 1).getLsbD i = incoming
    generalize BitVec.carry i propagate (generate <<< 1) false = carried
    cases generated <;> cases propagated <;> cases incoming <;> cases carried <;>
      simp [Bool.atLeastTwo]
#print axioms cascade_carry

/-- Carry lookahead by one addition: when no position both generates and propagates, bit `i` of
    `propagate ^^^ (propagate + (generate <<< 1))` is the ripple carry into position `i`. -/
theorem getLsbD_cascade (generate propagate : BitVec w) (i : Nat) (inWord : i < w)
    (disjoint : ∀ j < i, generate.getLsbD j = true → propagate.getLsbD j = false) :
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD i =
      rippleCarry generate propagate i := by
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_add inWord, ← (cascade_carry _ _ i inWord disjoint).2,
    ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
#print axioms getLsbD_cascade

/-- Doubling a packed flag word shifts every flag up one position. -/
theorem two_mul_eq_shiftLeft (x : BitVec w) : (2 : BitVec w) * x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
    BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_mul_mod, Nat.mul_comm]
#print axioms two_mul_eq_shiftLeft

/-- Lane flags from a wide sum drive the ripple to the true lane carries: when bit `j` of
    `generate` says lane `j` wraps and bit `j` of `propagate` says its sum is all ones. -/
theorem rippleCarry_eq_carry (x y : BitVec w) (generate propagate : BitVec flagWidth)
    (laneCount : Nat)
    (generated : ∀ j < laneCount,
      generate.getLsbD j = (lane64 x j + lane64 y j).ult (lane64 x j))
    (propagated : ∀ j < laneCount,
      propagate.getLsbD j = (lane64 x j + lane64 y j == BitVec.allOnes 64))
    (i : Nat) (covered : i ≤ laneCount) :
    rippleCarry generate propagate i = BitVec.carry (64 * i) x y false := by
  induction i with
  | zero => simp [rippleCarry]
  | succ i previous =>
    rw [rippleCarry, carry_lane_succ, generated i (by omega), propagated i (by omega),
      previous (by omega)]
#print axioms rippleCarry_eq_carry

/-- Lane flags from a wide difference drive the ripple to the true lane borrows: when bit `j`
    of `generate` says lane `j` of `x` is below that of `y` and bit `j` of `propagate` says they
    are equal. -/
theorem rippleCarry_eq_subBorrow (x y : BitVec w) (generate propagate : BitVec flagWidth)
    (laneCount : Nat)
    (generated : ∀ j < laneCount,
      generate.getLsbD j = (lane64 x j).ult (lane64 y j))
    (propagated : ∀ j < laneCount,
      propagate.getLsbD j = (lane64 x j == lane64 y j))
    (i : Nat) (covered : i ≤ laneCount) :
    rippleCarry generate propagate i = subBorrow (64 * i) x y := by
  induction i with
  | zero => simp [rippleCarry, subBorrow, Nat.mod_one]
  | succ i previous =>
    rw [rippleCarry, subBorrow_lane_succ, generated i (by omega), propagated i (by omega),
      previous (by omega)]
#print axioms rippleCarry_eq_subBorrow

/-- The packed-flag cascade of an addition yields the carry into each lane. -/
theorem cascade_add_flags (x y : BitVec w) (generate propagate : BitVec flagWidth)
    (laneCount : Nat)
    (generated : ∀ j < laneCount,
      generate.getLsbD j = (lane64 x j + lane64 y j).ult (lane64 x j))
    (propagated : ∀ j < laneCount,
      propagate.getLsbD j = (lane64 x j + lane64 y j == BitVec.allOnes 64))
    (i : Nat) (covered : i ≤ laneCount) (inWord : i < flagWidth) :
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD i =
      BitVec.carry (64 * i) x y false := by
  rw [getLsbD_cascade _ _ i inWord,
    rippleCarry_eq_carry x y _ _ laneCount generated propagated i covered]
  intro j below wraps
  rw [propagated j (by omega)]
  rw [generated j (by omega)] at wraps
  exact generate_not_propagate _ _ wraps
#print axioms cascade_add_flags

/-- The packed-flag cascade of a subtraction yields the borrow into each lane. -/
theorem cascade_sub_flags (x y : BitVec w) (generate propagate : BitVec flagWidth)
    (laneCount : Nat)
    (generated : ∀ j < laneCount,
      generate.getLsbD j = (lane64 x j).ult (lane64 y j))
    (propagated : ∀ j < laneCount,
      propagate.getLsbD j = (lane64 x j == lane64 y j))
    (i : Nat) (covered : i ≤ laneCount) (inWord : i < flagWidth) :
    (propagate ^^^ (propagate + (generate <<< 1))).getLsbD i = subBorrow (64 * i) x y := by
  rw [getLsbD_cascade _ _ i inWord,
    rippleCarry_eq_subBorrow x y _ _ laneCount generated propagated i covered]
  intro j below borrows
  rw [propagated j (by omega)]
  rw [generated j (by omega)] at borrows
  exact borrow_not_propagate _ _ borrows
#print axioms cascade_sub_flags

end CIL.Vector
