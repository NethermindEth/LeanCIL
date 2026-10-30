import CIL.Types

/-!
# Integer arithmetic

The faulting integer instructions: overflow-checked `add.ovf`, `sub.ovf` and `mul.ovf`,
checked conversions, and division and remainder. Each computes on mathematical integers
and returns an `ArithmeticFault` instead of a wrapped result.
-/

namespace CIL

/-- Arithmetic failures terminate execution; exception handlers are not modelled. -/
inductive ArithmeticFault where
  | invalidOperands | divideByZero | overflow | invalidBounds
  deriving DecidableEq, Repr

/-- The operation of an overflow-checked binary instruction. -/
inductive CheckedBinaryKind where
  | add | sub | mul
  deriving DecidableEq, Repr

/-- `x` and `y` combined on integers, read as signed or unsigned; `overflow` unless the
    result fits in `width` bits under the same reading. -/
def checkedBits (kind : CheckedBinaryKind) (signed : Bool) (x y : BitVec width) :
    Except ArithmeticFault (BitVec width) :=
  let a : Int := if signed then x.toInt else x.toNat
  let b : Int := if signed then y.toInt else y.toNat
  let result := match kind with | .add => a + b | .sub => a - b | .mul => a * b
  let bound : Int := if signed then 2 ^ (width - 1) else 2 ^ width
  let lower := if signed then -bound else 0
  if lower ≤ result ∧ result < bound then .ok (BitVec.ofInt width result)
  else .error .overflow

/-- An overflow-checked binary instruction on two `i32` or two `i64` stack values. -/
def checkedValues (kind : CheckedBinaryKind) (signed : Bool) (x y : Value) :
    Except ArithmeticFault Value :=
  match x, y with
  | .i32 x, .i32 y => (checkedBits kind signed x y).map Value.i32
  | .i64 x, .i64 y => (checkedBits kind signed x y).map Value.i64
  | _, _ => .error .invalidOperands

/-- Checked integer conversion preserves the mathematical input value. Narrow
    destinations are returned in a 32-bit evaluation-stack slot. -/
def convertNumber (width : Nat) (signed : Bool) (number : Int) : Except ArithmeticFault Value :=
  let bound : Int := if signed then 2 ^ (width - 1) else 2 ^ width
  let lower := if signed then -bound else 0
  if lower ≤ number ∧ number < bound then
    .ok (if width ≤ 32 then .i32 (BitVec.ofInt 32 number) else .i64 (BitVec.ofInt 64 number))
  else .error .overflow

/-- A checked conversion to a `width`-bit integer; `unsignedInput` reads the operand as
    unsigned (`conv.ovf.*.un`). Widths other than 8, 16, 32 and 64 are invalid. -/
def convertInteger (width : Nat) (signed unsignedInput : Bool) (value : Value) :
    Except ArithmeticFault Value :=
  if width != 8 && width != 16 && width != 32 && width != 64 then .error .invalidOperands else
  match value with
  | .i32 bits => convertNumber width signed (if unsignedInput then bits.toNat else bits.toInt)
  | .i64 bits => convertNumber width signed (if unsignedInput then bits.toNat else bits.toInt)
  | _ => .error .invalidOperands

/-- Integer division truncates toward zero. The signed minimum / -1 pair is
    rejected for quotient and remainder, matching the admitted .NET runtime. -/
def divideBits (signed remainder : Bool) (x y : BitVec width) :
    Except ArithmeticFault (BitVec width) := do
  if y = 0 then .error .divideByZero else
  if signed then
    if x.toInt = -(2 ^ (width - 1) : Int) && y.toInt = -1 then .error .overflow else
      return BitVec.ofInt width
        (if remainder then x.toInt.tmod y.toInt else x.toInt.tdiv y.toInt)
  else
    return BitVec.ofNat width (if remainder then x.toNat % y.toNat else x.toNat / y.toNat)

/-- `div`, `div.un`, `rem` or `rem.un` on two `i32` or two `i64` stack values. -/
def divideValues (signed remainder : Bool) (x y : Value) : Except ArithmeticFault Value :=
  match x, y with
  | .i32 x, .i32 y => (divideBits signed remainder x y).map Value.i32
  | .i64 x, .i64 y => (divideBits signed remainder x y).map Value.i64
  | _, _ => .error .invalidOperands

/-- `Math.DivRem` on `width`-bit operands, mirroring the runtime source: the quotient is the
    `div` of the operands, which C# widens to `int` below 32 bits and truncates back, and the
    remainder is `left - quotient * right` with wrapping. Faults are exactly those of `div`. -/
def divRemBits (signed : Bool) (left right : BitVec width) :
    Except ArithmeticFault (BitVec width × BitVec width) := do
  let quotient ← if width < 32 then
      let widen (x : BitVec width) : BitVec 32 :=
        if signed then x.signExtend 32 else x.zeroExtend 32
      (divideBits true false (widen left) (widen right)).map (·.setWidth width)
    else divideBits signed false left right
  return (quotient, left - quotient * right)

/-- A zero divisor faults with `divideByZero` at every width and signedness. -/
theorem divRemBits_zero (signed : Bool) (left : BitVec width) :
    divRemBits signed left 0 = .error .divideByZero := by
  have extended : BitVec.signExtend 32 (0#width) = 0#32 := by
    apply BitVec.eq_of_toInt_eq
    simp [BitVec.toInt_signExtend]
  unfold divRemBits divideBits
  cases signed <;> split <;> simp [extended, Except.map, Bind.bind, Except.bind]
#print axioms divRemBits_zero

/-- Unsigned 32- and 64-bit DivRem returns the exact `Nat` quotient and remainder. -/
theorem divRemBits_unsigned {left right : BitVec width} (wide : 32 ≤ width)
    (nonzero : right ≠ 0) :
    divRemBits false left right =
      .ok (BitVec.ofNat width (left.toNat / right.toNat),
        BitVec.ofNat width (left.toNat % right.toNat)) := by
  have narrow : ¬ width < 32 := by omega
  simp only [divRemBits, divideBits, narrow, nonzero, ite_false, Bool.false_eq_true,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  congr 2
  apply BitVec.eq_of_toNat_eq
  have positive : 0 < right.toNat := by
    have : right.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  have bound := left.isLt
  have quotientLe : left.toNat / right.toNat ≤ left.toNat := Nat.div_le_self _ _
  have productLe : left.toNat / right.toNat * right.toNat ≤ left.toNat := Nat.div_mul_le_self _ _
  have split := Nat.div_add_mod left.toNat right.toNat
  rw [BitVec.toNat_sub_of_le, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : left.toNat / right.toNat < 2 ^ width),
    Nat.mod_eq_of_lt (by omega : left.toNat / right.toNat * right.toNat < 2 ^ width),
    Nat.mod_eq_of_lt (by have := Nat.mod_lt left.toNat positive; have := right.isLt; omega)]
  · rw [Nat.mul_comm] at split; omega
  · rw [BitVec.le_def, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : left.toNat / right.toNat < 2 ^ width),
      Nat.mod_eq_of_lt (by omega : left.toNat / right.toNat * right.toNat < 2 ^ width)]
    exact productLe
#print axioms divRemBits_unsigned

/-- All-ones reads as `-1` at every positive width. -/
theorem toInt_negOne (positive : 0 < width) : (-1 : BitVec width).toInt = -1 := by
  rw [show (-1 : BitVec width) = BitVec.allOnes width from BitVec.neg_one_eq_allOnes,
    BitVec.toInt_allOnes]
  simp [positive]
#print axioms toInt_negOne

/-- Signed 32- and 64-bit DivRem, except `MinValue / -1`, returns `sdiv` and `srem`, whose
    signed readings are the exact truncated quotient and remainder. -/
theorem divRemBits_signed {left right : BitVec width} (wide : 32 ≤ width)
    (nonzero : right ≠ 0)
    (representable : left ≠ BitVec.intMin width ∨ right ≠ -1) :
    divRemBits true left right = .ok (left.sdiv right, left.srem right) ∧
      (left.sdiv right).toInt = left.toInt.tdiv right.toInt ∧
      (left.srem right).toInt = left.toInt.tmod right.toInt := by
  have quotient := BitVec.toInt_sdiv_of_ne_or_ne left right representable
  refine ⟨?_, quotient, BitVec.toInt_srem left right⟩
  have positive : 0 < width := by omega
  have narrow : ¬ width < 32 := by omega
  have notOverflow : ¬ (left.toInt = -(2 ^ (width - 1) : Int) ∧ right.toInt = -1) := by
    rintro ⟨minimum, negative⟩
    rcases representable with different | different
    · exact different (BitVec.eq_of_toInt_eq (by
        rw [minimum, BitVec.toInt_intMin_of_pos positive]))
    · exact different (BitVec.eq_of_toInt_eq (by rw [negative, toInt_negOne positive]))
  have remainder : left - left.sdiv right * right = left.srem right := by
    rw [← BitVec.ofInt_toInt (x := left.srem right), BitVec.toInt_srem, Int.tmod_def,
      Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_mul,
      BitVec.ofInt_toInt, BitVec.ofInt_toInt, ← quotient, BitVec.ofInt_toInt,
      BitVec.mul_comm, ← BitVec.sub_eq_add_neg]
  simp only [divRemBits, divideBits, narrow, nonzero, notOverflow, ite_false, ite_true,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Bool.and_eq_true, decide_eq_true_eq,
    Bool.false_eq_true]
  rw [← quotient, BitVec.ofInt_toInt, remainder]
#print axioms divRemBits_signed

/-- Signed 32- and 64-bit `MinValue / -1` faults with `overflow`, as CIL `div` does. -/
theorem divRemBits_overflow (wide : 32 ≤ width) :
    divRemBits true (BitVec.intMin width) (-1) = .error .overflow := by
  have positive : 0 < width := by omega
  have narrow : ¬ width < 32 := by omega
  have nonzero : (-1 : BitVec width) ≠ 0 := by
    intro zero
    have := congrArg BitVec.toInt zero
    rw [toInt_negOne positive] at this
    simp at this
  simp only [divRemBits, divideBits, narrow, nonzero, toInt_negOne positive,
    BitVec.toInt_intMin_of_pos positive, ite_false, ite_true, decide_true, Bool.and_self,
    Bool.false_eq_true, Bind.bind, Except.bind]
#print axioms divRemBits_overflow

/-- Truncating a 32-bit two's complement encoding equals encoding at the narrower width. -/
theorem setWidth_ofInt32 {width : Nat} (narrow : width ≤ 32) (number : Int) :
    (BitVec.ofInt 32 number).setWidth width = BitVec.ofInt width number := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have divides : ((2 ^ width : Nat) : Int) ∣ ((2 ^ 32 : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 narrow)
  have nonnegative : 0 ≤ number % ((2 ^ 32 : Nat) : Int) :=
    Int.emod_nonneg _ (by decide)
  have positive : (0 : Int) < ((2 ^ width : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.two_pow_pos width)
  apply Int.natCast_inj.mp
  rw [Int.natCast_emod, Int.toNat_of_nonneg nonnegative,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt positive)), Int.emod_emod_of_dvd _ divides]
#print axioms setWidth_ofInt32

/-- Below 32 bits the runtime divides in `int`: the fields are the exact truncating quotient
    and remainder wrapped to the field width, so `MinValue / -1` wraps and only zero faults. -/
theorem divRemBits_narrow_signed {left right : BitVec width} (narrow : width < 32)
    (nonzero : right ≠ 0) :
    divRemBits true left right = .ok (BitVec.ofInt width (left.toInt.tdiv right.toInt),
      BitVec.ofInt width (left.toInt.tmod right.toInt)) := by
  have leftWide := BitVec.toInt_signExtend_of_le (x := left) (v := 32) (by omega)
  have rightWide := BitVec.toInt_signExtend_of_le (x := right) (v := 32) (by omega)
  have power : (2 : Int) ^ width ≤ 2 ^ 31 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_lt_succ narrow)
    exact_mod_cast this
  have notMinimum : left.toInt ≠ -2 ^ (32 - 1) := by
    have := BitVec.le_two_mul_toInt (x := left)
    show left.toInt ≠ -2147483648
    omega
  have widenedNonzero : right.signExtend 32 ≠ 0 := by
    intro zero
    have := congrArg BitVec.toInt zero
    rw [rightWide] at this
    exact nonzero (BitVec.eq_of_toInt_eq (by simpa using this))
  have remainder : left - BitVec.ofInt width (left.toInt.tdiv right.toInt) * right =
      BitVec.ofInt width (left.toInt.tmod right.toInt) := by
    rw [Int.tmod_def, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_mul,
      BitVec.ofInt_toInt, BitVec.ofInt_toInt, BitVec.mul_comm, ← BitVec.sub_eq_add_neg]
  simp only [divRemBits, divideBits, narrow, widenedNonzero, leftWide, rightWide, notMinimum,
    ite_true, ite_false, decide_false, Bool.false_and, Bool.false_eq_true,
    Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure,
    setWidth_ofInt32 (width := width) (by omega)]
  rw [remainder]
#print axioms divRemBits_narrow_signed

/-- The low `count` bytes of `number`, least significant first: one stored tuple field. -/
def littleEndianBytes (count number : Nat) : List (BitVec 8) :=
  (List.range count).map fun i => BitVec.ofNat 8 (number / 256 ^ i)

end CIL
