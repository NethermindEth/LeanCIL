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

end CIL
