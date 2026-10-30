import CIL.Types
import CIL.IntegerArithmetic

/-!
# Scalar intrinsics

Portable integer helpers such as `Math.Min`, `BitOperations.PopCount` and
`BinaryPrimitives.ReverseEndianness`. Their results do not depend on the hardware, so every
profile may evaluate them.
-/

namespace CIL

/-- `Math.Min`, `Max`, `Clamp`, `Abs` and `Sign` on integers. -/
inductive IntegerMath where
  | min | max | clamp | abs | sign
  deriving DecidableEq, Repr

/-- Runtime integer helpers use mathematical comparisons, with explicit exceptional outcomes. -/
def evalIntegerMath (operation : IntegerMath) (width : Nat) (signed : Bool)
    (args : List Value) : Except ArithmeticFault Value := do
  if width != 8 && width != 16 && width != 32 && width != 64 then
    .error .invalidOperands
  else
    let numbers ← args.mapM fun value => match value with
      | .i32 bits => if width ≤ 32 then
          .ok (if signed then (bits.setWidth width).toInt else (bits.setWidth width).toNat)
        else .error .invalidOperands
      | .i64 bits => if width = 64 then .ok (if signed then bits.toInt else bits.toNat)
        else .error .invalidOperands
      | _ => .error .invalidOperands
    let result ← match operation, numbers with
      | .min, [a, b] => .ok (min a b)
      | .max, [a, b] => .ok (max a b)
      | .clamp, [x, lower, upper] =>
        if lower > upper then .error .invalidBounds else .ok (min (max x lower) upper)
      | .abs, [x] => if !signed then .error .invalidOperands else
        if x = -(2 ^ (width - 1) : Int) then .error .overflow else .ok (Int.ofNat x.natAbs)
      | .sign, [x] => if !signed then .error .invalidOperands else
        .ok (if x < 0 then -1 else if x = 0 then 0 else 1)
      | _, _ => .error .invalidOperands
    return if operation == .sign || width ≤ 32 then .i32 (BitVec.ofInt 32 result)
      else .i64 (BitVec.ofInt 64 result)

/-- Integer stack representation of a portable count or logarithm result. -/
inductive ScalarResultWidth where
  | word32 | word64
  deriving DecidableEq, Repr

/-- Encode a nonnegative result in its declared integer stack representation. -/
def ScalarResultWidth.value : ScalarResultWidth → Nat → Value
  | .word32, number => .i32 (BitVec.ofNat 32 number)
  | .word64, number => .i64 (BitVec.ofNat 64 number)

/-- Portable runtime helpers, independent of hardware feature availability. -/
inductive ScalarIntrinsic where
  | math (operation : IntegerMath) (width : Nat) (signed : Bool)
  | rotateLeft (width : Nat) | rotateRight (width : Nat)
  | popCount (width : Nat) (result : ScalarResultWidth)
  | leadingZeroCount (width : Nat) (result : ScalarResultWidth)
  | trailingZeroCount (width : Nat) (result : ScalarResultWidth)
  | reverseEndianness (width : Nat) (signed : Bool)
  | isPow2 (width : Nat) (signed : Bool)
  | log2 (width : Nat) (result : ScalarResultWidth) | roundUpToPowerOf2 (width : Nat)
  /-- `Math.DivRem(T, T)`, returning a `(T Quotient, T Remainder)` tuple. -/
  | divRem (width : Nat) (signed : Bool)
  /-- `Math.BigMul(int, int)` or `Math.BigMul(uint, uint)`: the exact 64-bit product. -/
  | bigMul32 (signed : Bool)
  deriving DecidableEq, Repr

/-- `Math.DivRem(T, T)` as its `ValueTuple<T, T>`: Item1 at offset 0 and Item2 at offset
    `width / 8`. Narrow parameters truncate at the call boundary; `div` faults are reported. -/
def evalDivRem (width : Nat) (signed : Bool) : List Value → Except ArithmeticFault Value
  | [.i32 left, .i32 right] =>
    if width == 8 || width == 16 || width == 32 then
      tuple (divRemBits signed (left.setWidth width) (right.setWidth width))
    else .error .invalidOperands
  | [.i64 left, .i64 right] =>
    if width == 64 then tuple (divRemBits signed left right) else .error .invalidOperands
  | _ => .error .invalidOperands
where
  tuple {w : Nat} (result : Except ArithmeticFault (BitVec w × BitVec w)) :
      Except ArithmeticFault Value := do
    let (quotient, remainder) ← result
    return .aggregate (Safety.numberBytes quotient.toNat (w / 8) ++
      Safety.numberBytes remainder.toNat (w / 8))

/-- The number of set bits. -/
def population (x : BitVec w) : Nat := x.cpopNatRec w 0

/-- Population counts exactly the set bit positions, including the empty bitvector. -/
theorem population_eq_length_filter (x : BitVec w) :
    population x = ((List.range w).filter x.getLsbD).length := by
  have count (width : Nat) :
      x.cpopNatRec width 0 = ((List.range width).filter x.getLsbD).length := by
    induction width with
    | zero => rfl
    | succ width previous =>
      rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq, previous, List.range_succ,
        List.filter_append, List.length_append]
      cases bit : x.getLsbD width <;> simp [bit]
  exact count w

#print axioms population_eq_length_filter

/-- The number of zero bits above the highest set bit; `w` for zero. -/
def leadingZeros (x : BitVec w) : Nat :=
  ((List.range w).takeWhile fun i => !x.getLsbD (w - 1 - i)).length

/-- The number of zero bits below the lowest set bit; `w` for zero. -/
def trailingZeros (x : BitVec w) : Nat :=
  ((List.range w).takeWhile fun i => !x.getLsbD i).length

/-- Whether `x` is a positive power of two; with `signed`, a negative value is not. -/
def isPowerOfTwo (x : BitVec w) (signed : Bool) : Bool :=
  x != 0 && (x &&& (x - 1)) == 0 && (!signed || !x.msb)

/-- Zero and overflow both produce zero after truncation to the operand width. -/
def roundUpPowerOfTwo (x : BitVec w) : BitVec w :=
  BitVec.ofNat w (2 ^ (w - leadingZeros (x - 1)))

/-- Reverse bytes, preserving the bit order within each byte. -/
def reverseBytes (x : BitVec w) : BitVec w :=
  (List.range (w / 8)).foldl (fun result i =>
    (result <<< 8) ||| ((x >>> (8 * i)) &&& 255)) 0

/-- A scalar intrinsic on its stack arguments, first argument first. An unsupported width
    or ill-typed argument is stuck; counts use their declared result representation. -/
def evalScalarIntrinsic : ScalarIntrinsic → List Value → Option Value
  | .math operation width signed, args =>
    (evalIntegerMath operation width signed args).toOption
  | .divRem width signed, args => (evalDivRem width signed args).toOption
  | .bigMul32 signed, [.i32 left, .i32 right] =>
    some (.i64 (BitVec.ofInt 64 (if signed then left.toInt * right.toInt
      else (left.toNat * right.toNat : Nat))))
  | .isPow2 32 signed, [.i32 x] => some (.i32 (if isPowerOfTwo x signed then 1 else 0))
  | .isPow2 64 signed, [.i64 x] => some (.i32 (if isPowerOfTwo x signed then 1 else 0))
  | .log2 32 result, [.i32 x] => some (result.value x.toNat.log2)
  | .log2 64 result, [.i64 x] => some (result.value x.toNat.log2)
  | .roundUpToPowerOf2 32, [.i32 x] => some (.i32 (roundUpPowerOfTwo x))
  | .roundUpToPowerOf2 64, [.i64 x] => some (.i64 (roundUpPowerOfTwo x))
  | .rotateLeft 32, [.i32 x, .i32 n] => some (.i32 (x.rotateLeft n.toNat))
  | .rotateLeft 64, [.i64 x, .i32 n] => some (.i64 (x.rotateLeft n.toNat))
  | .rotateRight 32, [.i32 x, .i32 n] => some (.i32 (x.rotateRight n.toNat))
  | .rotateRight 64, [.i64 x, .i32 n] => some (.i64 (x.rotateRight n.toNat))
  | .popCount 32 result, [.i32 x] => some (result.value (population x))
  | .popCount 64 result, [.i64 x] => some (result.value (population x))
  | .leadingZeroCount 32 result, [.i32 x] => some (result.value (leadingZeros x))
  | .leadingZeroCount 64 result, [.i64 x] => some (result.value (leadingZeros x))
  | .trailingZeroCount 32 result, [.i32 x] => some (result.value (trailingZeros x))
  | .trailingZeroCount 64 result, [.i64 x] => some (result.value (trailingZeros x))
  | .reverseEndianness 8 signed, [.i32 x] =>
    let result := x.setWidth 8
    some (.i32 (if signed then result.signExtend 32 else result.zeroExtend 32))
  | .reverseEndianness 16 signed, [.i32 x] =>
    let result := reverseBytes (x.setWidth 16)
    some (.i32 (if signed then result.signExtend 32 else result.zeroExtend 32))
  | .reverseEndianness 32 _, [.i32 x] => some (.i32 (reverseBytes x))
  | .reverseEndianness 64 _, [.i64 x] => some (.i64 (reverseBytes x))
  -- Narrow helper parameters truncate at the call boundary, even for noncanonical CIL inputs.
  | .isPow2 width signed, [.i32 bits] =>
    if width == 8 || width == 16 then
      some (.i32 (if isPowerOfTwo (bits.setWidth width) signed then 1 else 0)) else none
  | .popCount width result, [.i32 bits] =>
    if width == 8 || width == 16 then
      some (result.value (population (bits.setWidth width))) else none
  | .log2 width result, [.i32 bits] =>
    if width == 8 || width == 16 then
      some (result.value (bits.setWidth width).toNat.log2) else none
  | .leadingZeroCount width result, [.i32 bits] =>
    if width == 8 || width == 16 then
      some (result.value (leadingZeros (bits.setWidth width))) else none
  | .trailingZeroCount width result, [.i32 bits] =>
    if width == 8 || width == 16 then
      some (result.value (trailingZeros (bits.setWidth width))) else none
  | .rotateLeft width, [.i32 bits, .i32 count] =>
    if width == 8 || width == 16 then
      some (.i32 (((bits.setWidth width).rotateLeft count.toNat).zeroExtend 32)) else none
  | .rotateRight width, [.i32 bits, .i32 count] =>
    if width == 8 || width == 16 then
      some (.i32 (((bits.setWidth width).rotateRight count.toNat).zeroExtend 32)) else none
  | _, _ => none

end CIL
