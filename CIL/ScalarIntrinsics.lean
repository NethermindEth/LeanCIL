import CIL.Types

namespace CIL

/-- Portable runtime helpers, independent of hardware feature availability. -/
inductive ScalarIntrinsic where
  | rotateLeft (width : Nat) | rotateRight (width : Nat)
  | popCount (width : Nat) | leadingZeroCount (width : Nat) | trailingZeroCount (width : Nat)
  | reverseEndianness (width : Nat) (signed : Bool)
  | isPow2 (width : Nat) (signed : Bool)
  | log2 (width : Nat) | roundUpToPowerOf2 (width : Nat)
  deriving DecidableEq, Repr

def population (x : BitVec w) : Nat := ((List.range w).filter x.getLsbD).length

def leadingZeros (x : BitVec w) : Nat :=
  ((List.range w).takeWhile fun i => !x.getLsbD (w - 1 - i)).length

def trailingZeros (x : BitVec w) : Nat :=
  ((List.range w).takeWhile fun i => !x.getLsbD i).length

def isPowerOfTwo (x : BitVec w) (signed : Bool) : Bool :=
  x != 0 && (x &&& (x - 1)) == 0 && (!signed || !x.msb)

/-- Zero and overflow both produce zero after truncation to the operand width. -/
def roundUpPowerOfTwo (x : BitVec w) : BitVec w :=
  BitVec.ofNat w (2 ^ (w - leadingZeros (x - 1)))

/-- Reverse bytes, preserving the bit order within each byte. -/
def reverseBytes (x : BitVec w) : BitVec w :=
  (List.range (w / 8)).foldl (fun result i =>
    (result <<< 8) ||| ((x >>> (8 * i)) &&& 255)) 0

def evalScalarIntrinsic : ScalarIntrinsic → List Value → Option Value
  | .isPow2 32 signed, [.i32 x] => some (.i32 (if isPowerOfTwo x signed then 1 else 0))
  | .isPow2 64 signed, [.i64 x] => some (.i32 (if isPowerOfTwo x signed then 1 else 0))
  | .log2 32, [.i32 x] => some (.i32 (BitVec.ofNat 32 x.toNat.log2))
  | .log2 64, [.i64 x] => some (.i32 (BitVec.ofNat 32 x.toNat.log2))
  | .roundUpToPowerOf2 32, [.i32 x] => some (.i32 (roundUpPowerOfTwo x))
  | .roundUpToPowerOf2 64, [.i64 x] => some (.i64 (roundUpPowerOfTwo x))
  | .rotateLeft 32, [.i32 x, .i32 n] => some (.i32 (x.rotateLeft n.toNat))
  | .rotateLeft 64, [.i64 x, .i32 n] => some (.i64 (x.rotateLeft n.toNat))
  | .rotateRight 32, [.i32 x, .i32 n] => some (.i32 (x.rotateRight n.toNat))
  | .rotateRight 64, [.i64 x, .i32 n] => some (.i64 (x.rotateRight n.toNat))
  | .popCount 32, [.i32 x] => some (.i32 (BitVec.ofNat 32 (population x)))
  | .popCount 64, [.i64 x] => some (.i32 (BitVec.ofNat 32 (population x)))
  | .leadingZeroCount 32, [.i32 x] => some (.i32 (BitVec.ofNat 32 (leadingZeros x)))
  | .leadingZeroCount 64, [.i64 x] => some (.i32 (BitVec.ofNat 32 (leadingZeros x)))
  | .trailingZeroCount 32, [.i32 x] => some (.i32 (BitVec.ofNat 32 (trailingZeros x)))
  | .trailingZeroCount 64, [.i64 x] => some (.i32 (BitVec.ofNat 32 (trailingZeros x)))
  | .reverseEndianness 8 signed, [.i32 x] =>
    let result := x.setWidth 8
    some (.i32 (if signed then result.signExtend 32 else result.zeroExtend 32))
  | .reverseEndianness 16 signed, [.i32 x] =>
    let result := reverseBytes (x.setWidth 16)
    some (.i32 (if signed then result.signExtend 32 else result.zeroExtend 32))
  | .reverseEndianness 32 _, [.i32 x] => some (.i32 (reverseBytes x))
  | .reverseEndianness 64 _, [.i64 x] => some (.i64 (reverseBytes x))
  | _, _ => none

end CIL
