import CIL.Types

namespace CIL

/-- Arithmetic failures terminate execution; exception handlers are not modelled. -/
inductive ArithmeticFault where
  | invalidOperands | divideByZero | overflow
  deriving DecidableEq, Repr

/-- Integer division truncates toward zero. The signed minimum / -1 pair is
    rejected for quotient and remainder, matching the admitted .NET runtime. -/
def divideBits (signed remainder : Bool) (x y : BitVec width) :
    Except ArithmeticFault (BitVec width) := do
  if y = 0 then .error .divideByZero else
  if signed then
    if x.toInt = -(2 ^ (width - 1) : Int) && y.toInt = -1 then .error .overflow else
      return BitVec.ofInt width (if remainder then x.toInt.tmod y.toInt else x.toInt.tdiv y.toInt)
  else
    return BitVec.ofNat width (if remainder then x.toNat % y.toNat else x.toNat / y.toNat)

def divideValues (signed remainder : Bool) (x y : Value) : Except ArithmeticFault Value :=
  match x, y with
  | .i32 x, .i32 y => (divideBits signed remainder x y).map Value.i32
  | .i64 x, .i64 y => (divideBits signed remainder x y).map Value.i64
  | _, _ => .error .invalidOperands

end CIL
