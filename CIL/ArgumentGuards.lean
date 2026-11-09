import CIL.Types

/-!
# Argument guards

The integer tests of `System.ArgumentOutOfRangeException`'s `ThrowIfZero`, `ThrowIfNegative`,
`ThrowIfNegativeOrZero`, `ThrowIfEqual`, `ThrowIfNotEqual`, `ThrowIfGreaterThan`,
`ThrowIfGreaterThanOrEqual`, `ThrowIfLessThan` and `ThrowIfLessThanOrEqual`. On a primitive
integer each .NET 10 body (`T.IsZero`, `T.IsNegative`, `EqualityComparer<T>.Default.Equals` or
`CompareTo`) is the mathematical comparison of the values its type denotes, which is what
`ZeroGuard.throws` and `ComparisonGuard.throws` state. The checked interpreter raises the
exception for them.
-/

namespace CIL

/-- A guard of `System.ArgumentOutOfRangeException` that tests one value against zero. -/
inductive ZeroGuard where
  | zero | negative | negativeOrZero
  deriving DecidableEq, Repr

/-- Whether the guard throws for `value`. An unsigned value is never negative. -/
def ZeroGuard.throws : ZeroGuard → Int → Bool
  | .zero, value => decide (value = 0)
  | .negative, value => value < 0
  | .negativeOrZero, value => value ≤ 0

/-- A guard of `System.ArgumentOutOfRangeException` that compares a value with a bound. -/
inductive ComparisonGuard where
  | equal | notEqual | greaterThan | greaterThanOrEqual | lessThan | lessThanOrEqual
  deriving DecidableEq, Repr

/-- Whether the guard throws for `value` compared with `other`. -/
def ComparisonGuard.throws : ComparisonGuard → Int → Int → Bool
  | .equal, value, other => decide (value = other)
  | .notEqual, value, other => !decide (value = other)
  | .greaterThan, value, other => value > other
  | .greaterThanOrEqual, value, other => value ≥ other
  | .lessThan, value, other => value < other
  | .lessThanOrEqual, value, other => value ≤ other

/-- The integer a guard parameter of `width` bits holds. A narrow parameter takes the low bits
    of its `int32` stack value, as the call boundary truncates; other values are ill-typed. -/
def guardOperand (width : Nat) (signed : Bool) : Value → Option Int
  | .i32 bits =>
    if width == 8 || width == 16 || width == 32 then
      some (if signed then (bits.setWidth width).toInt else (bits.setWidth width).toNat)
    else none
  | .i64 bits => if width == 64 then some (if signed then bits.toInt else bits.toNat) else none
  | _ => none

end CIL
