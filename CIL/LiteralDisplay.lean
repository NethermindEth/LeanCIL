import Lean

/-!
# Literal display

How goals print bit-vector literals. A value of `2 ^ 16` or more prints in hexadecimal, as masks
and constants such as `0x80000000` are written in specs and C#; smaller values, typically counts
and indexes, keep their decimal form. The output elaborates back to the same term.
-/

namespace CIL

open Lean PrettyPrinter Delaborator SubExpr

/-- The smallest bit-vector literal value printed in hexadecimal. -/
def hexLiteralMinimum : Nat := 2 ^ 16

/-- `value` as an uppercase hexadecimal numeral, such as `0x80000000`. -/
def hexLiteral (value : Nat) : String :=
  "0x" ++ String.ofList ((Nat.toDigits 16 value).map Char.toUpper)

/-- The literal `value` of a bit-vector numeral, when it is shown in hexadecimal. -/
private def hexDisplayed? (value : Expr) : DelabM (Option Nat) := do
  if ← getPPOption getPPAll then return none
  return (value.nat?.orElse fun _ => value.rawNatLit?).filter (· ≥ hexLiteralMinimum)

/-- Print `BitVec.ofNat w n` of a wide literal `n` as `0x...#w`. -/
@[delab app.BitVec.ofNat]
def delabHexBitVec : Delab := do
  let literal ← getExpr
  guard (literal.getAppNumArgs == 2)
  let some width := literal.getArg! 0 |>.nat? | failure
  let some value ← hexDisplayed? (literal.getArg! 1) | failure
  `($(Syntax.mkNumLit (hexLiteral value)):num#$(Syntax.mkNumLit (toString width)):num)

/-- Print a wide numeral of a bit-vector type, such as `(0x80000000 : W32)`, in hexadecimal. -/
@[delab app.OfNat.ofNat]
def delabHexBitVecNumeral : Delab := do
  let literal ← getExpr
  guard (literal.getAppNumArgs == 3)
  guard ((← Meta.whnfR (literal.getArg! 0)).isAppOfArity ``BitVec 1)
  let some value ← hexDisplayed? (literal.getArg! 1) | failure
  return Syntax.mkNumLit (hexLiteral value)

end CIL
