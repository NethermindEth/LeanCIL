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

/-- The uppercase hexadecimal digits of `value`, such as `80000000`. -/
def upperHexDigits (value : Nat) : String :=
  String.ofList ((Nat.toDigits 16 value).map Char.toUpper)

/-- `value` as an uppercase hexadecimal numeral, such as `0x80000000`. -/
def hexLiteral (value : Nat) : String :=
  "0x" ++ upperHexDigits value

/-- The value of a natural number literal, written as a numeral or as a raw literal. -/
def natLiteral? (term : Expr) : Option Nat :=
  term.nat? <|> term.rawNatLit?

/-- The literal `value` of a bit-vector numeral, when it is shown in hexadecimal. -/
private def hexDisplayed? (value : Expr) : DelabM (Option Nat) := do
  if ← getPPOption getPPAll then return none
  return (natLiteral? value).filter (· ≥ hexLiteralMinimum)

/-- Print `BitVec.ofNat w n` of a wide literal `n` as `0x...#w`. -/
@[delab app.BitVec.ofNat]
def delabHexBitVec : Delab := do
  let literal ← getExpr
  let #[widthTerm, valueTerm] := literal.getAppArgs | failure
  let some width := widthTerm.nat? | failure
  let some value ← hexDisplayed? valueTerm | failure
  `($(Syntax.mkNumLit (hexLiteral value)):num#$(Syntax.mkNumLit (toString width)):num)

/-- Print a wide numeral of a bit-vector type, such as `(0x80000000 : W32)`, in hexadecimal. -/
@[delab app.OfNat.ofNat]
def delabHexBitVecNumeral : Delab := do
  let literal ← getExpr
  let #[type, valueTerm, _] := literal.getAppArgs | failure
  guard ((← Meta.whnfR type).isAppOfArity ``BitVec 1)
  let some value ← hexDisplayed? valueTerm | failure
  return Syntax.mkNumLit (hexLiteral value)

end CIL
