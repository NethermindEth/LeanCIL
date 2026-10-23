import Std

namespace CIL.Extraction

/-- Scoped metadata types shared by extraction and typed import slots. -/
inductive TypeExpr where
  | void
  | atom (scope name : String)
  | aggregate (identity : String) (index : Nat)
  | enum (identity : String) (underlying : TypeExpr)
  | parameter (index : Nat)
  | byref (element : TypeExpr)
  | pointer (element : TypeExpr)
  | constructor (scope name : String)
  | apply (constructor argument : TypeExpr)
  deriving DecidableEq, Repr

end CIL.Extraction
