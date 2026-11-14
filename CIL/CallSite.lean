import CIL.TypeExpr

/-!
# Call sites

The decoded metadata of a call-family operand: the target method, its type arguments and the
declared signature at the site. Shared by the extraction evidence that checks call binding and
by the instruction vocabulary.
-/

namespace CIL.Extraction
/-- A call target: a method of this module by metadata token, or another assembly's
    method by its `scope::signature` identity. -/
inductive MethodId where
  | managed (token : Nat)
  | external (identity : String)
  deriving DecidableEq, Repr

/-- The metadata of a `call` or `newobj` operand, as declared at the call site. -/
structure CallSite where
  declaringType : TypeExpr := .void
  name : String := ""
  target : MethodId
  typeArguments : List TypeExpr
  parameterCount : Nat
  hasThis : Bool
  returnsValue : Bool
  returnType : TypeExpr := .void
  parameterTypes : List TypeExpr := []
  /-- The suffix of `typeArguments` belonging to the declaring type, not the method. -/
  ownerArgumentCount : Nat := 0
  deriving DecidableEq, Repr

/-- The number of values a call at `site` consumes: its parameters and, for an instance
    method, the receiver. -/
def CallSite.argumentCount (site : CallSite) : Nat :=
  site.parameterCount + (if site.hasThis then 1 else 0)

end CIL.Extraction
