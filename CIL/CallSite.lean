import CIL.TypeExpr
import CIL.Identity

/-!
# Call sites and field references

The decoded metadata of a call-family operand: the target method, its type arguments and the
declared signature at the site. Shared by the extraction evidence that checks call binding and
by the instruction vocabulary. A field operand is named the same way, by its owner, its index in
the owner's model, its declared type and its metadata name.
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

/-- A field operand: its declaring type, its index among the owner's fields as the model counts
    them, the type it holds and its `#Strings` name. The index and type are claims that metadata
    binding checks against the field's row. -/
structure FieldRef where
  owner : TypeExpr
  index : Nat
  type : TypeExpr
  name : MetadataName
  deriving DecidableEq, Repr

end CIL.Extraction
