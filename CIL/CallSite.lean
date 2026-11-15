import CIL.Identity
import CIL.TypeExpr

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

/-- A method by declaring type, name and declared signature, with the type arguments of a
    generic method instance; types are in the closed form the call site states. -/
structure MethodRef where
  owner : TypeExpr
  name : MetadataName
  hasThis : Bool
  genericArity : Nat
  returnType : TypeExpr
  parameters : List TypeExpr
  methodArguments : List TypeExpr := []
  deriving DecidableEq, Repr

/-- The number of values a call to `method` consumes: its parameters and, for an instance
    method, the receiver. -/
def MethodRef.argumentCount (method : MethodRef) : Nat :=
  method.parameters.length + (if method.hasThis then 1 else 0)

/-- The metadata of a `call` or `newobj` operand, as declared at the call site. -/
structure CallSite where
  method : MethodRef
  name : String := ""
  target : MethodId
  typeArguments : List TypeExpr
  parameterCount : Nat
  returnsValue : Bool
  /-- The suffix of `typeArguments` belonging to the declaring type, not the method. -/
  ownerArgumentCount : Nat := 0
  deriving DecidableEq, Repr

/-- The type that declares the method a site calls. -/
abbrev CallSite.declaringType (site : CallSite) : TypeExpr := site.method.owner

/-- Whether the method a site calls takes a receiver. -/
abbrev CallSite.hasThis (site : CallSite) : Bool := site.method.hasThis

/-- The declared result type of the method a site calls. -/
abbrev CallSite.returnType (site : CallSite) : TypeExpr := site.method.returnType

/-- The declared parameter types of the method a site calls, receiver excluded. -/
abbrev CallSite.parameterTypes (site : CallSite) : List TypeExpr := site.method.parameters

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
