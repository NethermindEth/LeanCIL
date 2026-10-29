import CIL.TypeExpr

/-!
# Typed managed method identities

Indirect dispatch carries a closed managed signature and a method-table identity. These
descriptors are not numeric addresses and cannot be manufactured by integer conversion.
-/

namespace CIL

/-- The exact closed signature of a static method using the default managed convention. -/
structure ManagedSignature where
  result : Extraction.TypeExpr
  parameters : List Extraction.TypeExpr
  deriving DecidableEq, Repr

/-- Canonical metadata encoding, retaining every parameter's scoped type. -/
def ManagedSignature.typeExpr (signature : ManagedSignature) : Extraction.TypeExpr :=
  .functionPointer signature.result
    (signature.parameters.foldr Extraction.TypeExpr.signatureParameter .void)

/-- Stable metadata identity, unaffected by relocating a library's program indices. -/
structure ManagedIdentity where
  owner : String
  token : Nat
  arguments : List Extraction.TypeExpr
  deriving DecidableEq, Repr

/-- One authenticated catalog binding from metadata identity to an extracted body. -/
structure ManagedTarget where
  identity : ManagedIdentity
  method : Nat
  deriving DecidableEq, Repr

/-- A managed method identity; `none` represents a null function pointer. -/
structure MethodPointer where
  signature : ManagedSignature
  target : Option ManagedIdentity
  deriving DecidableEq, Repr

/-- Supplied immutable handler entries sharing one closed signature; `none` is a null table. -/
structure MethodTable where
  signature : ManagedSignature
  targets : Option (List ManagedIdentity)
  deriving DecidableEq, Repr

/-- Managed pointer operations preserve metadata provenance instead of encoding addresses. -/
inductive ManagedOp where
  | address (target : ManagedTarget) (signature : ManagedSignature)
  | tableLength
  | tableElement (signature : ManagedSignature)
  | call (signature : ManagedSignature) (catalog : List ManagedTarget) (tail : Bool)
  deriving DecidableEq, Repr

end CIL
