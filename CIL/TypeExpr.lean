import Std

/-!
# Metadata type expressions

A scope-qualified form of ECMA-335 signature types, used by extraction and by typed import
slots to compare signatures as values.
-/

namespace CIL.Extraction

/-- The assembly scope of the .NET 10 reference assembly that defines the primitive types. -/
def runtimeScope : String :=
  { toByteArray := ⟨#[
      83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 44, 32,
      86, 101, 114, 115, 105, 111, 110, 61, 49, 48, 46, 48, 46, 48, 46, 48,
      44, 32, 67, 117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97,
      108, 44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101,
      110, 61, 98, 48, 51, 102, 53, 102, 55, 102, 49, 49, 100, 53, 48, 97,
      51, 97]⟩,
    isValidUTF8 :=
      ("System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
      ).isValidUTF8 }

/-- The byte-backed scope retains the exact original assembly identity. -/
theorem runtimeScope_eq :
    runtimeScope =
      "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" := by rfl
#print axioms runtimeScope_eq

/-- Scoped metadata types shared by extraction and typed import slots. -/
inductive TypeExpr where
  | void
  | atom (scope name : String)
  | aggregate (identity : String) (index : Nat)
  | enum (identity : String) (underlying : TypeExpr)
  | parameter (index : Nat)
  | byref (element : TypeExpr)
  | pointer (element : TypeExpr)
  /-- A zero-based, single-dimensional CLI array signature. -/
  | array (element : TypeExpr)
  /-- A static function pointer using the default managed calling convention. -/
  | functionPointer (result parameters : TypeExpr)
  /-- One parameter in a function-pointer signature; the parameter chain ends in `.void`. -/
  | signatureParameter (head tail : TypeExpr)
  | constructor (scope name : String)
  | apply (constructor argument : TypeExpr)
  deriving DecidableEq, Repr

end CIL.Extraction
