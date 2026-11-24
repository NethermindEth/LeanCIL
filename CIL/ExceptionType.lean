import CIL.TypeExpr

/-!
# Modelled exception types

`ExceptionType` is the closed set of .NET exceptions the model raises: those instructions raise
and those the admitted constructors of a folded `throw` build. Each member stands for one type of
namespace `System` in `runtimeAssembly` (`ExceptionType.typeIdentity`, injective), and
`ExceptionType.ownerName` is the same type as the text a `TypeExpr` names it by, tied to its
identity in bytes by `ExceptionType.ownerName_spells`.
-/

namespace CIL

open CIL.Extraction (runtimeAssembly keyBytes)

/-- The .NET exceptions the model raises: those instructions raise and those the admitted
    constructors of a folded `throw` build. -/
inductive ExceptionType where
  /-- `System.Exception`. -/
  | baseException
  /-- `System.SystemException`. -/
  | systemException
  /-- `System.ApplicationException`. -/
  | applicationException
  /-- `System.ArithmeticException`. -/
  | arithmetic
  /-- `System.DivideByZeroException`. -/
  | divideByZero
  /-- `System.OverflowException`. -/
  | overflow
  /-- `System.InvalidOperationException`. -/
  | invalidOperation
  /-- `System.NotSupportedException`. -/
  | notSupported
  /-- `System.NotImplementedException`. -/
  | notImplemented
  /-- `System.ArgumentException`. -/
  | argument
  /-- `System.ArgumentNullException`. -/
  | argumentNull
  /-- `System.ArgumentOutOfRangeException`. -/
  | argumentOutOfRange
  /-- `System.IndexOutOfRangeException`. -/
  | indexOutOfRange
  /-- `System.NullReferenceException`. -/
  | nullReference
  /-- `System.FormatException`. -/
  | format
  /-- `System.InvalidCastException`. -/
  | invalidCast
  /-- `System.ArrayTypeMismatchException`. -/
  | arrayTypeMismatch
  deriving DecidableEq, Repr

namespace ExceptionType

/-- The name column of the member's `TypeDef` row, such as `OverflowException`. -/
def metadataName : ExceptionType → MetadataName
  | .baseException => name!"Exception"
  | .systemException => name!"SystemException"
  | .applicationException => name!"ApplicationException"
  | .arithmetic => name!"ArithmeticException"
  | .divideByZero => name!"DivideByZeroException"
  | .overflow => name!"OverflowException"
  | .invalidOperation => name!"InvalidOperationException"
  | .notSupported => name!"NotSupportedException"
  | .notImplemented => name!"NotImplementedException"
  | .argument => name!"ArgumentException"
  | .argumentNull => name!"ArgumentNullException"
  | .argumentOutOfRange => name!"ArgumentOutOfRangeException"
  | .indexOutOfRange => name!"IndexOutOfRangeException"
  | .nullReference => name!"NullReferenceException"
  | .format => name!"FormatException"
  | .invalidCast => name!"InvalidCastException"
  | .arrayTypeMismatch => name!"ArrayTypeMismatchException"

/-- The .NET type a member stands for: its type of namespace `System` in `runtimeAssembly`. -/
def typeIdentity (raised : ExceptionType) : TypeIdentity :=
  { assembly := runtimeAssembly, typeNamespace := name!"System", name := raised.metadataName }

/-- Every member, in declaration order. -/
def all : List ExceptionType :=
  [.baseException, .systemException, .applicationException, .arithmetic, .divideByZero, .overflow,
    .invalidOperation, .notSupported, .notImplemented, .argument, .argumentNull,
    .argumentOutOfRange, .indexOutOfRange, .nullReference, .format, .invalidCast,
    .arrayTypeMismatch]

/-- `all` lists every member. -/
theorem mem_all (raised : ExceptionType) : raised ∈ all := by
  cases raised <;> simp [all]

#print axioms mem_all

/-- The member that stands for `type`, or `none` for a type the model does not raise. -/
def ofTypeIdentity? (type : TypeIdentity) : Option ExceptionType :=
  all.find? (·.typeIdentity == type)

/-- A member's type identifies the member, so no two members stand for one type. -/
theorem ofTypeIdentity?_typeIdentity (raised : ExceptionType) :
    ofTypeIdentity? raised.typeIdentity = some raised := by
  cases raised <;> decide +kernel

#print axioms ofTypeIdentity?_typeIdentity

/-- Distinct members stand for distinct .NET types. -/
theorem typeIdentity_injective : Function.Injective typeIdentity := by
  intro left right same
  have found := ofTypeIdentity?_typeIdentity left
  rw [same, ofTypeIdentity?_typeIdentity] at found
  exact (Option.some.inj found).symm

#print axioms typeIdentity_injective

/-- The member's type as the full name a `TypeExpr` atom holds, such as
    `System.OverflowException`. -/
def ownerName : ExceptionType → String
  | .baseException => "System.Exception"
  | .systemException => "System.SystemException"
  | .applicationException => "System.ApplicationException"
  | .arithmetic => "System.ArithmeticException"
  | .divideByZero => "System.DivideByZeroException"
  | .overflow => "System.OverflowException"
  | .invalidOperation => "System.InvalidOperationException"
  | .notSupported => "System.NotSupportedException"
  | .notImplemented => "System.NotImplementedException"
  | .argument => "System.ArgumentException"
  | .argumentNull => "System.ArgumentNullException"
  | .argumentOutOfRange => "System.ArgumentOutOfRangeException"
  | .indexOutOfRange => "System.IndexOutOfRangeException"
  | .nullReference => "System.NullReferenceException"
  | .format => "System.FormatException"
  | .invalidCast => "System.InvalidCastException"
  | .arrayTypeMismatch => "System.ArrayTypeMismatchException"

/-- The UTF-8 bytes of `System.`, the namespace of every member and the separator before its
    name. -/
def ownerPrefix : List Nat := [83, 121, 115, 116, 101, 109, 46]

/-- `ownerPrefix` is the bytes of the namespace `System` followed by a `.`. -/
theorem ownerPrefix_spells :
    MetadataName.ofBytes? ownerPrefix.dropLast = some name!"System" ∧
      ownerPrefix.getLast? = some '.'.toNat := by
  decide +kernel

#print axioms ownerPrefix_spells

/-- The owner name encodes the member's non-nested type in the System namespace. -/
theorem ownerName_spells (raised : ExceptionType) :
    ((keyBytes raised.ownerName).map UInt8.toNat).take ownerPrefix.length = ownerPrefix ∧
      MetadataName.ofBytes? (((keyBytes raised.ownerName).map UInt8.toNat).drop
          ownerPrefix.length) = some raised.typeIdentity.name ∧
      raised.typeIdentity.typeNamespace = name!"System" ∧
      raised.typeIdentity.enclosing = [] := by
  cases raised <;> decide +kernel

#print axioms ownerName_spells

/-- Distinct members have distinct owner names. -/
theorem ownerName_injective : Function.Injective ownerName := by
  intro left right same
  apply typeIdentity_injective
  have leftName := (ownerName_spells left).2.1
  have rightName := (ownerName_spells right).2.1
  rw [same, rightName] at leftName
  have names : left.metadataName = right.metadataName := (Option.some.inj leftName).symm
  unfold typeIdentity
  rw [names]

#print axioms ownerName_injective


end ExceptionType

end CIL

namespace CIL.Extraction

/-- The member a constructor's owner spells, the scope compared once; `none` for any other type. -/
def exceptionOwner? : TypeExpr → Option ExceptionType
  | .atom scope name =>
    if scope == runtimeScope then ExceptionType.all.find? (·.ownerName == name) else none
  | _ => none

/-- A constructor owner that names a member is that member's runtime type. -/
theorem exceptionOwner?_eq_some {type : TypeExpr} {raised : ExceptionType}
    (found : exceptionOwner? type = some raised) : type = .atom runtimeScope raised.ownerName := by
  cases type with
  | atom scope name =>
    simp only [exceptionOwner?] at found
    split at found
    next sameScope =>
      have named := List.find?_some found
      simp only [beq_iff_eq] at named sameScope
      rw [sameScope, named]
    next => simp at found
  | _ => simp [exceptionOwner?] at found

#print axioms exceptionOwner?_eq_some

/-- Each member's owner name identifies that member: no member shadows another. -/
theorem exceptionOwner?_ownerName (raised : ExceptionType) :
    exceptionOwner? (.atom runtimeScope raised.ownerName) = some raised := by
  have sameOwner : ∀ other : ExceptionType,
      (other.ownerName == raised.ownerName) = (other == raised) := by
    intro other
    by_cases equal : other = raised
    · subst equal
      simp
    · have names : other.ownerName ≠ raised.ownerName := ExceptionType.ownerName_injective.ne equal
      simp only [beq_eq_false_iff_ne.mpr names, beq_eq_false_iff_ne.mpr equal]
  simp only [exceptionOwner?, beq_self_eq_true, ↓reduceIte, sameOwner]
  cases raised <;> decide

#print axioms exceptionOwner?_ownerName

/-- The exception carried by a heap object, using the platform reference or the defining class. -/
def runtimeException? (identity : TypeExpr) : Option ExceptionType :=
  match identity with
  | .object scope name =>
    if scope == coreLibraryScope then
      ExceptionType.all.find? (fun raised => raised.typeIdentity.levels == name.levels)
    else none
  | other => exceptionOwner? other

/-- A pinned CoreLib class and the platform reference identify the same named exception. -/
theorem runtimeException?_definingClass (raised : ExceptionType) :
    runtimeException? (.object coreLibraryScope raised.ownerName) = some raised := by
  cases raised <;> decide +kernel

#print axioms runtimeException?_definingClass

end CIL.Extraction
