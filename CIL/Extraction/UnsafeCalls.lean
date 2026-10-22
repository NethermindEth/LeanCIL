import CIL.Extraction.Generics

namespace CIL.Extraction

private def runtimeScope : String :=
  "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"

/-- Unsafe helpers that translate to one dedicated emitted operation each. -/
inductive UnsafeHelper where
  | skipInit | nullRef | isNullRef
  deriving DecidableEq, Repr

private def unsafeTarget (signature : String) : MethodId :=
  .external (runtimeScope ++ "::" ++ signature)

/-- Recognize the external helper from raw metadata, independently of translation. -/
def unsafeHelper (layouts : List RawLayout) (instruction : RawInstruction) : Option UnsafeHelper :=
  match instruction.opcode, instruction.operand with
  | 0x28, .call site =>
    if site.declaringType == .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" && !site.hasThis &&
        match site.typeArguments with
        | [type] => match typeStorage layouts type with
          | some .reference | none => false
          | some _ => true
        | _ => false then
      match site.name, site.parameterCount, site.returnsValue with
      | "SkipInit", 1, false =>
        if site.target == unsafeTarget "System.Void System.Runtime.CompilerServices.Unsafe::SkipInit(!!0&)"
        then some .skipInit else none
      | "NullRef", 0, true =>
        if site.target == unsafeTarget "!!0& System.Runtime.CompilerServices.Unsafe::NullRef()"
        then some .nullRef else none
      | "IsNullRef", 1, true =>
        if site.target == unsafeTarget "System.Boolean System.Runtime.CompilerServices.Unsafe::IsNullRef(!!0&)"
        then some .isNullRef else none
      | _, _, _ => none
    else none
  | _, _ => none

def emittedUnsafeHelper : Op → Option UnsafeHelper
  | .skipInit => some .skipInit
  | .memory .nullRef => some .nullRef
  | .memory .isNullRef => some .isNullRef
  | _ => none

/-- A recognized call emits exactly its helper operation, which no other instruction may emit. -/
def UnsafeCallsValid (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Op) : Prop :=
  closed.code.length = reachable.length ∧ closed.code.length = code.length ∧
  ∀ pc : Fin closed.code.length, reachable[pc.val]? = some true →
    unsafeHelper layouts closed.code[pc] = code[pc.val]?.bind emittedUnsafeHelper

instance (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Op) : Decidable (UnsafeCallsValid layouts closed reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
