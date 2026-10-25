import CIL.Extraction.Generics

/-!
# Unsafe helper calls

`Unsafe.SkipInit`, `Unsafe.NullRef` and `Unsafe.IsNullRef` are translated to dedicated
operations instead of calls. `UnsafeCallsValid` recognizes these calls from raw metadata
alone and requires that each live one emits its operation and that no other instruction
emits any of them.
-/

namespace CIL.Extraction

/-- Unsafe helpers that translate to one dedicated emitted operation each. -/
inductive UnsafeHelper where
  | skipInit | nullRef | isNullRef
  deriving DecidableEq, Repr

/-- The external identity of an `Unsafe` method with the given signature. -/
private def unsafeTarget (signature : String) : MethodId :=
  .external (runtimeScope ++ "::" ++ signature)

/-- One admitted non-reference type argument. -/
private def admittedArgument (layouts : List RawLayout) : List TypeExpr → Bool
  | [type] => match typeStorage layouts type with
    | some .reference | none => false
    | some _ => true
  | _ => false

/-- `helper` when the call has its exact target and an admitted type argument. -/
private def bound (layouts : List RawLayout) (site : CallSite) (signature : String)
    (helper : UnsafeHelper) : Option UnsafeHelper :=
  if site.target == unsafeTarget signature && admittedArgument layouts site.typeArguments then
    some helper
  else none

/-- Recognize the external helper from raw metadata, independently of translation. -/
def unsafeHelper (layouts : List RawLayout) (instruction : RawInstruction) : Option UnsafeHelper :=
  match instruction.opcode, instruction.operand with
  | 0x28, .call site =>
    if !(site.declaringType == .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" &&
        !site.hasThis) then none
    else if site.name == "SkipInit" && site.parameterCount == 1 && !site.returnsValue then
      bound layouts site "System.Void System.Runtime.CompilerServices.Unsafe::SkipInit(!!0&)"
        .skipInit
    else if site.name == "NullRef" && site.parameterCount == 0 && site.returnsValue then
      bound layouts site "!!0& System.Runtime.CompilerServices.Unsafe::NullRef()" .nullRef
    else if site.name == "IsNullRef" && site.parameterCount == 1 && site.returnsValue then
      bound layouts site
        "System.Boolean System.Runtime.CompilerServices.Unsafe::IsNullRef(!!0&)" .isNullRef
    else none
  | _, _ => none

/-- The helper an emitted operation implements, if any. -/
def emittedUnsafeHelper : Op → Option UnsafeHelper
  | .skipInit => some .skipInit
  | .memory .nullRef => some .nullRef
  | .memory .isNullRef => some .isNullRef
  | _ => none

/-- A recognized call emits exactly its helper operation, which no other instruction may emit. -/
def UnsafeCallsValid (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Op) : Prop :=
  closed.code.length = reachable.length ∧ closed.code.length = code.length ∧
  all3 (fun instruction live emitted => !live ||
      if instruction.opcode == 20 && instruction.operand == .none &&
          emittedUnsafeHelper emitted == some .nullRef then true
      else unsafeHelper layouts instruction == emittedUnsafeHelper emitted)
    closed.code reachable code = true

instance (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Op) :
    Decidable (UnsafeCallsValid layouts closed reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
