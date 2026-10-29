import CIL.Extraction.UnsafeReferences
import CIL.Extraction.UnsafeTransfers
import CIL.Extraction.MarshalCalls
import CIL.Extraction.ViewObservations

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

/-- Reference helpers use supported stored values, excluding array and span descriptors. -/
private def admittedReferenceArgument (layouts : List RawLayout) : List TypeExpr → Bool
  | [type] => match typeStorage layouts type with
    | some (.field _) | some .vector128 | some .vector256 | some .vector512 => true
    | _ => false
  | _ => false

/-- Element subtraction binds signedness and native stride; aggregate sizes use layout evidence. -/
def unsafeSubtractMatches (layouts : List RawLayout) (raw : RawInstruction) (emitted : Op) : Bool :=
  match raw.opcode, raw.operand with
  | 40, .call site =>
    if site.name != "Subtract" ||
        site.declaringType != .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" then true
    else if !unsafeElementOffset raw || !admittedReferenceArgument layouts site.typeArguments then
      false
    else match site.typeArguments, emitted with
      | [type], .memory (.add stride signed) =>
        signed == (site.parameterTypes[1]? != some (.atom runtimeScope "System.UIntPtr")) &&
          match typeStorage layouts type with
          | some (.field (.aggregate _)) => true
          | some (.field kind) => (primitiveFieldWidth kind).any fun width =>
            stride == subtractionStride width
          | some .vector128 => stride == subtractionStride 16
          | some .vector256 => stride == subtractionStride 32
          | some .vector512 => stride == subtractionStride 64
          | _ => false
      | _, _ => false
  | _, _ => true

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
      unsafeTransferMatches layouts instruction emitted &&
      marshalTransferMatches layouts instruction emitted &&
      viewObservationMatches instruction emitted &&
      unsafeSubtractMatches layouts instruction emitted &&
      if unsafeReferenceRequired instruction emitted then
        match unsafeReferenceHelper instruction, instruction.operand with
        | some helper, .call site =>
          admittedReferenceArgument layouts site.typeArguments && helper.matches emitted
        | _, _ => false
      else if instruction.opcode == 20 && instruction.operand == .none &&
          emittedUnsafeHelper emitted == some .nullRef then true
      else unsafeHelper layouts instruction == emittedUnsafeHelper emitted)
    closed.code reachable code = true

instance (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Op) :
    Decidable (UnsafeCallsValid layouts closed reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
