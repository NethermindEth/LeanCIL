import CIL.Extraction.UnsafeReferences
import CIL.Extraction.UnsafeTransfers
import CIL.Extraction.ViewObservations
import CIL.Extraction.BinaryTransfers
import CIL.Extraction.ObjectConstruction
import CIL.Extraction.GuardCalls

/-!
# Unsafe helper calls

Live transfers and offsets bind their storage and memory operations. The model table binds
reference formation, null-reference helpers and SkipInit.
-/

namespace CIL.Extraction

/-- Reference helpers use supported stored values, excluding array and span descriptors. -/
private def admittedReferenceArgument (layouts : List RawLayout) : List TypeExpr → Bool
  | [type] => (typeStorage layouts type).any StorageType.isFieldOrVector
  | _ => false

/-- Element offsets bind signedness and native stride; aggregate sizes use layout evidence. -/
def unsafeElementOffsetMatches (layouts : List RawLayout) (raw : RawInstruction)
    (emitted : Instruction) : Bool :=
  match raw.opcode, raw.operand with
  | 40, .call site =>
    if site.name ∉ ["Add", "Subtract"] ||
        site.declaringType != .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" then true
    else if !unsafeElementOffset raw || !admittedReferenceArgument layouts site.typeArguments then
      false
    else match site.typeArguments, emitted with
      | [type], .memory (.add stride signed) =>
        let expected := fun width => if site.name == "Subtract" then subtractionStride width
          else width
        signed == (site.parameterTypes[1]? != some (.atom runtimeScope "System.UIntPtr")) &&
          match typeStorage layouts type with
          | some (.field (.aggregate _)) => true
          | some (.field kind) => (primitiveFieldWidth kind).any fun width =>
            stride == expected width
          | some .vector128 => stride == expected 16
          | some .vector256 => stride == expected 32
          | some .vector512 => stride == expected 64
          | _ => false
      | _, _ => false
  | _, _ => true

/-- Dedicated memory instructions must originate at an opcode that can still emit them: no raw
    opcode but a call emits a pointer or byte-span transfer, reinterprets a span or takes an
    array's data reference. -/
private def memoryCallOrigin (raw : RawInstruction) : Instruction → Bool
  | .skipInit | .memory .isNullRef => false
  | .memory .nullRef => raw.opcode == 20 && raw.operand == .none
  | .memory (.pointerTransfer ..) | .memory (.marshalRead ..) | .memory (.marshalWrite ..)
  | .memory (.spanReinterpret ..) | .memory (.observeView .arrayData) => raw.opcode == 40
  | _ => true

/-- A recognized call emits exactly its helper operation, which no other instruction may emit. -/
def UnsafeCallsValid (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Instruction) : Prop :=
  closed.code.length = reachable.length ∧ closed.code.length = code.length ∧
  all3 (fun instruction live emitted => !live ||
      memoryCallOrigin instruction emitted &&
      unsafeBlockMatches instruction emitted &&
      vector128UnsafeMatches instruction emitted &&
      viewObservationMatches instruction emitted &&
      binaryTransferMatches instruction emitted &&
      unsafeElementOffsetMatches layouts instruction emitted &&
      callEmitsNoPop instruction emitted &&
      guardCallMatches instruction emitted &&
      if unsafeReferenceRequired instruction emitted then
        match unsafeReferenceHelper instruction, instruction.operand with
        | some helper, .call site =>
          admittedReferenceArgument layouts site.typeArguments && helper.matches emitted
        | _, _ => false
      else true)
    closed.code reachable code = true

instance (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Instruction) :
    Decidable (UnsafeCallsValid layouts closed reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
