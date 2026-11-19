import CIL.Extraction.UnsafeReferences
import CIL.Extraction.UnsafeTransfers
import CIL.Extraction.ViewObservations
import CIL.Extraction.BinaryTransfers
import CIL.Extraction.ObjectConstruction
import CIL.Extraction.GuardCalls

/-!
# Unsafe helper calls

`Unsafe.NullRef` and `Unsafe.IsNullRef` are translated to dedicated operations instead of calls.
`UnsafeCallsValid` recognizes these calls from raw metadata alone and requires that each live one
emits its operation and that no other instruction emits any of them. `Unsafe.SkipInit` keeps its
call and runs through the runtime model table.
-/

namespace CIL.Extraction

/-- Unsafe helpers that lower to dedicated instructions. -/
inductive UnsafeHelper where
  | nullRef | isNullRef
  deriving DecidableEq, Repr

/-- The external identity of an `Unsafe` method with the given signature. -/
private def unsafeTarget (signature : String) : MethodId :=
  .external (runtimeScope ++ "::" ++ signature)

/-- One admitted non-reference type argument. -/
private def admittedArgument (storage : TypeExpr → Option StorageType) : List TypeExpr → Bool
  | [type] => match storage type with
    | some .reference | none => false
    | some _ => true
  | _ => false

/-- Reference helpers use supported stored values, excluding array and span descriptors. -/
private def admittedReferenceArgument (layouts : List RawLayout) : List TypeExpr → Bool
  | [type] => match typeStorage layouts type with
    | some (.field _) | some .vector128 | some .vector256 | some .vector512 => true
    | _ => false
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

/-- The runtime helper named by the opcode and owner, before resolving its signature or layout. -/
def unsafeHelperFamily (instruction : RawInstruction) : Option UnsafeHelper := do
  if instruction.opcode != 40 then none else pure ()
  let .call site := instruction.operand | none
  if site.declaringType != .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" then none
    else match site.name with
      | "NullRef" => some .nullRef
      | "IsNullRef" => some .isNullRef
      | _ => none

/-- The parameter count, return flag and external member signature of a lowered helper. -/
private def UnsafeHelper.signature : UnsafeHelper → Nat × Bool × String
  | .nullRef => (0, true, "!!0& System.Runtime.CompilerServices.Unsafe::NullRef()")
  | .isNullRef =>
    (1, true, "System.Boolean System.Runtime.CompilerServices.Unsafe::IsNullRef(!!0&)")

/-- A family member resolves exactly when its call shape, target and stored type agree. -/
def UnsafeHelper.resolvesAt (helper : UnsafeHelper) (storage : TypeExpr → Option StorageType)
    (site : CallSite) : Bool :=
  let (count, returnsValue, signature) := helper.signature
  let typed := match site.typeArguments with
    | [element] =>
      let result := match helper with
        | .nullRef => .byref element
        | .isNullRef => .atom runtimeScope "System.Boolean"
      site.returnType == result && site.parameterTypes ==
        (if helper == .nullRef then [] else [.byref element]) &&
        site.method.methodArguments == [element] && site.method.genericArity == 1
    | _ => false
  typed && !site.hasThis && site.parameterCount == count && site.returnsValue == returnsValue &&
    site.target == unsafeTarget signature && admittedArgument storage site.typeArguments

/-- Whether a helper resolves under the method's raw layouts. -/
def UnsafeHelper.resolves (helper : UnsafeHelper) (layouts : List RawLayout)
    (site : CallSite) : Bool :=
  helper.resolvesAt (typeStorage layouts) site

/-- The instruction a resolving runtime helper emits. -/
def UnsafeHelper.instruction : UnsafeHelper → Instruction
  | .nullRef => .memory .nullRef
  | .isNullRef => .memory .isNullRef

/-- The helper an emitted operation implements, if any. -/
def emittedUnsafeHelper : Instruction → Option UnsafeHelper
  | .memory .nullRef => some .nullRef
  | .memory .isNullRef => some .isNullRef
  | _ => none

/-- A member of the helper family decodes to its operation or an opcode-tagged hole. -/
def UnsafeHelper.decode (helper : UnsafeHelper) (layouts : List RawLayout)
    (raw : RawInstruction) : Instruction :=
  match raw.operand with
  | .call site =>
    if helper.resolves layouts site then helper.instruction else .unadmitted raw.opcode
  | _ => .unadmitted raw.opcode

/-- A family member emits its resolved operation or its own hole. Other sites cannot emit
    helper operations. -/
def unsafeHelperMatches (layouts : List RawLayout) (raw : RawInstruction)
    (emitted : Instruction) : Bool :=
  match unsafeHelperFamily raw with
  | none => !(emitted matches .skipInit) && (emittedUnsafeHelper emitted).isNone
  | some helper => match helper.decode layouts raw with
    | .unadmitted opcode => match emitted with
      | .unadmitted actual => actual == opcode
      | _ => false
    | _ => emittedUnsafeHelper emitted == some helper

/-- The site rule checks calls. Other raw opcodes cannot emit a byte-span transfer,
    reinterpret a span or take an array's data reference. -/
private def memoryCallOrigin (raw : RawInstruction) : Instruction → Bool
  | .memory (.marshalRead ..) | .memory (.marshalWrite ..)
  | .memory (.spanReinterpret ..) | .memory (.observeView .arrayData) => raw.opcode == 40
  | _ => true

/-- A recognized call emits exactly its helper operation, which no other instruction may emit. -/
def UnsafeCallsValid (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Instruction) : Prop :=
  closed.code.length = reachable.length ∧ closed.code.length = code.length ∧
  all3 (fun instruction live emitted => !live ||
      memoryCallOrigin instruction emitted &&
      unsafeTransferMatches layouts instruction emitted &&
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
      else if instruction.opcode == 20 && instruction.operand == .none &&
          emittedUnsafeHelper emitted == some .nullRef then true
      else unsafeHelperMatches layouts instruction emitted)
    closed.code reachable code = true

instance (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Instruction) :
    Decidable (UnsafeCallsValid layouts closed reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
