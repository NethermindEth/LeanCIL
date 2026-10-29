import CIL.Extraction.Generics

/-!
# Managed-reference unaligned transfers

Unsafe byte-reference reads and writes lower to existing checked typed operations. Scalar and
vector widths are bound here; aggregate widths are additionally bound by complete layout uses.
-/

namespace CIL.Extraction

/-- The exact load or store representation of an admitted reference-free value type. -/
def typedTransferMatches (layouts : List RawLayout) (type : TypeExpr) (read : Bool)
    (emitted : Op) : Bool :=
  if let some width := integerVectorWidth type then
    match read, width, emitted with
    | true, 16, .memory .load128 | true, 32, .memory .load256
    | true, 64, .memory .load512 | false, 16, .memory .store128
    | false, 32, .memory .store256 | false, 64, .memory .store512 => true
    | _, _, _ => false
  else match typeStorage layouts type with
    | some (.field (.aggregate _)) => match read, emitted with
      | true, .loadAggregate _ | false, .storeAggregate _ => true
      | _, _ => false
    | some (.field kind) => match primitiveFieldWidth kind with
      | none => false
      | some width => match read, emitted with
        | true, .loadScalar actual signed => actual == width &&
          signed == (kind == .signed8 || kind == .signed16)
        | false, .storeScalar actual => actual == width
        | _, _ => false
    | _ => false

/-- Exact static generic Unsafe identity, including both closed parameter and result types. -/
private def unalignedCall (raw : RawInstruction) : Option (TypeExpr × Bool) := do
  if raw.opcode != 40 then none else pure ()
  let .call site := raw.operand | none
  let [type] := site.typeArguments | none
  if site.declaringType != .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" ||
      site.hasThis then none else pure ()
  let byte := TypeExpr.atom runtimeScope "System.Byte"
  if site.name == "ReadUnaligned" && site.parameterCount == 1 && site.returnsValue &&
      site.parameterTypes == [.byref byte] && site.returnType == type &&
      site.target == .external (runtimeScope ++
        "::!!0 System.Runtime.CompilerServices.Unsafe::ReadUnaligned(System.Byte&)") then
    some (type, true)
  else if site.name == "WriteUnaligned" && site.parameterCount == 2 && !site.returnsValue &&
      site.parameterTypes == [.byref byte, type] && site.returnType == .void &&
      site.target == .external (runtimeScope ++
        "::System.Void System.Runtime.CompilerServices.Unsafe::" ++
        "WriteUnaligned(System.Byte&,!!0)") then
    some (type, false)
  else none

/-- Typed memory operations from calls are reserved for an exact admitted unaligned helper. -/
def unsafeTransferMatches (layouts : List RawLayout) (raw : RawInstruction) (emitted : Op) : Bool :=
  match unalignedCall raw with
  | some (type, read) => typedTransferMatches layouts type read emitted
  | none => match raw.opcode, emitted with
    | 40, .loadScalar .. | 40, .storeScalar _ | 40, .loadAggregate _ | 40, .storeAggregate _
    | 40, .memory .load128 | 40, .memory .load256 | 40, .memory .load512
    | 40, .memory .store128 | 40, .memory .store256 | 40, .memory .store512 => false
    | _, _ => true

end CIL.Extraction
