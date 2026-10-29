import CIL.Extraction.Generics

/-!
# Checked Unsafe transfers

Unsafe reads and writes reuse checked typed transfers. Scalar and vector widths and alignment
are bound here; aggregate width and alignment are additionally bound by complete layout uses.
-/

namespace CIL.Extraction

/-- Exact byte-reference and pointer block helpers share the existing checked block operations. -/
def unsafeBlockCall (raw : RawInstruction) : Option (Bool × Nat) := do
  if raw.opcode != 40 then none else pure ()
  let .call site := raw.operand | none
  if site.declaringType != .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" ||
      site.hasThis || site.returnsValue || site.returnType != .void ||
      !site.typeArguments.isEmpty || site.parameterCount != 3 then none else pure ()
  let (copy, alignment) ← match site.name with
    | "CopyBlock" => some (true, 8) | "CopyBlockUnaligned" => some (true, 1)
    | "InitBlock" => some (false, 8) | "InitBlockUnaligned" => some (false, 1)
    | _ => none
  let byte := TypeExpr.atom runtimeScope "System.Byte"
  let pointer := site.parameterTypes.head? == some (.pointer .void)
  let address := if pointer then .pointer .void else .byref byte
  if site.parameterTypes != [address, if copy then address else byte,
      .atom runtimeScope "System.UInt32"] then none else pure ()
  let addressName := if pointer then "System.Void*" else "System.Byte&"
  if site.target != .external (runtimeScope ++
      "::System.Void System.Runtime.CompilerServices.Unsafe::" ++ site.name ++ "(" ++
      addressName ++ "," ++ (if copy then addressName else "System.Byte") ++
      ",System.UInt32)") then none else some (copy, alignment)

/-- Block helper calls bind operation, alignment and signature independently of the extractor. -/
def unsafeBlockMatches (raw : RawInstruction) (emitted : Op) : Bool :=
  match unsafeBlockCall raw with
  | some (copy, alignment) => match copy, emitted with
    | true, .memory (.copyBlock actual) | false, .memory (.initBlock actual) => actual == alignment
    | _, _ => false
  | none => match raw.opcode, emitted with
    | 40, .memory (.copyBlock _) | 40, .memory (.initBlock _) => false
    | _, _ => true

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

/-- The transfer representation agrees with the validated value type. -/
def transferKindMatches (layouts : List RawLayout) (type : TypeExpr)
    (kind : TransferKind) : Bool :=
  match kind with
  | .scalar width signed => typedTransferMatches layouts type true (.loadScalar width signed)
  | .snapshot (.aggregate width) => typedTransferMatches layouts type true (.loadAggregate width)
  | .snapshot .vector128 => typedTransferMatches layouts type true (.memory .load128)
  | .snapshot .vector256 => typedTransferMatches layouts type true (.memory .load256)
  | .snapshot .vector512 => typedTransferMatches layouts type true (.memory .load512)

/-- Exact static generic Unsafe identity, including both closed parameter and result types. -/
def unsafeValueCall (raw : RawInstruction) : Option (TypeExpr × Bool × Bool) := do
  if raw.opcode != 40 then none else pure ()
  let .call site := raw.operand | none
  let [type] := site.typeArguments | none
  if site.declaringType != .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" ||
      site.hasThis then none else pure ()
  let byte := TypeExpr.atom runtimeScope "System.Byte"
  let pointer := site.parameterTypes.head? == some (.pointer .void)
  let aligned := site.name == "Read" || site.name == "Write"
  if aligned && !pointer then none else pure ()
  let address := if pointer then .pointer .void else .byref byte
  let addressName := if pointer then "System.Void*" else "System.Byte&"
  if (site.name == "ReadUnaligned" || site.name == "Read") &&
      site.parameterCount == 1 && site.returnsValue &&
      site.parameterTypes == [address] && site.returnType == type &&
      site.target == .external (runtimeScope ++
        "::!!0 System.Runtime.CompilerServices.Unsafe::" ++
        site.name ++ "(" ++ addressName ++ ")") then
    some (type, true, aligned)
  else if (site.name == "WriteUnaligned" || site.name == "Write") &&
      site.parameterCount == 2 && !site.returnsValue &&
      site.parameterTypes == [address, type] && site.returnType == .void &&
      site.target == .external (runtimeScope ++
        "::System.Void System.Runtime.CompilerServices.Unsafe::" ++
        site.name ++ "(" ++ addressName ++ ",!!0)") then
    some (type, false, aligned)
  else none

/-- Primitive and vector alignment is fixed here; aggregate alignment uses complete layout uses. -/
private def transferAlignmentMatches (layouts : List RawLayout) (type : TypeExpr)
    (alignment : Nat) : Bool :=
  if let some width := integerVectorWidth type then alignment == width else
  match typeStorage layouts type with
  | some (.field (.aggregate _)) => true
  | some (.field kind) => primitiveFieldWidth kind == some alignment
  | _ => false

/-- Typed memory operations from calls are reserved for exact admitted Unsafe transfer helpers. -/
def unsafeTransferMatches (layouts : List RawLayout) (raw : RawInstruction) (emitted : Op) : Bool :=
  match unsafeValueCall raw with
  | some (type, read, false) => typedTransferMatches layouts type read emitted
  | some (type, read, true) => match emitted with
    | .memory (.pointerTransfer kind alignment store) => store == !read &&
      transferKindMatches layouts type kind && transferAlignmentMatches layouts type alignment
    | _ => false
  | none => match raw.opcode, emitted with
    | 40, .loadScalar .. | 40, .storeScalar _ | 40, .loadAggregate _ | 40, .storeAggregate _
    | 40, .memory .load128 | 40, .memory .load256 | 40, .memory .load512
    | 40, .memory .store128 | 40, .memory .store256 | 40, .memory .store512 => false
    | _, .memory (.pointerTransfer ..) => false
    | _, _ => true

end CIL.Extraction
