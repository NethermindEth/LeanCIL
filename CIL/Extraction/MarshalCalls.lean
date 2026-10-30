import CIL.Extraction.UnsafeTransfers

/-!
# Exact byte-span value transfers

MemoryMarshal calls retain their complete generic signature and transfer representation.
Aggregate widths additionally require the existing complete layout-use certificate.
`Vector128.Create<byte>` and `Vector256.Create<byte>` over a byte span are the same checked
read of the vector, including the `ArgumentOutOfRangeException` for a short span.
-/

namespace CIL.Extraction

/-- An exact runtime generic call agrees with its lowered byte-span operation. -/
private def marshalCallMatches (layouts : List RawLayout) (raw : RawInstruction)
    (kind : TransferKind) (read trying : Bool) : Bool := Id.run do
  if raw.opcode != 40 then return false
  let .call site := raw.operand | return false
  let [type] := site.typeArguments | return false
  if site.declaringType != .atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal" ||
      site.hasThis || !transferKindMatches layouts type kind then return false
  let name := if read then (if trying then "TryRead" else "Read")
    else if trying then "TryWrite" else "Write"
  let spanName := if read then "System.ReadOnlySpan`1" else "System.Span`1"
  let span := TypeExpr.apply (.constructor runtimeScope spanName)
    (.atom runtimeScope "System.Byte")
  let parameters := if read && !trying then [span] else [span, .byref type]
  let result := if trying then TypeExpr.atom runtimeScope "System.Boolean"
    else if read then type else .void
  let resultName := if trying then "System.Boolean" else if read then "!!0" else "System.Void"
  let parameterNames := spanName ++ "<System.Byte>" ++ (if read && !trying then "" else ",!!0&")
  return site.name == name && site.parameterCount == parameters.length &&
    site.parameterTypes == parameters && site.returnType == result &&
    site.returnsValue == (read || trying) &&
    site.target == .external (runtimeScope ++ "::" ++ resultName ++
      " System.Runtime.InteropServices.MemoryMarshal::" ++ name ++ "(" ++ parameterNames ++ ")")

/-- The vector type a byte-span vector construction produces, by transfer shape. -/
private def spanVectorOwner : TransferKind → Option String
  | .snapshot .vector128 => some "System.Runtime.Intrinsics.Vector128"
  | .snapshot .vector256 => some "System.Runtime.Intrinsics.Vector256"
  | _ => none

/-- A call to `Vector128.Create<byte>` or `Vector256.Create<byte>` taking one read-only span,
    by owner, name, type argument and parameter shape alone. -/
private def byteSpanCreateFamily (site : CallSite) : Bool :=
  site.name == "Create" && site.typeArguments == [.atom runtimeScope "System.Byte"] &&
  (site.declaringType == .atom intrinsicsScope "System.Runtime.Intrinsics.Vector128" ||
    site.declaringType == .atom intrinsicsScope "System.Runtime.Intrinsics.Vector256") &&
  match site.parameterTypes with
  | [.apply (.constructor _ "System.ReadOnlySpan`1") _] => true
  | _ => false

/-- An exact byte-span vector construction agrees with the checked read of its vector. -/
private def byteSpanCreateMatches (raw : RawInstruction) (kind : TransferKind) : Bool :=
  Id.run do
  if raw.opcode != 40 then return false
  let .call site := raw.operand | return false
  let some owner := spanVectorOwner kind | return false
  let byte := TypeExpr.atom runtimeScope "System.Byte"
  let span := TypeExpr.apply (.constructor runtimeScope "System.ReadOnlySpan`1") byte
  let vector := TypeExpr.apply (.constructor intrinsicsScope (owner ++ "`1")) byte
  return site.declaringType == .atom intrinsicsScope owner && site.name == "Create" &&
    !site.hasThis && site.typeArguments == [byte] && site.parameterCount == 1 &&
    site.parameterTypes == [span] && site.returnType == vector && site.returnsValue &&
    site.target == .external (intrinsicsScope ++ "::" ++ owner ++ "`1<!!0> " ++ owner ++
      "::Create(System.ReadOnlySpan`1<!!0>)")

/-- No other raw instruction may manufacture a byte-span transfer operation, and a byte-span
    vector construction emits only the exact read of its vector. -/
def marshalTransferMatches (layouts : List RawLayout) (raw : RawInstruction) : Op → Bool
  | .memory (.marshalRead kind trying) => marshalCallMatches layouts raw kind true trying ||
    !trying && byteSpanCreateMatches raw kind
  | .memory (.marshalWrite kind trying) => marshalCallMatches layouts raw kind false trying
  | _ => match raw.operand with
    | .call site => !(site.declaringType ==
        .atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal" &&
        site.name ∈ ["Read", "Write", "TryRead", "TryWrite"]) && !byteSpanCreateFamily site
    | _ => true

end CIL.Extraction
