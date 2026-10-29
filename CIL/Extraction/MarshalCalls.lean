import CIL.Extraction.UnsafeTransfers

/-!
# Exact byte-span value transfers

MemoryMarshal calls retain their complete generic signature and transfer representation.
Aggregate widths additionally require the existing complete layout-use certificate.
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

/-- No other raw instruction may manufacture a byte-span transfer operation. -/
def marshalTransferMatches (layouts : List RawLayout) (raw : RawInstruction) : Op → Bool
  | .memory (.marshalRead kind trying) => marshalCallMatches layouts raw kind true trying
  | .memory (.marshalWrite kind trying) => marshalCallMatches layouts raw kind false trying
  | _ => match raw.operand with
    | .call site => !(site.declaringType ==
        .atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal" &&
        site.name ∈ ["Read", "Write", "TryRead", "TryWrite"])
    | _ => true

end CIL.Extraction
