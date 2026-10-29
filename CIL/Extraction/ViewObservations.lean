import CIL.Extraction.SpanCalls

/-!
# Exact view observations

Span emptiness and pinnable references, and array data references, preserve the identity of
their admitted view types. Their evidence cannot be replaced by another unary operation.
-/

namespace CIL.Extraction

/-- The exact accessor signature fixes the observation without consulting element contents. -/
def viewObservation (raw : RawInstruction) : Option ViewObservation := do
  if raw.opcode != 40 then none else pure ()
  let .call site := raw.operand | none
  if !site.returnsValue || site.parameterCount != site.parameterTypes.length then none else pure ()
  if site.name == "GetArrayDataReference" then
    let [element] := site.typeArguments | none
    let _ ← arrayElementType element
    if site.hasThis || site.parameterTypes != [.array element] ||
        site.returnType != .byref element || site.declaringType !=
          .atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal" ||
        site.target != .external (runtimeScope ++ "::!!0& " ++
          "System.Runtime.InteropServices.MemoryMarshal::GetArrayDataReference(!!0[])") then none
    else some .arrayData
  else
    let .apply (.constructor _ owner) element := site.declaringType | none
    let .span _ writable ← spanStorage site.declaringType | none
    let elementName ← spanElementName element
    if !site.hasThis || !site.typeArguments.isEmpty || !site.parameterTypes.isEmpty then none
      else pure ()
    let target (result : String) := MethodId.external (runtimeScope ++ "::" ++ result ++
      " " ++ owner ++ "<" ++ elementName ++ ">::" ++ site.name ++ "()")
    if site.name == "get_IsEmpty" && site.returnType == .atom runtimeScope "System.Boolean" &&
        site.target == target "System.Boolean" then some .spanEmpty
    else if site.name == "GetPinnableReference" then
      let result := if writable then "!0&" else
        "!0& modreq(System.Runtime.InteropServices.InAttribute)"
      let returnType := if writable then TypeExpr.byref element else .atom runtimeScope result
      if site.returnType == returnType && site.target == target result then some .spanPinnable
      else none
    else none

/-- Accessor calls and observation instructions agree in both directions. -/
def viewObservationMatches (raw : RawInstruction) (emitted : Op) : Bool :=
  let actual := match emitted with
    | .memory (.observeView observation) => some observation
    | _ => none
  viewObservation raw == actual

end CIL.Extraction
