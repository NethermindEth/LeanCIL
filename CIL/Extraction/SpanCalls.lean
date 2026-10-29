import CIL.Extraction.MetadataNames

/-!
# Exact primitive span calls

Runtime span members and array-view factories retain their element identity, argument arity,
width and write capability in translation evidence. Array factories require the exact
System.Memory identity; the span types and primitive elements require System.Runtime.
-/

namespace CIL.Extraction

/-- The exact assembly defining the supported array extension methods. -/
def spanMemoryScope : String :=
  "System.Memory, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

/-- The observable choice made by a supported span call. -/
inductive SpanCall where
  | fill (width : Nat) (clear : Bool)
  | item (width : Nat) | length | slice (counted : Bool) | readOnly
  | array (element : ArrayElement) (writable : Bool) (range : ArraySpanRange)
  deriving DecidableEq, Repr

/-- A span operation's exact semantic parameters, independent of other memory operations. -/
private def emittedSpanCall : Op → Option SpanCall
  | .memory (.spanFill width clear) => some (.fill width clear)
  | .memory (.spanItem width) => some (.item width)
  | .memory .spanLength => some .length
  | .memory (.spanSlice counted) => some (.slice counted)
  | .memory .spanReadOnly => some .readOnly
  | .memory (.arraySpan element writable range) => some (.array element writable range)
  | _ => none

/-- A span member or array constructor with a fully specified owner and signature. -/
private def spanMemberCall (opcode : Nat) (site : CallSite) : Option SpanCall := do
  let .apply (.constructor _ owner) elementType := site.declaringType
    | none
  let elementName ← match elementType with
    | .atom _ name => some name
    | .enum .. => (String.ofList ∘ Prod.snd) <$> namedType elementType
    | _ => none
  let .span width writable ← spanStorage site.declaringType | none
  let element ← arrayElementType elementType
  if !site.typeArguments.isEmpty || site.parameterCount != site.parameterTypes.length then none
    else pure ()
  let intType := TypeExpr.atom runtimeScope "System.Int32"
  let ownerName := owner ++ "<" ++ elementName ++ ">"
  let target (result parameters : String) := MethodId.external
    (runtimeScope ++ "::" ++ result ++ " " ++ ownerName ++ "::" ++ site.name ++
      "(" ++ parameters ++ ")")
  if opcode == 115 && site.name == ".ctor" && site.hasThis &&
      !site.returnsValue && site.returnType == .void then
    if site.parameterTypes == [.array elementType] &&
        site.target == target "System.Void" "!0[]" then
      some (.array element writable .whole)
    else if site.parameterTypes == [.array elementType, intType, intType] &&
        site.target == target "System.Void" "!0[],System.Int32,System.Int32" then
      some (.array element writable .counted)
    else none
  else if opcode == 40 && site.hasThis && writable && !site.returnsValue &&
      site.returnType == .void && site.name == "Clear" && site.parameterTypes.isEmpty &&
      site.target == target "System.Void" "" then some (.fill width true)
  else if opcode == 40 && site.hasThis && writable && !site.returnsValue &&
      site.returnType == .void && site.name == "Fill" && site.parameterTypes == [elementType] &&
      site.target == target "System.Void" "!0" then some (.fill width false)
  else if opcode != 40 || !site.returnsValue then none
  else if !site.hasThis && site.name == "op_Implicit" then
    if site.returnType == site.declaringType && site.parameterTypes == [.array elementType] &&
        site.target == target (owner ++ "<!0>") "!0[]" then
      some (.array element writable .whole)
    else if writable && site.returnType ==
        .apply (.constructor runtimeScope "System.ReadOnlySpan`1") elementType &&
        site.parameterTypes == [site.declaringType] &&
        site.target == target "System.ReadOnlySpan`1<!0>" "System.Span`1<!0>" then
      some .readOnly
    else none
  else if !site.hasThis then none
  else if site.name == "get_Length" && site.returnType == intType &&
      site.parameterTypes.isEmpty && site.target == target "System.Int32" "" then
    some .length
  else if site.name == "get_Item" && site.parameterTypes == [intType] then
    let result := if writable then "!0&" else
      "!0& modreq(System.Runtime.InteropServices.InAttribute)"
    let returnType := if writable then TypeExpr.byref elementType else
      .atom runtimeScope result
    if site.returnType == returnType && site.target == target result "System.Int32" then
      some (.item width) else none
  else if site.name == "Slice" && site.returnType == site.declaringType then
    if site.parameterTypes == [intType] &&
        site.target == target (owner ++ "<!0>") "System.Int32" then some (.slice false)
    else if site.parameterTypes == [intType, intType] &&
        site.target == target (owner ++ "<!0>") "System.Int32,System.Int32" then
      some (.slice true)
    else none
  else none

/-- An exact span constructor, independent of whether CIL allocates or initializes its receiver. -/
def spanLocalConstructor (site : CallSite) : Option SpanConstructor := do
  if let some (.array element writable range) := spanMemberCall 115 site then
    return .array element writable range
  if site.name != ".ctor" || !site.hasThis || site.returnsValue ||
      !site.typeArguments.isEmpty || site.parameterCount != 2 || site.returnType != .void ||
      site.parameterTypes != [.pointer .void, .atom runtimeScope "System.Int32"] then none
    else pure ()
  let .apply (.constructor _ owner) elementType := site.declaringType | none
  let element ← match elementType with
    | .atom _ name => some name
    | .enum .. => (String.ofList ∘ Prod.snd) <$> namedType elementType
    | _ => none
  let .span width writable ← spanStorage site.declaringType | none
  if site.target != .external (runtimeScope ++ "::System.Void " ++ owner ++ "<" ++ element ++
      ">::.ctor(System.Void*,System.Int32)") then none else some (.reference width writable)

/-- The array overloads of AsSpan accept an array and zero, one or two int32 arguments. -/
private def arrayExtensionCall (opcode : Nat) (site : CallSite) : Option SpanCall := do
  if opcode != 40 || site.hasThis || !site.returnsValue || site.name != "AsSpan" ||
      site.declaringType != .atom spanMemoryScope "System.MemoryExtensions" ||
      site.parameterCount != site.parameterTypes.length then none else pure ()
  let [elementType] := site.typeArguments | none
  let element ← arrayElementType elementType
  if site.returnType != .apply (.constructor runtimeScope "System.Span`1") elementType then none
    else pure ()
  let intType := TypeExpr.atom runtimeScope "System.Int32"
  let (range, parameters) ←
    if site.parameterTypes == [.array elementType] then some (.whole, "!!0[]")
    else if site.parameterTypes == [.array elementType, intType] then
      some (.fromStart, "!!0[],System.Int32")
    else if site.parameterTypes == [.array elementType, intType, intType] then
      some (.counted, "!!0[],System.Int32,System.Int32") else none
  if site.target != .external (spanMemoryScope ++
      "::System.Span`1<!!0> System.MemoryExtensions::AsSpan(" ++
      parameters ++ ")") then none else some (.array element true range)

/-- Covered calls cannot be replaced with another operation of the same stack effect. -/
def spanCallMatches (instruction : RawInstruction) (emitted : Op) : Bool :=
  let expected := match instruction.operand with
    | .call site => (spanMemberCall instruction.opcode site).orElse
        (fun _ => arrayExtensionCall instruction.opcode site)
    | _ => none
  expected == emittedSpanCall emitted

end CIL.Extraction
