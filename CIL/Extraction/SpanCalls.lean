import CIL.Extraction.Generics

/-!
# Exact reference-free span calls

Runtime span members and array-view factories retain their element identity, argument arity,
width and write capability in translation evidence. Aggregate widths use checked layouts.
Array factories require the exact
System.Memory identity; the span types and primitive elements require System.Runtime.
-/

namespace CIL.Extraction

/-- The exact assembly defining the supported array extension methods. -/
def spanMemoryScope : String :=
  "System.Memory, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

/-- The observable choice made by a supported span call. -/
inductive SpanCall where
  | empty (width : Nat) (writable : Bool)
  | reinterpret (sourceWidth targetWidth : Nat) (writable : Bool)
  | copy (width : Nat) (tryCopy : Bool)
  | reference (width : Nat) (writable : Bool)
  | singleReference (width : Nat) (writable : Bool)
  | fill (width : Nat) (clear : Bool)
  | arrayFill (element : ArrayElement) (counted : Bool)
  | item (width : Nat) | length | slice (counted : Bool) | readOnly
  | array (element : ArrayElement) (writable : Bool) (range : ArraySpanRange)
  deriving DecidableEq, Repr

/-- A span operation's exact semantic parameters, independent of other memory operations. -/
private def emittedSpanCall : Op → Option SpanCall
  | .memory (.spanEmpty width writable) => some (.empty width writable)
  | .memory (.spanReinterpret source target writable) => some (.reinterpret source target writable)
  | .memory (.spanCopy width tryCopy) => some (.copy width tryCopy)
  | .memory (.spanFromReference width writable) => some (.reference width writable)
  | .memory (.spanSingleReference width writable) => some (.singleReference width writable)
  | .memory (.spanFill width clear) => some (.fill width clear)
  | .memory (.arrayFill element counted) => some (.arrayFill element counted)
  | .memory (.spanItem width) => some (.item width)
  | .memory .spanLength => some .length
  | .memory (.spanSlice counted) => some (.slice counted)
  | .memory .spanReadOnly => some .readOnly
  | .memory (.arraySpan element writable range) => some (.array element writable range)
  | _ => none

/-- Closed span element names retain nested type arguments in runtime signatures. -/
def spanElementName (type : TypeExpr) : Option String := do
  if let .aggregate identity _ := type then
    return String.ofList (← aggregateName identity)
  if let some (_, name) := namedType type then
    return String.ofList name
  let .apply (.constructor _ name) (.atom _ element) := type | none
  if (integerVectorWidth type).isSome then some (name ++ "<" ++ element ++ ">") else none

/-- A span member or array constructor with a fully specified owner and signature. -/
private def spanMemberCall (opcode : Nat) (site : CallSite)
    (aggregateWidth : Nat := 0) : Option SpanCall := do
  let .apply (.constructor _ owner) elementType := site.declaringType
    | none
  let elementName ← spanElementName elementType
  let .span width writable ← spanStorage site.declaringType aggregateWidth | none
  let arrayElement := arrayElementType elementType aggregateWidth
  if !site.typeArguments.isEmpty || site.parameterCount != site.parameterTypes.length then none
    else pure ()
  let intType := TypeExpr.atom runtimeScope "System.Int32"
  let ownerName := owner ++ "<" ++ elementName ++ ">"
  let target (result parameters : String) := MethodId.external
    (runtimeScope ++ "::" ++ result ++ " " ++ ownerName ++ "::" ++ site.name ++
      "(" ++ parameters ++ ")")
  if opcode == 115 && site.name == ".ctor" && site.hasThis &&
      !site.returnsValue && site.returnType == .void then
    if site.parameterTypes == [.byref elementType] &&
        site.target == target "System.Void" "!0&" then
      some (.singleReference width writable)
    else if site.parameterTypes == [.pointer .void, intType] &&
        site.target == target "System.Void" "System.Void*,System.Int32" then
      if !writable && elementType == .atom runtimeScope "System.Byte" then none
      else some (.reference width writable)
    else do
      let element ← arrayElement
      if site.parameterTypes == [.array elementType] &&
          site.target == target "System.Void" "!0[]" then
        some (.array (← arrayElement) writable .whole)
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
  else if opcode == 40 && site.hasThis &&
      site.parameterTypes == [.apply (.constructor runtimeScope "System.Span`1") elementType] &&
      site.name == "CopyTo" && !site.returnsValue && site.returnType == .void &&
      site.target == target "System.Void" "System.Span`1<!0>" then some (.copy width false)
  else if opcode == 40 && site.hasThis &&
      site.parameterTypes == [.apply (.constructor runtimeScope "System.Span`1") elementType] &&
      site.name == "TryCopyTo" && site.returnsValue &&
      site.returnType == .atom runtimeScope "System.Boolean" &&
      site.target == target "System.Boolean" "System.Span`1<!0>" then some (.copy width true)
  else if opcode != 40 || !site.returnsValue then none
  else if !site.hasThis && site.name == "op_Implicit" then
    if site.returnType == site.declaringType && site.parameterTypes == [.array elementType] &&
        site.target == target (owner ++ "<!0>") "!0[]" then
      some (.array (← arrayElement) writable .whole)
    else if writable && site.returnType ==
        .apply (.constructor runtimeScope "System.ReadOnlySpan`1") elementType &&
        site.parameterTypes == [site.declaringType] &&
        site.target == target "System.ReadOnlySpan`1<!0>" "System.Span`1<!0>" then
      some .readOnly
    else none
  else if !site.hasThis && site.name == "get_Empty" && site.parameterTypes.isEmpty &&
      site.returnType == site.declaringType &&
      site.target == target (owner ++ "<!0>") "" then some (.empty width writable)
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
def spanLocalConstructor (site : CallSite) (aggregateWidth : Nat := 0) : Option SpanConstructor := do
  if let some (.array element writable range) := spanMemberCall 115 site aggregateWidth then
    return .array element writable range
  if let some (.singleReference width writable) := spanMemberCall 115 site aggregateWidth then
    return .singleReference width writable
  if site.name != ".ctor" || !site.hasThis || site.returnsValue ||
      !site.typeArguments.isEmpty || site.parameterCount != 2 || site.returnType != .void ||
      site.parameterTypes != [.pointer .void, .atom runtimeScope "System.Int32"] then none
    else pure ()
  let .apply (.constructor _ owner) elementType := site.declaringType | none
  let element ← spanElementName elementType
  let .span width writable ← spanStorage site.declaringType aggregateWidth | none
  if site.target != .external (runtimeScope ++ "::System.Void " ++ owner ++ "<" ++ element ++
      ">::.ctor(System.Void*,System.Int32)") then none else some (.reference width writable)

/-- Aggregate constructor widths are bound separately by mandatory layout-use evidence.
    Only aggregate metadata yields the zero-width placeholder in a folded descriptor. -/
def spanConstructorMatches : SpanConstructor → SpanConstructor → Bool
  | .empty expected writable, .empty actual capability
  | .reference expected writable, .reference actual capability
  | .singleReference expected writable, .singleReference actual capability =>
    (expected == 0 || expected == actual) && writable == capability
  | .array expected writable range, .array actual capability actualRange =>
    expected.metadata == actual.metadata && writable == capability && range == actualRange
  | expected, actual => expected == actual

/-- Array fill binds the exact primitive or enum element and optional int32 range. -/
private def arrayFillCall (opcode : Nat) (site : CallSite) : Option SpanCall := do
  if opcode != 40 || site.hasThis || site.returnsValue || site.returnType != .void ||
      site.name != "Fill" || site.declaringType != .atom runtimeScope "System.Array" ||
      site.parameterCount != site.parameterTypes.length || site.ownerArgumentCount != 0 then none
      else pure ()
  let [elementType] := site.typeArguments | none
  let element ← arrayElementType elementType
  match element with
  | .aggregate .. | .vector .. => none
  | _ =>
    let intType := TypeExpr.atom runtimeScope "System.Int32"
    let (counted, suffix) ← if site.parameterTypes == [.array elementType, elementType] then
        some (false, "")
      else if site.parameterTypes == [.array elementType, elementType, intType, intType] then
        some (true, ",System.Int32,System.Int32") else none
    if site.target != .external
        (runtimeScope ++ "::System.Void System.Array::Fill(!!0[],!!0" ++ suffix ++ ")")
      then none else some (.arrayFill element counted)

/-- The array overloads of AsSpan accept an array and zero, one or two int32 arguments. -/
private def arrayExtensionCall (opcode : Nat) (site : CallSite)
    (aggregateWidth : Nat := 0) : Option SpanCall := do
  if opcode != 40 || site.hasThis || !site.returnsValue || site.name != "AsSpan" ||
      site.declaringType != .atom spanMemoryScope "System.MemoryExtensions" ||
      site.parameterCount != site.parameterTypes.length then none else pure ()
  let [elementType] := site.typeArguments | none
  let arrayElement := arrayElementType elementType aggregateWidth
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
      parameters ++ ")") then none else some (.array (← arrayElement) true range)

/-- Reinterpretation retains readonly status and both primitive or enum element types. -/
private def reinterpretCall (opcode : Nat) (site : CallSite)
    (sourceAggregateWidth targetAggregateWidth : Nat) : Option SpanCall := do
  if opcode != 40 || site.hasThis || !site.returnsValue || site.parameterCount != 1 ||
      site.declaringType != .atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal" then
    none else pure ()
  let (source, target, resultName) ← match site.name, site.typeArguments with
    | "AsBytes", [source] => some (source, .atom runtimeScope "System.Byte", "System.Byte")
    | "Cast", [source, target] => some (source, target, "!!1")
    | _, _ => none
  let sourceWidth ← spanElementWidth source sourceAggregateWidth
  let targetWidth ← spanElementWidth target targetAggregateWidth
  let [input] := site.parameterTypes | none
  let .span _ writable ← spanStorage input | none
  let owner := if writable then "System.Span`1" else "System.ReadOnlySpan`1"
  if input != .apply (.constructor runtimeScope owner) source ||
      site.returnType != .apply (.constructor runtimeScope owner) target ||
      site.target != .external (runtimeScope ++ "::" ++ owner ++ "<" ++ resultName ++
        "> System.Runtime.InteropServices.MemoryMarshal::" ++ site.name ++ "(" ++ owner ++
        "<!!0>)") then none
  else some (.reinterpret sourceWidth targetWidth writable)

/-- Reference factories bind the exact element, output capability and generic signature. -/
private def referenceFactory (opcode : Nat) (site : CallSite)
    (aggregateWidth : Nat) : Option SpanCall := do
  if opcode != 40 || site.hasThis || !site.returnsValue || site.parameterCount != 2 ||
      site.declaringType != .atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal" then
    none else pure ()
  let [element] := site.typeArguments | none
  let writable ← if site.name == "CreateSpan" then some true
    else if site.name == "CreateReadOnlySpan" then some false else none
  let owner := if writable then "System.Span`1" else "System.ReadOnlySpan`1"
  if site.parameterTypes != [.byref element, .atom runtimeScope "System.Int32"] ||
      site.returnType != .apply (.constructor runtimeScope owner) element ||
      site.target != .external (runtimeScope ++ "::" ++ owner ++
        "<!!0> System.Runtime.InteropServices.MemoryMarshal::" ++ site.name ++
        "(!!0&,System.Int32)") then none
  else some (.reference (← spanElementWidth element aggregateWidth) writable)

/-- An exactly checked span indexer returns a reference, including readonly metadata modifiers. -/
def spanCallReturnsReference (site : CallSite) : Bool :=
  (spanMemberCall 40 site).any fun operation => match operation with
    | .item _ => true
    | _ => false

/-- Exact span signatures and primitive/vector widths. Aggregate widths are separately bound
    by mandatory LayoutUsesComplete and MethodLayoutsValid evidence. -/
def spanCallMatches (instruction : RawInstruction) (emitted : Op) : Bool :=
    let (sourceWidth, targetWidth) := match emittedSpanCall emitted with
      | some (.reinterpret source target _) => (source, target)
      | some (.copy width _) | some (.fill width _) | some (.item width)
      | some (.reference width _) | some (.singleReference width _)
      | some (.empty width _) => (width, width)
      | some (.array element _ _) => (element.width, element.width)
      | _ => (0, 0)
    let expected := match instruction.operand with
      | .call site => (arrayFillCall instruction.opcode site).orElse (fun _ =>
          (spanMemberCall instruction.opcode site sourceWidth).orElse
          (fun _ => (arrayExtensionCall instruction.opcode site sourceWidth).orElse
            (fun _ => (referenceFactory instruction.opcode site sourceWidth).orElse
              (fun _ => reinterpretCall instruction.opcode site sourceWidth targetWidth))))
      | _ => none
    expected == emittedSpanCall emitted

end CIL.Extraction
