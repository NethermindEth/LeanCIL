import CIL.Extraction.Generics

/-!
# Exact reference-free span calls

Span constructors and bulk operations bind their element identity, argument arity, width and
write capability in translation evidence. Aggregate widths use checked layouts.
-/

namespace CIL.Extraction

/-- The exact assembly defining the supported array extension methods. -/
def spanMemoryScope : String :=
  metadata_text%
    "System.Memory, Version=11.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

/-- The observable choice made by a supported span call. -/
inductive SpanCall where
  | reference (width : Nat) (writable : Bool)
  | singleReference (width : Nat) (writable : Bool)
  | array (element : ArrayElement) (writable : Bool) (range : ArraySpanRange)
  deriving DecidableEq, Repr

/-- The memory instruction for a resolved span signature. -/
def SpanCall.instruction : SpanCall → Instruction
  | .reference width writable => .memory (.spanFromReference width writable)
  | .singleReference width writable => .memory (.spanSingleReference width writable)
  | .array element writable range => .memory (.arraySpan element writable range)

/-- A span operation's exact semantic parameters, independent of other memory operations. -/
private def emittedSpanCall : Instruction → Option SpanCall
  | .memory (.spanFromReference width writable) => some (.reference width writable)
  | .memory (.spanSingleReference width writable) => some (.singleReference width writable)
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


/-- The span member or factory at a raw site, with aggregate widths from layout evidence. -/
def spanCall (instruction : RawInstruction) (width : Nat := 0) :
    Option SpanCall := do
  let .call site := instruction.operand | none
  let opcode := instruction.opcode
  spanMemberCall opcode site width

/-- Exact span signatures and primitive/vector widths. Aggregate widths are separately bound
    by mandatory LayoutUsesComplete and MethodLayoutsValid evidence. -/
def spanCallMatches (instruction : RawInstruction) (emitted : Instruction) : Bool :=
    let width := match emittedSpanCall emitted with
      | some (.reference width _) | some (.singleReference width _) => width
      | some (.array element _ _) => element.width
      | _ => 0
    match emitted with
    | .memory (.spanCopy ..) | .memory (.spanFill ..) | .memory (.arrayFill ..)
    | .memory (.spanEmpty ..) | .memory (.spanItem _) | .memory .spanLength
    | .memory (.spanSlice _) | .memory .spanReadOnly => false
    | _ => spanCall instruction width == emittedSpanCall emitted

end CIL.Extraction
