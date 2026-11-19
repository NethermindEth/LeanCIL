import CIL.Extraction.Generics

/-!
# Exact reference-free span calls

Folded constructors bind the local span's element, argument types, width and write capability.
Aggregate widths use checked layouts.
-/

namespace CIL.Extraction

/-- The exact assembly defining the supported array extension methods. -/
def spanMemoryScope : String :=
  metadata_text%
    "System.Memory, Version=11.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

/-- Closed span element names retain nested type arguments in runtime signatures. -/
def spanElementName (type : TypeExpr) : Option String := do
  if let .aggregate identity _ := type then
    return String.ofList (← aggregateName identity)
  if let some (_, name) := namedType type then
    return String.ofList name
  let .apply (.constructor _ name) (.atom _ element) := type | none
  if (integerVectorWidth type).isSome then some (name ++ "<" ++ element ++ ">") else none

/-- An in-place constructor binds the local span's element, capability and explicit arguments. -/
def spanLocalConstructor (site : CallSite) (aggregateWidth : Nat := 0) :
    Option SpanConstructor := do
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
  if site.name != ".ctor" || !site.hasThis || site.returnsValue || site.returnType != .void then
    none
  else if site.parameterTypes == [.byref elementType] &&
      site.target == target "System.Void" "!0&" then
    return .singleReference width writable
  else if site.parameterTypes == [.pointer .void, intType] &&
      site.target == target "System.Void" "System.Void*,System.Int32" then
    return .reference width writable
  else if site.parameterTypes == [.array elementType] &&
      site.target == target "System.Void" "!0[]" then
    return .array (← arrayElement) writable .whole
  else if site.parameterTypes == [.array elementType, intType, intType] &&
      site.target == target "System.Void" "!0[],System.Int32,System.Int32" then
    return .array (← arrayElement) writable .counted
  else none

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

/-- Modelled span operations require a checked model binding at their call site. -/
def spanEmissionAllowed : Instruction → Bool
  | .memory .spanCreate | .memory (.spanFromReference ..) | .memory (.spanSingleReference ..)
  | .memory (.arraySpan ..) | .memory (.spanCopy ..) | .memory (.spanFill ..)
  | .memory (.arrayFill ..) | .memory (.spanEmpty ..) | .memory (.spanItem _) | .memory .spanLength
  | .memory (.spanSlice _) | .memory .spanReadOnly => false
  | _ => true

end CIL.Extraction
