import CIL.Extraction.Generics

/-!
# Span call names

Span element names as runtime signatures spell them and the assembly defining array extensions.
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
  if (integerVectorWidth type).isSome then return (← name.signatureName?) ++ "<" ++ element ++ ">"
  else none

end CIL.Extraction
