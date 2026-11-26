import CIL.Extraction.ModelTable

/-! Closed method operands for System.Type handles and equality. -/

namespace CIL.Extraction

/-- The exact call site of a static `System.Type` method with `parameters` parameters;
    `methodName` is the metadata name spelling `name`. -/
private def typeMethod (name : String) (methodName : MetadataName) (signature : String)
    (parameters : Nat) : CallSite :=
  let type := TypeExpr.atom runtimeScope (metadata_text% "System.Type") .classType
  let fromHandle := methodName == name!"GetTypeFromHandle"
  let method : MethodRef := {
    owner := type, name := methodName, hasThis := false,
    genericArity := 0,
    returnType := if fromHandle then type else
      .primitive .boolean,
    parameters := if fromHandle then
        [.atom runtimeScope (metadata_text% "System.RuntimeTypeHandle") .valueType]
      else [type, type] }
  { method, declared := method.signature 0, name,
    target := .external (runtimeScope ++ "::" ++ signature), typeArguments := [],
    parameterCount := parameters, returnsValue := true }

/-- The exact System.Type.GetTypeFromHandle call. -/
def getTypeFromHandle : CallSite :=
  typeMethod (metadata_text% "GetTypeFromHandle") name!"GetTypeFromHandle"
    (metadata_text% "System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)") 1

/-- The exact System.Type equality operator call selected by its polarity. -/
def runtimeTypeComparison (equal : Bool) : CallSite :=
  if equal then typeMethod (metadata_text% "op_Equality") name!"op_Equality"
    (metadata_text% "System.Boolean System.Type::op_Equality(System.Type,System.Type)") 2
  else typeMethod (metadata_text% "op_Inequality") name!"op_Inequality"
    (metadata_text% "System.Boolean System.Type::op_Inequality(System.Type,System.Type)") 2

/-- Closed metadata identities for the three System.Type runtime calls. -/
def runtimeTypeEntries : List ModelEntry :=
  [ModelEntry.exact .call getTypeFromHandle.method getTypeFromHandle.declared .typeFromHandle,
   ModelEntry.exact .call (runtimeTypeComparison true).method (runtimeTypeComparison true).declared
     (.typeEquality true),
   ModelEntry.exact .call (runtimeTypeComparison false).method (runtimeTypeComparison false).declared
     (.typeEquality false)]

/-- Each closed System.Type entry resolves to its corresponding handle or comparison model. -/
theorem runtimeTypeEntries_yields {property : RuntimeModel → Prop}
    (handle : property .typeFromHandle) (comparison : ∀ equal, property (.typeEquality equal)) :
    ∀ entry ∈ runtimeTypeEntries, entry.Yields property := by
  intro entry member
  simp only [runtimeTypeEntries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ModelEntry.exact_yields.mpr handle
  · exact ModelEntry.exact_yields.mpr (comparison true)
  · exact ModelEntry.exact_yields.mpr (comparison false)

#print axioms runtimeTypeEntries_yields

end CIL.Extraction
