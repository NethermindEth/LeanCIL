import CIL.Extraction.ModelTable

/-! The RuntimeHelpers field-handle model binds the scalar element of a readonly span. -/

namespace CIL.Extraction

/-- The field handle is the sole parameter of the generic static member. -/
private def staticSpanSignature (element : TypeExpr) : OpenSignature :=
  { convention := 0x10, parameters := [.atom runtimeScope "System.RuntimeFieldHandle"],
    returnType := .apply (.constructor runtimeScope "System.ReadOnlySpan`1") element }

/-- The closed result must have the primitive or enum element supplied to the generic method. -/
private def staticSpanOperation (reader : CallLayouts) (method : MethodRef) : Option MemoryOp := do
  let [element] := method.methodArguments | none
  guard (!method.hasThis && method.genericArity == 1 &&
    method.signature 0x10 == staticSpanSignature element)
  let .primitive width _ := reader.valueShape element | none
  return .createSpan width

/-- Both the open declaration and the closed member bind the field handle and the span result. -/
def staticSpanEntry : ModelEntry :=
  let owner := "System.Runtime.CompilerServices.RuntimeHelpers"
  let name := "CreateSpan"
  let handle := "System.RuntimeFieldHandle"
  let target := s!"{runtimeScope}::System.ReadOnlySpan`1<!!0> {owner}::{name}({handle})"
  let operand := ModelOperand.external (fun _ => staticSpanSignature (.parameter 0)) name
    (fun _ => some target)
  .single .call (.atom runtimeScope owner) name!"CreateSpan" operand
    (fun reader method => RuntimeModel.memory <$> staticSpanOperation reader method) true

/-- The field handle model executes a memory operation under the caller's storage checks. -/
theorem staticSpanEntry_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) : staticSpanEntry.Yields property := by
  intro reader method model found
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp found
  exact memory _

#print axioms staticSpanEntry_yields

end CIL.Extraction
