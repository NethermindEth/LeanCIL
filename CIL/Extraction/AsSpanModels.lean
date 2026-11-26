import CIL.Extraction.SpanModels

/-!
# Array overloads of MemoryExtensions.AsSpan

The checked array element and the method's parameter types determine the writable view.
-/

namespace CIL.Extraction

/-- All array overloads belong to the same nongeneric type in System.Memory. -/
private def owner : TypeExpr := .atom spanMemoryScope "System.MemoryExtensions" .classType

/-- The number of int32 parameters determines which part of the array the call exposes. -/
private def signature (range : ArraySpanRange) (element : TypeExpr) : OpenSignature :=
  let bounds := List.replicate (range.argumentCount - 1) (.primitive .int32)
  ⟨0x10, .apply (spanHead true) element, .array element :: bounds⟩

/-- The external identity retains the method type variable from the original MemberRef. -/
private def operand (range : ArraySpanRange) : ModelOperand :=
  let parameters := ",".intercalate ("!!0[]" :: List.replicate (range.argumentCount - 1)
    "System.Int32")
  let target := s!"{spanMemoryScope}::System.Span`1<!!0> System.MemoryExtensions::AsSpan"
  .external (fun _ => signature range (.parameter 0)) "AsSpan" (fun _ => s!"{target}({parameters})")

/-- Array storage excludes reference-bearing and byref-like elements from the checked view. -/
private def operation (range : ArraySpanRange) (reader : CallLayouts) (method : MethodRef) :
    Option MemoryOp := do
  let [element] := method.methodArguments | none
  let _ ← reader.storage (.array element)
  let width ← (reader.valueShape element).size?
  return .arraySpan (← arrayElementType element width) true range

/-- Only a static generic method with this closed array signature selects the overload. -/
private def overload (range : ArraySpanRange) : ModelOverload :=
  { operand := operand range
    accepts := fun method => match method.methodArguments with
      | [element] => !method.hasThis && method.genericArity == 1 && method.owner == owner &&
          method.name == name!"AsSpan" && method.signature 0x10 == signature range element
      | _ => false
    resolve := fun reader method => RuntimeModel.memory <$> operation range reader method }

/-- The reserved member admits the whole-array, start-index and counted overloads. -/
def asSpanEntries : List ModelEntry :=
  [{ opcode := .call, owner, name := name!"AsSpan", ownsName := true,
     overloads := [.whole, .fromStart, .counted].map overload }]

/-- Each selected array overload executes a checked memory operation. -/
theorem asSpanEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ op, property (.memory op)) :
    ∀ entry ∈ asSpanEntries, entry.Yields property := by
  intro entry member reader method model found
  simp only [asSpanEntries, List.mem_singleton] at member
  subst entry
  obtain ⟨row, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨range, _, rfl⟩ := List.mem_map.mp (ModelEntry.select?_mem selected)
  obtain ⟨op, _, rfl⟩ := Option.map_eq_some_iff.mp resolved
  exact memory op

#print axioms asSpanEntries_yields

end CIL.Extraction
