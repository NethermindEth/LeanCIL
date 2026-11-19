import CIL.Extraction.SpanModels

/-!
# Value-producing span constructors

Each overload binds an external MemberRef to the checked construction for its closed element.
-/

namespace CIL.Extraction

/-- The explicit arguments determine how the constructor locates its storage. -/
private inductive Source where
  | array | range | pointer | reference

/-- Open and closed signatures differ only in the owner's element type. -/
private def Source.signature (source : Source) (element : TypeExpr) : OpenSignature :=
  let int := TypeExpr.atom runtimeScope "System.Int32"
  ⟨0x20, .void, match source with
    | .array => [.array element]
    | .range => [.array element, int, int]
    | .pointer => [.pointer .void, int]
    | .reference => [.byref element]⟩

/-- The target names the closed owner and the parameter types of its open declaration. -/
private def Source.operand (source : Source) : ModelOperand :=
  .external (fun _ => source.signature (.ownerParameter 0)) ".ctor" fun method => do
    let .apply (.constructor _ owner) element := method.owner | none
    let name ← spanElementName element
    let parameters := match source with
      | .array => "!0[]" | .range => "!0[],System.Int32,System.Int32"
      | .pointer => "System.Void*,System.Int32" | .reference => "!0&"
    return s!"{runtimeScope}::System.Void {owner}<{name}>::.ctor({parameters})"

/-- Array views require admissible array storage. Aggregate widths use the checked layout. -/
private def Source.operation (source : Source) (writable : Bool) (reader : CallLayouts)
    (method : MethodRef) : Option MemoryOp := do
  let .apply _ element := method.owner | none
  let _ ← spanElementName element
  let width ← match element with
    | .aggregate .. => (reader.valueShape element).size?
    | _ => spanElementWidth element
  match source with
  | .reference => return .spanSingleReference width writable
  | .pointer =>
    if !writable && element == .atom runtimeScope "System.Byte" then return .spanCreate
    return .spanFromReference width writable
  | .array | .range =>
    let _ ← reader.storage (.array element)
    let range := match source with | .range => ArraySpanRange.counted | _ => .whole
    return .arraySpan (← arrayElementType element width) writable range

/-- The closed instance constructor must agree with the declaration on its result and arguments. -/
private def Source.overload (source : Source) (writable : Bool) : ModelOverload :=
  { operand := source.operand
    accepts := fun method => match method.owner with
      | .apply head element => head == spanHead writable && method.name == name!".ctor" &&
          method.hasThis && method.genericArity == 0 && method.methodArguments.isEmpty &&
          method.signature 0x20 == source.signature element
      | _ => false
    resolve := fun reader method =>
      RuntimeModel.memory <$> source.operation writable reader method }

/-- Both span owners reserve their constructor name for the four value-producing overloads. -/
def spanConstructorEntries : List ModelEntry := [true, false].map fun writable =>
  { opcode := .newobj, owner := spanHead writable, name := name!".ctor", ownsName := true,
    overloads := [Source.array, .range, .pointer, .reference].map (·.overload writable) }

/-- Every resolved span constructor executes a checked memory operation. -/
theorem spanConstructorEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ spanConstructorEntries, entry.Yields property := by
  intro entry member reader method model found
  obtain ⟨writable, _, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp (ModelEntry.select?_mem selected)
  obtain ⟨op, _, rfl⟩ := Option.map_eq_some_iff.mp resolved
  exact memory op

#print axioms spanConstructorEntries_yields

end CIL.Extraction
