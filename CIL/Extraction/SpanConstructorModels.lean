import CIL.Extraction.SpanModels

/-!
# Span constructors

Each overload binds an external MemberRef to the checked construction for its closed element.
`newobj` pushes the constructed span; `call` on the home of a span local or homed parameter
stores it in the slot the home names. `newobj` of `ReadOnlySpan<byte>(void*, int)` views
extracted static data, while the in-place call views any readable bytes, as a reference span.
-/

namespace CIL.Extraction

/-- The explicit arguments determine how the constructor locates its storage. -/
private inductive Source where
  | array | range | pointer | reference

/-- Open and closed signatures differ only in the owner's element type. -/
private def Source.signature (source : Source) (element : TypeExpr) : OpenSignature :=
  let int := TypeExpr.primitive .int32
  ⟨0x20, .void, match source with
    | .array => [.array element]
    | .range => [.array element, int, int]
    | .pointer => [.pointer .void, int]
    | .reference => [.byref element]⟩

/-- The target names the closed owner and the parameter types of its open declaration. -/
private def Source.operand (source : Source) : ModelOperand :=
  .external (fun _ => source.signature (.ownerParameter 0)) ".ctor" fun method => do
    let .apply head element := method.owner | none
    let owner ← spanOwnerName? head
    let name ← spanElementName element
    let parameters := match source with
      | .array => "!0[]" | .range => "!0[],System.Int32,System.Int32"
      | .pointer => "System.Void*,System.Int32" | .reference => "!0&"
    return s!"{runtimeScope}::System.Void {owner}<{name}>::.ctor({parameters})"

/-- Array views require admissible array storage. Aggregate widths use the checked layout. With
    `staticData` a read-only byte span over a pointer must lie in extracted static data. -/
private def Source.constructor (source : Source) (writable staticData : Bool)
    (reader : CallLayouts) (method : MethodRef) : Option SpanConstructor := do
  let .apply _ element := method.owner | none
  let _ ← spanElementName element
  let width ← match element with
    | .aggregate .. => (reader.valueShape element).size?
    | _ => spanElementWidth element
  match source with
  | .reference => return .singleReference width writable
  | .pointer =>
    if staticData && !writable && element == .primitive .byte then
      return .staticBytes
    return .reference width writable
  | .array | .range =>
    let _ ← reader.storage (.array element)
    let range := match source with | .range => ArraySpanRange.counted | _ => .whole
    return .array (← arrayElementType element width) writable range

/-- The closed instance constructor must agree with the declaration on its result and arguments;
    `model` says what the opcode does with the constructed span. -/
private def Source.overload (source : Source) (writable staticData : Bool)
    (model : SpanConstructor → RuntimeModel) : ModelOverload :=
  { operand := source.operand
    accepts := fun method => match method.owner with
      | .apply head element => head == spanHead writable && method.name == name!".ctor" &&
          method.hasThis && method.genericArity == 0 && method.methodArguments.isEmpty &&
          method.signature 0x20 == source.signature element
      | _ => false
    resolve := fun reader method =>
      model <$> source.constructor writable staticData reader method }

/-- The four overloads, in the order their rows are tried. -/
private def sources : List Source := [.array, .range, .pointer, .reference]

/-- Both span owners reserve their constructor name under `newobj` and under `call`. -/
def spanConstructorEntries : List ModelEntry := [true, false].flatMap fun writable =>
  [{ opcode := .newobj, owner := spanHead writable, name := name!".ctor", ownsName := true,
     overloads := sources.map (·.overload writable true fun constructor =>
       .memory constructor.operation) },
   { opcode := .call, owner := spanHead writable, name := name!".ctor", ownsName := true,
     overloads := sources.map (·.overload writable false .spanInPlace) }]

/-- A resolved span constructor executes its checked memory operation, or runs in place. -/
theorem spanConstructorEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation))
    (inPlace : ∀ constructor, property (.spanInPlace constructor)) :
    ∀ entry ∈ spanConstructorEntries, entry.Yields property := by
  intro entry member reader method model found
  obtain ⟨writable, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨row, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp (ModelEntry.select?_mem selected)
    obtain ⟨constructor, _, rfl⟩ := Option.map_eq_some_iff.mp resolved
  · exact memory _
  · exact inPlace constructor

#print axioms spanConstructorEntries_yields

end CIL.Extraction
