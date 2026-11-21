import CIL.Extraction.SpanModels

/-! Bulk span and array calls use checked memory operations on the original evaluation stack. -/

namespace CIL.Extraction

/-- Each form identifies one declaration of a bulk memory member. -/
private inductive BulkMember where
  | fill | clear | copy (trying : Bool) | arrayFill (counted : Bool)

/-- The table key and raw metadata spelling of the member name. -/
private def BulkMember.names : BulkMember → MetadataName × String
  | .fill | .arrayFill _ => (name!"Fill", "Fill")
  | .clear => (name!"Clear", "Clear")
  | .copy false => (name!"CopyTo", "CopyTo")
  | .copy true => (name!"TryCopyTo", "TryCopyTo")

/-- The signature uses the owner's element for spans and the method's element for arrays. -/
private def BulkMember.signature (member : BulkMember) (element : TypeExpr) : OpenSignature :=
  let int := TypeExpr.atom runtimeScope "System.Int32"
  match member with
  | .fill => ⟨0x20, .void, [element]⟩
  | .clear => ⟨0x20, .void, []⟩
  | .copy trying => ⟨0x20, if trying then .atom runtimeScope "System.Boolean" else .void,
      [.apply (spanHead true) element]⟩
  | .arrayFill counted => ⟨0x10, .void,
      if counted then [.array element, element, int, int] else [.array element, element]⟩

/-- The open declaration and exact external target bound to this overload. -/
private def BulkMember.operand (member : BulkMember) : ModelOperand :=
  let name := member.names.2
  match member with
  | .arrayFill counted =>
    let parameters := if counted then "!!0[],!!0,System.Int32,System.Int32" else "!!0[],!!0"
    .external (fun _ => member.signature (.parameter 0)) name fun _ =>
      some s!"{runtimeScope}::System.Void System.Array::Fill({parameters})"
  | _ =>
    .external (fun _ => member.signature (.ownerParameter 0)) name fun method => do
      let .apply (.constructor _ owner) element := method.owner | none
      let elementName ← spanElementName element
      let result := if member matches .copy true then "System.Boolean" else "System.Void"
      let parameters := match member with
        | .copy _ => "System.Span`1<!0>" | .fill => "!0" | _ => ""
      return s!"{runtimeScope}::{result} {owner}<{elementName}>::{name}({parameters})"

/-- The closed receiver or generic argument supplies the element of this overload. -/
private def BulkMember.element (member : BulkMember) (owner : TypeExpr) (method : MethodRef) :
    Option TypeExpr := do
  match member with
  | .arrayFill _ =>
    let [element] := method.methodArguments | none
    _root_.guard (method.owner == owner && !method.hasThis && method.genericArity == 1)
    return element
  | _ =>
    let .apply head element := method.owner | none
    _root_.guard (head == owner && method.hasThis && method.genericArity == 0 &&
      method.methodArguments.isEmpty)
    return element

/-- A closed call selects exactly its declared result and parameter list. -/
private def BulkMember.accepts (member : BulkMember) (owner : TypeExpr) (method : MethodRef) :
    Bool := (member.element owner method).any fun element =>
  let signature := member.signature element
  method.name == member.names.1 && method.returnType == signature.returnType &&
    method.parameters == signature.parameters

/-- Array fills require scalar storage. Span operations also admit checked structs and vectors. -/
private def BulkMember.operation (member : BulkMember) (owner : TypeExpr) (reader : CallLayouts)
    (method : MethodRef) : Option MemoryOp := do
  let element ← member.element owner method
  if let .arrayFill counted := member then
    let storage ← arrayElementType element
    if storage matches .aggregate .. | .vector .. then none
    return .arrayFill storage counted
  let width ← match element with
    | .aggregate .. => (reader.valueShape element).size?
    | _ => spanElementWidth element
  let _ ← spanElementName element
  match member with
  | .copy trying => return .spanCopy width trying
  | .fill => return .spanFill width false
  | .clear => return .spanFill width true
  | .arrayFill _ => none

/-- Each overload resolves only to its checked memory operation. -/
private def bulkEntry (owner : TypeExpr) (first : BulkMember) (others : List BulkMember := []) :
    ModelEntry :=
  { opcode := .call, owner, name := first.names.1, ownsName := true,
    overloads := (first :: others).map fun member =>
      { operand := member.operand, accepts := member.accepts owner,
        resolve := fun reader method =>
          RuntimeModel.memory <$> member.operation owner reader method } }

/-- The seven owner and name pairs cover both copy receivers and both array fill overloads. -/
def spanBulkEntries : List ModelEntry :=
  [bulkEntry (spanHead true) .fill, bulkEntry (spanHead true) .clear,
   bulkEntry (spanHead true) (.copy false), bulkEntry (spanHead false) (.copy false),
   bulkEntry (spanHead true) (.copy true), bulkEntry (spanHead false) (.copy true),
   bulkEntry (.atom runtimeScope "System.Array") (.arrayFill false) [.arrayFill true]]

/-- Every resolved bulk call executes a memory model. -/
theorem spanBulkEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ spanBulkEntries, entry.Yields property := by
  have yields (owner first others) : (bulkEntry owner first others).Yields property := by
    intro reader method model found
    obtain ⟨row, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
    have listed := ModelEntry.select?_mem (entry := bulkEntry owner first others) selected
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp listed
    obtain ⟨operation, _, rfl⟩ := Option.map_eq_some_iff.mp resolved
    exact memory operation
  intro entry member
  simp only [spanBulkEntries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply yields

#print axioms spanBulkEntries_yields

end CIL.Extraction
