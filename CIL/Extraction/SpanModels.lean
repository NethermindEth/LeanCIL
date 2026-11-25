import CIL.Extraction.ModelTable
import CIL.Extraction.SpanCalls

/-!
# Core span member models

A kept span call checks the member's open declaration and its closed receiver, result and
parameters. Indexing and empty span construction read the checked element width.
-/

namespace CIL.Extraction

/-- The operations available on an existing span, including the two static members. -/
inductive SpanMember where
  | item | length | slice (counted : Bool) | isEmpty | pinnable | readOnly | array | empty
  deriving DecidableEq

/-- The member name used to index calls in the model table. -/
def SpanMember.name : SpanMember → MetadataName
  | .item => name!"get_Item"
  | .length => name!"get_Length"
  | .slice _ => name!"Slice"
  | .isEmpty => name!"get_IsEmpty"
  | .pinnable => name!"GetPinnableReference"
  | .readOnly | .array => name!"op_Implicit"
  | .empty => name!"get_Empty"

/-- Signature spelling of the two runtime span definitions. -/
private def spanName (writable : Bool) : String :=
  if writable then "System.Span`1" else "System.ReadOnlySpan`1"

/-- The generic definition that declares members of a writable or read-only span. -/
def spanHead (writable : Bool) : TypeExpr :=
  .constructor runtimeScope (spanName writable)

/-- The runtime signature spelling of a checked span constructor. -/
def spanOwnerName? (head : TypeExpr) : Option String :=
  if head == spanHead true then some (spanName true)
  else if head == spanHead false then some (spanName false) else none

/-- The accessor signature for an element. Open readonly returns carry the required modifier;
    the closed operand carries Cecil's scoped spelling of that return. -/
private def SpanMember.signature (member : SpanMember) (writable openType : Bool)
    (element : TypeExpr) : OpenSignature := Id.run do
  let owner := TypeExpr.apply (spanHead writable) element
  let int := TypeExpr.primitive .int32
  let reference := if writable then TypeExpr.byref element else if openType then
      .modified true runtimeScope "System.Runtime.InteropServices.InAttribute" (.byref element)
    else .atom runtimeScope "!0& modreq(System.Runtime.InteropServices.InAttribute)"
  return match member with
    | .item => ⟨0x20, reference, [int]⟩
    | .pinnable => ⟨0x20, reference, []⟩
    | .length => ⟨0x20, int, []⟩
    | .isEmpty => ⟨0x20, .primitive .boolean, []⟩
    | .slice counted => ⟨0x20, owner, if counted then [int, int] else [int]⟩
    | .readOnly => ⟨0, .apply (spanHead false) element, [owner]⟩
    | .array => ⟨0, owner, [.array element]⟩
    | .empty => ⟨0, owner, []⟩

/-- The declaration and exact external target of a span overload. -/
private def SpanMember.operand (member : SpanMember) (writable : Bool) : ModelOperand :=
  let memberName := match member with
    | .item => "get_Item" | .length => "get_Length" | .slice _ => "Slice"
    | .isEmpty => "get_IsEmpty" | .pinnable => "GetPinnableReference" | .empty => "get_Empty"
    | .array | .readOnly => "op_Implicit"
  let declared := member.signature writable true (.ownerParameter 0)
  .external (fun _ => declared) memberName fun method => do
    let .apply head element := method.owner | none
    let owner ← spanOwnerName? head
    let name ← spanElementName element
    let reference := if writable then "!0&" else
      "!0& modreq(System.Runtime.InteropServices.InAttribute)"
    let (result, parameters) := match member with
      | .item => (reference, "System.Int32")
      | .pinnable => (reference, "")
      | .length => ("System.Int32", "")
      | .isEmpty => ("System.Boolean", "")
      | .array => (owner ++ "<!0>", "!0[]")
      | .empty => (owner ++ "<!0>", "")
      | .slice counted => (owner ++ "<!0>", if counted then "System.Int32,System.Int32"
          else "System.Int32")
      | .readOnly => ("System.ReadOnlySpan`1<!0>", "System.Span`1<!0>")
    return s!"{runtimeScope}::{result} {owner}<{name}>::{memberName}({parameters})"

/-- The closed receiver, element and signature select this overload. -/
private def SpanMember.accepts (member : SpanMember) (writable : Bool) (method : MethodRef) :
    Bool := match method.owner with
  | .apply head element =>
    head == spanHead writable && method.name == member.name && method.genericArity == 0 &&
      method.methodArguments.isEmpty && method.signature (if method.hasThis then 0x20 else 0) ==
        member.signature writable false element
  | _ => false

/-- Scalar flow recognizes an exact element reference before it has a computed layout table. -/
def spanReferenceResult (site : CallSite) : Bool := (do
  let member ← match site.name with
    | "get_Item" => some SpanMember.item
    | "GetPinnableReference" => some SpanMember.pinnable
    | _ => none
  let .span _ writable ← spanStorage site.declaringType | none
  return member.accepts writable site.method && (member.operand writable).bindsSite site
  ).getD false

/-- The operation uses the indexed layout of a closed aggregate element. -/
private def SpanMember.operation (member : SpanMember) (writable : Bool)
    (reader : CallLayouts) (method : MethodRef) : Option MemoryOp := do
  let .apply _ element := method.owner | none
  let width ← match element with
    | .aggregate .. => (reader.valueShape element).size?
    | _ => spanElementWidth element
  let _ ← spanElementName element
  match member with
  | .item => return .spanItem width
  | .length => return .spanLength
  | .slice counted => return .spanSlice counted
  | .isEmpty => return .observeView .spanEmpty
  | .pinnable => return .observeView .spanPinnable
  | .readOnly => return .spanReadOnly
  | .empty => return .spanEmpty width writable
  | .array =>
    let _ ← reader.storage (.array element)
    return .arraySpan (← arrayElementType element width) writable .whole

/-- A span overload binds its own declaration and produces only memory models. -/
private def SpanMember.overload (member : SpanMember) (writable : Bool) : ModelOverload :=
  { operand := member.operand writable, accepts := member.accepts writable,
    resolve := fun reader method =>
      RuntimeModel.memory <$> member.operation writable reader method }

/-- All overloads of one span member share its reserved table slot. -/
def spanEntry (writable : Bool) (member : SpanMember) (others : List SpanMember := []) :
    ModelEntry :=
  { opcode := .call, owner := spanHead writable, name := member.name, ownsName := true,
    overloads := (member :: others).map (·.overload writable) }

/-- Both span owners have array conversions. Only a writable span converts to a readonly span. -/
def spanEntries : List ModelEntry := [true, false].flatMap fun writable =>
  [spanEntry writable .array (if writable then [.readOnly] else []),
   spanEntry writable (.slice false) [.slice true]] ++
    [.item, .length, .isEmpty, .pinnable, .empty].map (spanEntry writable · [])

/-- Every resolved core span member executes a checked memory operation. -/
theorem spanEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ spanEntries, entry.Yields property := by
  have yields (writable : Bool) (member : SpanMember) (others : List SpanMember) :
      (spanEntry writable member others).Yields property := by
    intro reader method model found
    obtain ⟨row, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
    have listed := ModelEntry.select?_mem (entry := spanEntry writable member others) selected
    obtain ⟨form, _, rfl⟩ := List.mem_map.mp listed
    obtain ⟨operation, _, rfl⟩ := Option.map_eq_some_iff.mp resolved
    exact memory operation
  intro entry member
  simp only [spanEntries, List.mem_flatMap, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at member
  obtain ⟨writable, _, (rfl | rfl) | ⟨_, _, rfl⟩⟩ := member <;> apply yields

/-- info: 'CIL.Extraction.spanEntries_yields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms spanEntries_yields
/-- info: 'CIL.Extraction.spanEntry' depends on axioms: [propext] -/
#guard_msgs in #print axioms spanEntry

end CIL.Extraction
