import CIL.Extraction.Generics

/-!
# Layout coverage

`MethodLayoutsValid` checks only the layout uses it is given. `LayoutUsesComplete` closes
that gap: it derives every layout-dependent site from the raw body (field accesses, struct
loads, stores, copies, initializations, sizes, constructions and Unsafe element offsets), plus every
struct-typed local and homed parameter, and requires the extractor's list to be exactly
that list.
-/

namespace CIL.Extraction

/-- The raw layout index of a struct type. -/
private def aggregateIndex : TypeExpr → Option Nat
  | .aggregate _ index => some index
  | _ => none

/-- Derive required instruction sites from the complete raw body, independently
    of the extractor's optional list of layout uses. -/
def instructionLayoutUses (layouts : List RawLayout) (pc : Nat)
    (instruction : RawInstruction) : Option (List LayoutUse) := do
  match instruction.opcode, instruction.operand with
  -- A class field access carries no layout data: its step resolves the slot, and the size of a
  -- struct array element, from the checked layouts.
  | 0x7b, .field (.object _ _) _ _ _ false | 0x7c, .field (.object _ _) _ _ _ false
  | 0x7d, .field (.object _ _) _ _ _ false => return []
  -- `ldfld`, `ldflda` and `stfld` on a struct instance field, whose declared type must match.
  -- The step reads the offset and width from the checked layouts, so the site needs no use.
  | 0x7b, .field owner index type _ false
  | 0x7c, .field owner index type _ false
  | 0x7d, .field owner index type _ false =>
    let .field (.aggregate parent) ← typeStorage layouts owner | none
    let metadata ← layouts[parent]?
    let field ← metadata.fields[index]?
    if fieldKind? layouts type != some field.type then none else return []
  -- `ldobj`, `stobj`, `initobj`, `cpobj` and `sizeof` of a struct.
  | 0xfe15, .type (.apply (.constructor scope owner) (.aggregate identity index)) =>
    if scope == runtimeScope && owner ∈ ["System.Span`1", "System.ReadOnlySpan`1"] then
      if typeStorage layouts (.aggregate identity index) != some (.field (.aggregate index)) then
        none else return [.size pc index .spanElement]
    else return []
  | opcode, .type type =>
    match aggregateIndex type with
    | none => return []
    | some index =>
      if typeStorage layouts type ≠ some (.field (.aggregate index)) then none
      else if opcode = 0x71 then return [.size pc index .load]
      else if opcode = 0x81 then return [.size pc index .store]
      else if opcode = 0xfe15 then return [.size pc index .initialize]
      else if opcode = 0x70 then return [.size pc index .copy]
      else if opcode = 0xfe1c then return [.size pc index .sizeOf]
      else return []
  -- `newobj` of a struct, then `Unsafe.Add<T>`.
  | 0x73, .call site =>
    if let .apply (.constructor scope owner) (.aggregate _ index) := site.declaringType then
      if scope == runtimeScope && owner ∈ ["System.Span`1", "System.ReadOnlySpan`1"] &&
          site.name == ".ctor" then
        let access := match site.parameterTypes.head? with
          | some (.array _) => SizeAccess.arrayElement | _ => .spanElement
        return [.size pc index access]
    return (aggregateIndex (closeLayoutType layouts site.declaringType)).toList.map
      fun index => .size pc index .construct
  | 0x28, .call site =>
    match site.declaringType, site.typeArguments with
    | .apply (.constructor scope owner) (.aggregate identity index), [] =>
      if site.name == "get_Empty" &&
          typeStorage layouts (.aggregate identity index) != some (.field (.aggregate index)) then
        none else
      if scope == runtimeScope && owner ∈ ["System.Span`1", "System.ReadOnlySpan`1"] &&
          site.name ∈ [".ctor", "op_Implicit"] &&
          (site.parameterTypes.head?.map fun type => match type with
            | .array _ => true | _ => false).getD false then
        return [.size pc index .arrayElement]
      else if scope == runtimeScope && owner ∈ ["System.Span`1", "System.ReadOnlySpan`1"] &&
          site.name ∈ ["get_Item", "CopyTo", "TryCopyTo", "Clear", "Fill", ".ctor", "get_Empty"] then
        return [.size pc index .spanElement] else return []
    | .atom _ "System.MemoryExtensions", [.aggregate _ index] =>
      if site.name == "AsSpan" then return [.size pc index .arrayElement] else return []
    | .atom _ "System.Runtime.CompilerServices.Unsafe", [.aggregate _ index] =>
      if site.name = "Add" then return [.size pc index .referenceAdd]
      else if site.name = "Subtract" then return [.size pc index .referenceSubtract]
      else if site.name ∈ ["ReadUnaligned", "Read"] then return [.size pc index .load]
      else if site.name ∈ ["WriteUnaligned", "Write"] then return [.size pc index .store]
      else return []
    | _, _ => return []
  | _, _ => return []

/-- Every layout use of the method, in order: live instruction sites by pc, then struct
    locals, then struct parameter homes. -/
def expectedLayoutUses (layouts : List RawLayout) (closed : RawMethod)
    (parameters : RawArguments) (reachable : List Bool) : Option (List LayoutUse) := do
  if closed.code.length != reachable.length then none else
    let instructions ← ((closed.code.zip reachable).zipIdx).mapM fun ((instruction, live), pc) =>
      if live then instructionLayoutUses layouts pc instruction else some []
    let locals := (closed.locals.zipIdx).flatMap fun (type, slot) =>
      (aggregateIndex type).toList.map fun index => LayoutUse.local slot index
    let homes ← ((requiredHomeIndices parameters reachable).zipIdx).mapM fun (argument, slot) => do
      let type ← parameters.arguments[argument]?
      return match type with
        | .field (.aggregate index) => [LayoutUse.parameter slot index]
        | _ => []
    return instructions.flatten ++ locals ++ homes.flatten

/-- The extractor's layout uses are exactly the ones the raw body requires. -/
def LayoutUsesComplete (layouts : List RawLayout) (closed : RawMethod)
    (parameters : RawArguments) (reachable : List Bool) (uses : List LayoutUse) : Prop :=
  expectedLayoutUses layouts closed parameters reachable = some uses

instance (layouts : List RawLayout) (closed : RawMethod) (parameters : RawArguments)
    (reachable : List Bool) (uses : List LayoutUse) :
    Decidable (LayoutUsesComplete layouts closed parameters reachable uses) :=
  inferInstanceAs (Decidable (_ = _))

theorem layout_uses_complete {layouts closed parameters reachable uses}
    (valid : LayoutUsesComplete layouts closed parameters reachable uses) :
    expectedLayoutUses layouts closed parameters reachable = some uses := valid

end CIL.Extraction
