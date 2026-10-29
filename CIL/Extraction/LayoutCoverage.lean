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
  -- `ldfld`, `ldflda` and `stfld` on an instance field, whose declared type must match.
  | 0x7b, .field owner index type false
  | 0x7c, .field owner index type false
  | 0x7d, .field owner index type false =>
    let .field (.aggregate parent) ← typeStorage layouts owner | none
    let metadata ← layouts[parent]?
    let field ← metadata.fields[index]?
    let storage := match field.type with
      | .vector128 => StorageType.vector128
      | .vector256 => StorageType.vector256
      | kind => .field kind
    if typeStorage layouts type != some storage then none else
      return [.field pc parent index (if instruction.opcode = 0x7b then .load
        else if instruction.opcode = 0x7c then .address else .store)]
  -- `ldobj`, `stobj`, `initobj`, `cpobj` and `sizeof` of a struct.
  | opcode, .type type =>
    match aggregateIndex type with
    | none => return []
    | some index =>
      if opcode = 0x71 then return [.size pc index .load]
      else if opcode = 0x81 then return [.size pc index .store]
      else if opcode = 0xfe15 then return [.size pc index .initialize]
      else if opcode = 0x70 then return [.size pc index .copy]
      else if opcode = 0xfe1c then return [.size pc index .sizeOf]
      else if opcode ∈ [0x8f, 0xa3, 0xa4] then return [.size pc index .arrayElement]
      else return []
  -- `newobj` of a struct, then `Unsafe.SizeOf<T>` and `Unsafe.Add<T>`.
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
    if site.name ∈ ["AsBytes", "Cast"] &&
        site.declaringType == .atom runtimeScope "System.Runtime.InteropServices.MemoryMarshal" then
      return ((site.typeArguments[0]?).bind aggregateIndex).toList.map
        (fun index => .size pc index .spanSource) ++
        ((site.typeArguments[1]?).bind aggregateIndex).toList.map
        (fun index => .size pc index .spanTarget)
    match site.declaringType, site.typeArguments with
    | .apply (.constructor scope owner) (.aggregate _ index), [] =>
      if scope == runtimeScope && owner ∈ ["System.Span`1", "System.ReadOnlySpan`1"] &&
          site.name ∈ [".ctor", "op_Implicit"] &&
          (site.parameterTypes.head?.map fun type => match type with
            | .array _ => true | _ => false).getD false then
        return [.size pc index .arrayElement]
      else if scope == runtimeScope && owner ∈ ["System.Span`1", "System.ReadOnlySpan`1"] &&
          site.name ∈ ["get_Item", "CopyTo", "TryCopyTo", "Clear", "Fill", ".ctor"] then
        return [.size pc index .spanElement] else return []
    | .atom _ "System.MemoryExtensions", [.aggregate _ index] =>
      if site.name == "AsSpan" then return [.size pc index .arrayElement] else return []
    | .atom _ "System.Runtime.InteropServices.MemoryMarshal", [.aggregate _ index] =>
      if site.name = "Read" || site.name = "TryRead" then return [.size pc index .load]
      else if site.name = "Write" || site.name = "TryWrite" then return [.size pc index .store]
      else if site.name ∈ ["CreateSpan", "CreateReadOnlySpan"] then
        return [.size pc index .spanElement]
      else return []
    | .atom _ "System.Runtime.CompilerServices.Unsafe", [.aggregate _ index] =>
      if site.name = "SizeOf" then return [.size pc index .sizeOf]
      else if site.name = "Add" then return [.size pc index .referenceAdd]
      else if site.name = "Subtract" then return [.size pc index .referenceSubtract]
      else if site.name = "ReadUnaligned" then return [.size pc index .load]
      else if site.name = "WriteUnaligned" then return [.size pc index .store]
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
