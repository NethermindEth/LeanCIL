import CIL.Extraction.Generics

namespace CIL.Extraction

private def aggregateIndex : TypeExpr → Option Nat
  | .aggregate _ index => some index
  | _ => none

/-- Derive required instruction sites from the complete raw body, independently
    of the extractor's optional list of layout uses. -/
def instructionLayoutUses (layouts : List RawLayout) (pc : Nat)
    (instruction : RawInstruction) : Option (List LayoutUse) := do
  match instruction.opcode, instruction.operand with
  | 0x7b, .field owner index type false
  | 0x7c, .field owner index type false
  | 0x7d, .field owner index type false =>
    let .field (.aggregate parent) ← typeStorage layouts owner | none
    let metadata ← layouts[parent]?
    let field ← metadata.fields[index]?
    if typeStorage layouts type != some (.field field.type) then none else
      return [.field pc parent index (if instruction.opcode = 0x7b then .load
        else if instruction.opcode = 0x7c then .address else .store)]
  | opcode, .type type =>
    match aggregateIndex type with
    | none => return []
    | some index =>
      if opcode = 0x71 then return [.size pc index .load]
      else if opcode = 0x81 then return [.size pc index .store]
      else if opcode = 0xfe15 then return [.size pc index .initialize]
      else if opcode = 0x70 then return [.size pc index .copy]
      else if opcode = 0xfe1c then return [.size pc index .sizeOf]
      else return []
  | 0x73, .call site =>
    return (aggregateIndex site.declaringType).toList.map fun index => .size pc index .construct
  | 0x28, .call site =>
    match site.declaringType, site.typeArguments with
    | .atom _ "System.Runtime.CompilerServices.Unsafe", [.aggregate _ index] =>
      if site.name = "SizeOf" then return [.size pc index .sizeOf]
      else if site.name = "Add" then return [.size pc index .referenceAdd]
      else return []
    | _, _ => return []
  | _, _ => return []

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
