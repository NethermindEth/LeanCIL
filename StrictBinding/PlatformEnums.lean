import StrictBinding.PlatformType
import CIL.Extraction.PlatformDefinitions

/-! Read an enum's exact integer storage from the Field rows owned by its pinned TypeDef. -/

namespace StrictBinding

open CIL.Extraction

/-- The one non-static field must be the runtime special field named value__.
    Its entire field signature must consist of the FIELD tag and an integer element type. -/
def physicalEnumStorage (image : PreparedImage) (row : Nat) : Except AuditError Nat := do
  let (first, finish) ← platformFieldRange image row
  let mut result := none
  for field in [first:finish] do
    let cell := image.layout.cellOfRow image.view Table.field field
    let flags ← cell 0
    if flags &&& 0x10 != 0 then continue
    if result.isSome || flags &&& 0x600 != 0x600 ||
        !(← stringFound image (← cell 1) (asciiOf "value__" ++ [0])) then
      throw (.typeDefMismatch row .fields)
    let [0x06, code] ← image.layout.blobAt image.view (← cell 2)
      | throw (.typeDefMismatch row .fields)
    unless 0x04 ≤ code && code ≤ 0x0b do throw (.typeDefMismatch row .fields)
    result := some code
  let some code := result | throw (.typeDefMismatch row .fields)
  return code

/-- The enclosing TypeDef row, or zero for a top-level declaration. -/
private def enumParent (image : PreparedImage) (row flags : Nat) : Except AuditError Nat := do
  let mut parent := 0
  for i in [:nestedCount image] do
    if (← nestedTypeOf image (i + 1)) == row then
      let enclosing ← enclosingOf image (i + 1)
      unless parent == 0 && 0 < enclosing && enclosing < row do
        throw (.typeDefMismatch row .nesting)
      parent := enclosing
  unless (visibilityOf flags < nestedVisibility) == (parent == 0) do
    throw (.typeDefMismatch row .nesting)
  return parent

/-- Find a unique type at this level, retaining namespace and simple name as separate bytes. -/
private def enumChild? (image : PreparedImage) (parent : Nat) (space name : List Nat) :
    Except AuditError (Option Nat) := do
  if name.isEmpty || name.contains 0 || space.contains 0 then throw (.typeDefMismatch parent .typeName)
  let cell := image.layout.cellOfRow image.view Table.typeDef
  let mut found := none
  for i in [:image.layout.rowCount Table.typeDef] do
    let row := i + 1
    unless ← stringFound image (← cell row typeNameColumn) (name ++ [0]) do continue
    unless ← stringFound image (← cell row typeNamespaceColumn) (space ++ [0]) do continue
    unless (← enumParent image row (← cell row typeDefFlagsColumn)) == parent do continue
    if found.isSome then throw (.typeDefMismatch row .typeName)
    found := some row
  return found

/-- Locate each namespace/name pair from the outermost definition to the innermost. -/
def enumDefinition? (image : PreparedImage) (parent : Nat) :
    List (List Nat) → Except AuditError (Option Nat)
  | space :: name :: rest => do
    let some row ← enumChild? image parent space name | return none
    if rest.isEmpty then return some row
    enumDefinition? image row rest
  | _ => .error (.typeDefMismatch parent .typeName)

/-- The resolved row is a non-interface with a direct base in the recognized core assembly. -/
def physicalEnumCode (image : PreparedImage) (row : Nat) : Except AuditError Nat := do
  let cell := image.layout.cellOfRow image.view Table.typeDef row
  let flags ← cell typeDefFlagsColumn
  let baseValue ← cell typeDefExtendsColumn
  let table ← match baseValue % 4 with
    | 0 => pure Table.typeDef
    | 1 => pure Table.typeRef
    | _ => throw (.typeDefMismatch row .base)
  let base ← checkedTokenOf table (baseValue / 4) .rowOverflow
  let claim := BaseType.named base systemNamespace enumName
  baseBound image row baseValue claim
  if table == Table.typeDef then
    let baseFlags ← image.layout.cell image.view base typeDefFlagsColumn
    unless (← enumParent image (baseValue / 4) baseFlags) == 0 do throw (.typeDefMismatch row .base)
  unless (← kindOf image flags [] [] claim) == .enum do throw (.typeDefMismatch row .kind)
  physicalEnumStorage image row

/-- Check an enum in the supplied defining image against the entry the method decoder can use. -/
def directEnumBound (image : PreparedImage) (entry : PlatformDefinition) : Except AuditError Unit := do
  unless bytesOf image.identity == entry.scope do throw (.typeDefMismatch 0 .typeName)
  let .enumType code _ := entry.kind | throw (.typeDefMismatch 0 .kind)
  let some row ← enumDefinition? image 0 entry.parts | throw (.typeDefMismatch 0 .typeName)
  unless (← physicalEnumCode image row) == code do throw (.typeDefMismatch row .fields)

/-- A checked entry identifies the physical row and its declared storage code in this image. -/
theorem directEnumBound_row {image : PreparedImage} {entry : PlatformDefinition} {code arity : Nat}
    (kind : entry.kind = .enumType code arity) (checked : directEnumBound image entry = .ok ()) :
    bytesOf image.identity = entry.scope ∧ ∃ row, enumDefinition? image 0 entry.parts = .ok (some row) ∧
      physicalEnumCode image row = .ok code := by
  unfold directEnumBound at checked
  simp only [kind, bind, Except.bind] at checked
  split at checked <;> try contradiction
  rename_i scope
  cases found : enumDefinition? image 0 entry.parts with
  | error error => simp [found] at checked
  | ok result =>
    cases result with
    | none => simp [found] at checked
    | some row =>
      cases read : physicalEnumCode image row with
      | error error => simp [found, read] at checked
      | ok actual =>
        simp [found, read] at checked
        split at checked
        · rename_i same
          exact ⟨by simpa using scope, row, rfl, same ▸ read⟩
        · contradiction
#print axioms directEnumBound_row

end StrictBinding
