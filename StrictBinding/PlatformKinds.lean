import StrictBinding.DefinitionRoute
import CIL.Extraction.Translation

/-! Check the TypeDef and GenericParam rows of an externally referenced type. -/

namespace StrictBinding

open CIL.Extraction

/-- The ordinal of a GenericParam owned by a TypeDef is its position among that owner's rows. -/
def physicalTypeArity (image : PreparedImage) (row : Nat) : Except AuditError Nat := do
  let cell := image.layout.cellOfRow image.view Table.genericParam
  let mut count := 0
  for i in [:image.layout.rowCount Table.genericParam] do
    if (← cell (i + 1) 2) == 2 * row then
      unless (← cell (i + 1) 0) == count do throw (.typeDefMismatch row .kind)
      count := count + 1
  return count

/-- Decode the physical Extends column, including the tag when the base is a generic instance. -/
private def physicalBase (image : PreparedImage) (row : Nat) : Except AuditError BaseType := do
  let value ← image.layout.cellOfRow image.view Table.typeDef row typeDefExtendsColumn
  if value == 0 then return .none
  unless value / 4 != 0 do throw (.typeDefMismatch row .base)
  let table ← match value % 4 with
    | 0 => pure Table.typeDef
    | 1 => pure Table.typeRef
    | 2 => pure Table.typeSpec
    | _ => throw (.typeDefMismatch row .base)
  let token ← checkedTokenOf table (value / 4) .rowOverflow
  let _ ← image.layout.rowAt token
  if table == Table.typeSpec then return .spec token
  let cell := image.layout.cell image.view token
  let space ← image.layout.stringAt image.view (← cell typeNamespaceColumn)
  let name ← image.layout.stringAt image.view (← cell typeNameColumn)
  return .named token space name

/-- Read the declaration's CLI kind and generic arity at a resolved TypeDef row. -/
def physicalTypeShape (image : PreparedImage) (row : Nat) : Except AuditError (TypeKind × Nat) := do
  let cell := image.layout.cellOfRow image.view Table.typeDef row
  let flags ← cell typeDefFlagsColumn
  let space ← image.layout.stringAt image.view (← cell typeNamespaceColumn)
  let name ← image.layout.stringAt image.view (← cell typeNameColumn)
  let base ← physicalBase image row
  let kind ← kindOf image flags space name base
  if kind == .interface && base != .none then throw (.typeDefMismatch row .base)
  if kind == .enum || kind == .valueType then
    if let .named token baseSpace baseName := base then
      if tableOf token == Table.typeDef then
        unless (← enumDefinition? image 0 [baseSpace, baseName]) == some (token % 2^24) do
          throw (.typeDefMismatch row .base)
  return (kind, ← physicalTypeArity image row)

/-- A distinguished root's base is the top-level type in a recognized core assembly. -/
private def coreBaseNamed (image : PreparedImage) (row : Nat) (expected : List Nat) :
    Except AuditError Bool := do
  let .named token space name ← physicalBase image row | return false
  unless space == systemNamespace && name == expected do return false
  if tableOf token == Table.typeDef then
    return (← platformAssembly image) &&
      (← enumDefinition? image 0 [space, name]) == some (token % 2^24)
  let scope ← image.layout.cell image.view token 0
  unless scope % 4 == 2 do return false
  let reference ← checkedTokenOf Table.assemblyRef (scope / 4) .rowOverflow
  coreAssemblyAt image reference 0

/-- The physical declaration determines its ordinary kind and arity. The five distinguished
    System types also require their exact top-level names, publisher and base. -/
def physicalPlatformKind (image : PreparedImage) (row : Nat) (parts : List (List Nat)) :
    Except AuditError PlatformKind := do
  let (kind, arity) ← physicalTypeShape image row
  if let [space, name] := parts then
    if space == systemNamespace && (← platformAssembly image) then
      let special := if name == asciiOf "Object" then some PlatformKind.objectRoot
        else if name == valueTypeName then some .valueTypeRoot
        else if name == enumName then some .enumRoot
        else if name == valueTuplePairName then some .valuePair
        else if name == asciiOf "BitConverter" then some .byteOrder
        else none
      if let some role := special then
        unless arity == role.arity do throw (.typeDefMismatch row .kind)
        let valid ← match role with
          | .objectRoot => pure (kind == .classType && (← physicalBase image row) == .none)
          | .valuePair => pure (kind == .valueType && (← coreBaseNamed image row valueTypeName))
          | .enumRoot => pure (kind == .classType && (← coreBaseNamed image row valueTypeName))
          | _ => pure (kind == .classType && (← coreBaseNamed image row (asciiOf "Object")))
        unless valid do throw (.typeDefMismatch row .base)
        return role
  match kind with
  | .classType => return if arity == 0 then .classType else .genericClass arity
  | .interface => return if arity == 0 then .interfaceType else .genericInterface arity
  | .valueType => return if arity == 0 then .valueType else .genericValue arity
  | .enum => return .enumType (← physicalEnumStorage image row) arity

/-- A missing definition or forwarder image leaves the entry uncovered. A wrong kind in
    a supplied image fails verification. -/
def coveredPlatformKind (images : List PreparedImage) (entry : PlatformDefinition) :
    Except AuditError Bool := do
  let some (image, row) ← findPinnedDefinition images entry.parts entry.scope (images.length + 1)
    | return false
  unless (← physicalPlatformKind image row entry.parts) == entry.kind do
    throw (.typeDefMismatch row .kind)
  return true

/-- Bind the table to each method's checked environment and read every externally declared kind.
    Even a partial audit checks all definitions for which the images were supplied. -/
def checkPlatformKinds (images : List PinnedImage) (platform : PlatformTable)
    (methods : List MethodEvidence) : Except AuditError Bool := do
  let _ ← methods.mapM fun item => do
    let .ok env := item.body.environment | throw (.rowMismatch item.original.token)
    unless env.platform == platform do throw (.rowMismatch item.original.token)
    pure ()
  let prepared ← prepare images
  let entries := platform.definitions
  let covered ← entries.mapM (coveredPlatformKind prepared)
  return !methods.isEmpty && !entries.isEmpty && covered.all id

/-- The completeness bit describes the exact pinned images and platform declarations used by
    these method bodies. -/
def PlatformKindsChecked (images : List PinnedImage) (platform : PlatformTable)
    (methods : List MethodEvidence) (complete : Bool) : Prop :=
  (checkPlatformKinds images platform methods).toOption = some complete

instance (images : List PinnedImage) (platform : PlatformTable) (methods : List MethodEvidence)
    (complete : Bool) : Decidable (PlatformKindsChecked images platform methods complete) :=
  inferInstanceAs (Decidable (_ = _))

/-- The definition used for a fully covered entry has the declared kind in its pinned image. -/
theorem coveredPlatformKind_physical {images : List PreparedImage} {entry : PlatformDefinition}
    (covered : coveredPlatformKind images entry = .ok true) :
    ∃ image row, PinnedDefinitionAt images entry.parts entry.scope image row ∧
      physicalPlatformKind image row entry.parts = .ok entry.kind := by
  simp only [coveredPlatformKind, bind, Except.bind] at covered
  cases selected : findPinnedDefinition images entry.parts entry.scope (images.length + 1) with
  | error fault => simp [selected] at covered
  | ok result =>
    cases result with
    | none => simp [selected, pure, Except.pure] at covered
    | some pair =>
      obtain ⟨image, row⟩ := pair
      cases read : physicalPlatformKind image row entry.parts with
      | error fault => simp [selected, read] at covered
      | ok actual =>
        simp [selected, read] at covered
        split at covered <;> try contradiction
        rename_i same
        exact ⟨image, row, pinnedDefinitionAt_of_find selected, same ▸ read⟩
#print axioms coveredPlatformKind_physical

/-- In every certified method, each declaration selected from the platform table has its
    claimed kind at the physical TypeDef row found through the supplied images. -/
theorem PlatformKindsChecked.physical {images : List PinnedImage} {platform : PlatformTable}
    {methods : List MethodEvidence} {item : MethodEvidence} {env : MetadataEnv}
    (checked : PlatformKindsChecked images platform methods true) (method : item ∈ methods)
    (environment : item.body.environment = .ok env) {entry : PlatformDefinition}
    (member : entry ∈ env.platform.definitions) :
    ∃ prepared image row, prepare images = .ok prepared ∧
      PinnedDefinitionAt prepared entry.parts entry.scope image row ∧
      physicalPlatformKind image row entry.parts = .ok entry.kind := by
  have done : checkPlatformKinds images platform methods = .ok true := by
    cases result : checkPlatformKinds images platform methods with
    | error err => simp [PlatformKindsChecked, result, Except.toOption] at checked
    | ok value =>
      have yes : value = true := by simpa [PlatformKindsChecked, result, Except.toOption] using checked
      rw [yes]
  unfold checkPlatformKinds at done
  obtain ⟨checks, usingPlatform, done⟩ := CIL.Safety.except_bind_ok done
  obtain ⟨prepared, built, done⟩ := CIL.Safety.except_bind_ok done
  obtain ⟨covered, entries, done⟩ := CIL.Safety.except_bind_ok done
  have all := Except.ok.inj done
  simp only [Bool.and_eq_true] at all
  obtain ⟨_, _, validated⟩ := read_member method usingPlatform
  have same : env.platform = platform := by
    by_cases same : env.platform = platform
    · exact same
    · simp [environment, same, bind, Except.bind, throw] at validated
  obtain ⟨result, found, read⟩ := read_member (same ▸ member) entries
  have yes : result = true := List.all_eq_true.mp all.2 result found
  obtain ⟨image, row, route, kind⟩ := coveredPlatformKind_physical (yes ▸ read)
  exact ⟨prepared, image, row, built, route, kind⟩
#print axioms PlatformKindsChecked.physical

end StrictBinding
