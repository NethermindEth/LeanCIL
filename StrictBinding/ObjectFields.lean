import StrictBinding.TypeDefs
import CIL.Extraction.Translation

/-!
# Instance fields of System.Object

Read the full identity of each platform scope from the certified method evidence. In each
corresponding image, find the root class by name and check the flags of every field it owns.
-/

namespace StrictBinding

open CIL.Extraction

/-- The unique top-level System.Object in the image is a public, baseless class and each
    physical Field row it owns has the Static flag (ECMA-335 II.23.1.5). -/
private def objectDefinition (image : PreparedImage) : Except AuditError (Option Nat) := do
  let cell := image.layout.cellOfRow image.view Table.typeDef
  let mut found := none
  for i in [:image.layout.rowCount Table.typeDef] do
    let row := i + 1
    unless ← stringFound image (← cell row typeNameColumn) (asciiOf "Object" ++ [0]) do continue
    unless ← stringFound image (← cell row typeNamespaceColumn) (systemNamespace ++ [0]) do continue
    let flags ← cell row typeDefFlagsColumn
    if visibilityOf flags ≥ nestedVisibility then continue
    if found.isSome || visibilityOf flags != 1 || flags &&& interfaceFlag != 0 ||
        (← cell row typeDefExtendsColumn) != 0 then throw (.invalidObjectDefinition image.identity)
    found := some row
  let some row := found | return none
  for i in [:nestedCount image] do
    if (← nestedTypeOf image (i + 1)) == row then throw (.invalidObjectDefinition image.identity)
  let first ← cell row typeDefFieldListColumn
  let finish ← fieldsEnd image row
  unless 1 ≤ first && first ≤ finish && finish ≤ image.layout.rowCount Table.field + 1 do
    throw (.typeDefMismatch row .fields)
  for field in [first:finish] do
    let flags ← image.layout.cellOfRow image.view Table.field field 0
    if flags &&& 0x10 == 0 then throw (.objectInstanceField image.identity field)

  return some row

/-- ECMA-335 II.22.14. A top-level forwarded System.Object has an ExportedType row with a
    Forwarder flag and an Implementation pointing to the destination AssemblyRef. -/
private def objectForwarder (image : PreparedImage) : Except AuditError (Option String) := do
  let exportedType := 0x27
  let cell := image.layout.cellOfRow image.view exportedType
  let mut target := none
  for i in [:image.layout.rowCount exportedType] do
    let row := i + 1
    unless ← stringFound image (← cell row 2) (asciiOf "Object" ++ [0]) do continue
    unless ← stringFound image (← cell row 3) (systemNamespace ++ [0]) do continue
    let implementation ← cell row 4
    if implementation % 4 == 2 then continue  -- A nested export names its enclosing export.
    if target.isSome || implementation % 4 != 1 || implementation / 4 == 0 ||
        (← cell row 0) &&& 0x00200000 == 0 then throw (.invalidObjectDefinition image.identity)
    let token ← CIL.Extraction.checkedTokenOf Table.assemblyRef (implementation / 4) .rowOverflow
    unless ← coreAssemblyAt image token 0 do throw (.invalidObjectDefinition image.identity)
    let identity ← assemblyIdentityAt image.view image.layout token 0
    target := some (String.ofList (identity.map Char.ofNat))
  return target

/-- The platform Assembly row carries a full public key that hashes to the recognized token. -/
private def platformAssembly (image : PreparedImage) : Except AuditError Bool := do
  let row := tokenOf 0x20 1
  let flags ← image.layout.cell image.view row 5
  return flags &&& 1 != 0 && (← coreAssemblyAt image row 1)

/-- Follow at most one forwarder per supplied image. A cycle or a definition competing with
    an export cannot identify the platform root class. -/
private def resolveObject (images : List PreparedImage) (identity : String) :
    Nat → Except AuditError Bool
  | 0 => throw (.invalidObjectDefinition identity)
  | fuel + 1 => do
    let some image := images.find? (·.identity == identity) | return false
    unless ← platformAssembly image do throw (.invalidObjectScope identity)
    match ← objectDefinition image, ← objectForwarder image with
    | some _, none => pure true
    | none, some next => resolveObject images next fuel
    | _, _ => throw (.invalidObjectDefinition identity)

/-- The exact identities of the core scopes retained in one slice, including its primitive
    type scope. The identity includes version, culture and publisher. -/
private def objectScopes (slice : MetadataSlice) (ownCore : Bool) :
    Except MetadataError (List (List Nat)) := do
  let index ← slice.index
  let identity ← match ← index.corlibIdentity with
    | some name => pure name
    | none => if ownCore then pure (asciiOf slice.assembly.identity)
              else throw (.unsupportedAssemblyRef 0)
  let mut scopes := [identity]
  for (token, _) in slice.rows do
    if CIL.Extraction.metadataTableOf token == Table.assemblyRef then
      if ← index.coreAssemblyRef token then
        let scope ← index.assemblyRefIdentity token
        unless scopes.contains scope do scopes := scope :: scopes
  return scopes

/-- Every core scope used in every method's metadata has a pinned defining image. -/
def checkObjectFields (images : List PinnedImage) (evidence : List MethodEvidence) :
    Except AuditError Bool := do
  let prepared ← prepare images
  let mut scopes : Std.TreeSet (List Nat) := {}
  for item in evidence do
    for slice in item.body.metadata.slices do
      let ownCore ←
        if slice.corlib != 0 then pure false
        else do
          let source ← located prepared slice.assembly.identity
          platformAssembly source
      let .ok names := objectScopes slice ownCore
        | throw (.invalidObjectScope slice.assembly.identity)
      for name in names do scopes := scopes.insert name
  if scopes.isEmpty then throw (.invalidObjectScope "")
  let mut complete := true
  for name in scopes do
    let identity := String.ofList (name.map Char.ofNat)
    let covered ← resolveObject prepared identity (prepared.length + 1)
    complete := complete && covered
  return complete

/-- Every platform root class selected by the certified methods declares no instance fields. -/
def ObjectFieldsBound (images : List PinnedImage) (evidence : List MethodEvidence) : Prop :=
  (checkObjectFields images evidence).toOption = some true

instance (images : List PinnedImage) (evidence : List MethodEvidence) :
    Decidable (ObjectFieldsBound images evidence) := inferInstanceAs (Decidable (_ = some true))

/-- Every supplied image reachable through a core scope or its forwarders agrees with the
    extraction about System.Object. Some destination images may be absent. -/
def SuppliedObjectFieldsValid (images : List PinnedImage) (evidence : List MethodEvidence) : Prop :=
  ok (checkObjectFields images evidence) = true

instance (images : List PinnedImage) (evidence : List MethodEvidence) :
    Decidable (SuppliedObjectFieldsValid images evidence) := inferInstanceAs (Decidable (_ = true))

end StrictBinding
