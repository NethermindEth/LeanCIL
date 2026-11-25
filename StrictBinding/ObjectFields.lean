import StrictBinding.PlatformType
import CIL.Extraction.Translation

/-!
# Instance fields of System.Object

Read the full identity of each platform scope from the certified method evidence. In each
corresponding image, find the root class by name and check the flags of every field it owns.
-/

namespace StrictBinding

open CIL.Extraction

/-- System.Object has no base type, and all its physically declared fields are static. -/
private def objectFields (image : PreparedImage) (row : Nat) : Except AuditError Unit := do
  let base ← image.layout.cellOfRow image.view Table.typeDef row typeDefExtendsColumn
  if base != 0 then throw (.invalidObjectDefinition image.identity)
  let (first, finish) ← platformFieldRange image row
  for field in [first:finish] do
    let flags ← image.layout.cellOfRow image.view Table.field field 0
    if flags &&& 0x10 == 0 then throw (.objectInstanceField image.identity field)

/-- The exact identities of the core scopes retained in one slice, including its primitive
    type scope. The identity includes version, culture and publisher. -/
private def objectScopes (slice : MetadataSlice) (ownCore : Bool) :
    Except MetadataError (List CIL.AssemblyName) := do
  let index ← slice.index
  let identity ← match ← index.corlibIdentity with
    | some name => pure name
    | none => if ownCore then slice.assembly.name
              else throw (.unsupportedAssemblyRef 0)
  let mut scopes := [identity]
  for (token, _) in slice.rows do
    if CIL.Extraction.metadataTableOf token == Table.assemblyRef then
      if ← index.coreAssemblyRef token then
        let scope ← index.referenceName token
        unless scopes.contains scope do scopes := scope :: scopes
  return scopes

/-- Every core scope used in every method's metadata has a pinned defining image. -/
def checkObjectFields (images : List PinnedImage) (evidence : List MethodEvidence) :
    Except AuditError Bool := do
  let prepared ← prepare images
  let mut scopes : Std.TreeSet CIL.AssemblyName := {}
  for item in evidence do
    for slice in item.body.metadata.slices do
      let ownCore ←
        if slice.corlib != 0 then pure false
        else do
          let source ← locatedBlock prepared slice.assembly
          platformAssembly source
      let .ok names := objectScopes slice ownCore
        | throw (.invalidObjectScope (blockDisplay slice.assembly))
      for name in names do scopes := scopes.insert name
  if scopes.isEmpty then throw (.invalidObjectScope "")
  let mut complete := true
  for identity in scopes do
    let covered ← resolvePlatformType prepared "Object" .invalidObjectDefinition objectFields
      identity (prepared.length + 1)
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
