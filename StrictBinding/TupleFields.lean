import StrictBinding.PlatformType
import CIL.Extraction.Translation

/-! Verify the declared instance-field order of the platform pair used by a canonical extraction. -/

namespace StrictBinding

open CIL CIL.Extraction

/-- The base of the public pair is System.ValueType in a core assembly. -/
private def pairBase (image : PreparedImage) (row : Nat) : Except AuditError Bool := do
  let base ← image.layout.cellOfRow image.view Table.typeDef row typeDefExtendsColumn
  let table := if base % 4 == 0 then Table.typeDef else Table.typeRef
  if base % 4 > 1 || base / 4 == 0 then return false
  let token ← checkedTokenOf table (base / 4) .rowOverflow
  let cell := image.layout.cell image.view token
  unless ← stringFound image (← cell typeNameColumn) (valueTypeName ++ [0]) do return false
  unless ← stringFound image (← cell typeNamespaceColumn) (systemNamespace ++ [0]) do return false
  return (← kindOf image 0 systemNamespace valueTuplePairName
    (.named token systemNamespace valueTypeName)) == .valueType

/-- Every GenericParam owned by this TypeDef has its expected ordinal. Both slots must exist. -/
private def pairParameters (image : PreparedImage) (row : Nat) : Except AuditError Bool := do
  let cell := image.layout.cellOfRow image.view Table.genericParam
  let mut count := 0
  for i in [:image.layout.rowCount Table.genericParam] do
    if (← cell (i + 1) 2) == 2 * row then
      if (← cell (i + 1) 0) != count then return false
      count := count + 1
  return count == 2

/-- The two instance fields in declaration order are Item1 of VAR 0 and Item2 of VAR 1.
    Static fields do not occupy an instance slot. -/
private def pairFields (image : PreparedImage) (row : Nat) : Except AuditError Unit := do
  unless ← pairBase image row do throw (.invalidTupleDefinition image.identity)
  unless ← pairParameters image row do throw (.invalidTupleDefinition image.identity)
  let (first, finish) ← platformFieldRange image row
  let mut slot := 0
  for field in [first:finish] do
    let cell := image.layout.cellOfRow image.view Table.field field
    if (← cell 0) &&& 0x10 != 0 then continue
    let name := if slot == 0 then firstItemName else secondItemName
    if slot ≥ 2 || !(← stringFound image (← cell 1) (name ++ [0])) ||
        (← image.layout.blobAt image.view (← cell 2)) != [0x06, 0x13, slot] then
      throw (.invalidTupleField image.identity field)
    slot := slot + 1
  if slot != 2 then throw (.invalidTupleDefinition image.identity)

/-- A retained TypeRef names the pair in exactly the System.Runtime identity admitted for it. -/
private def pairRef (index : MetadataIndex) (token : Nat) : Except MetadataError Bool := do
  if metadataTableOf token != Table.typeRef then return false
  let row ← index.typeRef token
  if metadataTableOf row.scope != Table.assemblyRef then return false
  if (← index.string row.namespace_) != systemNamespace ||
      (← index.string row.name) != valueTuplePairName then return false
  return (← index.assemblyRefName row.scope runtimeAssembly) == some runtimeAssembly &&
    (← index.assemblyRefIdentity row.scope) == runtimeScopeBytes

/-- Bind the defining or forwarded pair to both the selected layout and its scoped TypeRef. -/
def checkTupleFields (images : List PinnedImage) (evidence : List MethodEvidence)
    (layouts : List RawLayout) : Except AuditError Bool := do
  unless layouts.any (·.identity.startsWith (runtimeScope ++ "::System.ValueTuple`2<")) do
    return false
  let mut used := false
  for item in evidence do
    for slice in item.body.metadata.slices do
      let .ok index := slice.index | throw (.invalidTupleDefinition slice.assembly.identity)
      for (token, _) in slice.rows do
        let .ok matchesPair := pairRef index token
          | throw (.invalidTupleDefinition slice.assembly.identity)
        if matchesPair then used := true; break
      if used then break
    if used then break
  unless used do return false
  let prepared ← prepare images
  resolvePlatformType prepared "ValueTuple`2" .invalidTupleDefinition pairFields runtimeScope
    (prepared.length + 1)

/-- The selected pair's defining image declares both instance fields in the expected order. -/
def TupleFieldsBound (images : List PinnedImage) (evidence : List MethodEvidence)
    (layouts : List RawLayout) : Prop :=
  (checkTupleFields images evidence layouts).toOption = some true

instance (images : List PinnedImage) (evidence : List MethodEvidence) (layouts : List RawLayout) :
    Decidable (TupleFieldsBound images evidence layouts) := inferInstanceAs (Decidable (_ = _))

/-- Any supplied part of the selected forwarding chain agrees with the extraction. -/
def SuppliedTupleFieldsValid (images : List PinnedImage) (evidence : List MethodEvidence)
    (layouts : List RawLayout) : Prop :=
  ok (checkTupleFields images evidence layouts) = true

instance (images : List PinnedImage) (evidence : List MethodEvidence) (layouts : List RawLayout) :
    Decidable (SuppliedTupleFieldsValid images evidence layouts) :=
  inferInstanceAs (Decidable (_ = true))

end StrictBinding
