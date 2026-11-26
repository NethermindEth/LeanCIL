import StrictBinding.Bind
import StrictBinding.Reads
import CIL.Extraction.Translation
import CIL.Extraction.StaticIdentities

/-!
# Static data in a PE image

The FieldRVA table associates a Field row with an RVA. Build its index once per image, then
check the Field flags, the table row, the mapped range and the bytes for each access.
-/

namespace StrictBinding

/-- ECMA-335 II.22.18, FieldRVA. Its columns are the RVA and the Field index. -/
def fieldRvaTable : Nat := 0x1d

/-- Index the physical rows of a table by the full token of the Field or TypeDef each row
    names. Reject duplicate keys independently of the table header's sorted bit. -/
def dataTableIndex (image : PreparedImage) (table column target : Nat) :
    Except AuditError (Std.TreeMap Nat Nat) := do
  let mut rows : Std.TreeMap Nat Nat := {}
  let count := image.layout.rowCount target
  for i in [:image.layout.rowCount table] do
    let row := i + 1
    let key ← image.layout.cellOfRow image.view table row column
    let token := tokenOf target key
    if key == 0 || key > count || rows.contains token then
      throw (.invalidDataTableKey table row key)
    rows := rows.insert token row
  return rows

/-- The FieldRVA row of each Field that has one. -/
def fieldRvaIndex (image : PreparedImage) : Except AuditError (Std.TreeMap Nat Nat) :=
  dataTableIndex image fieldRvaTable 1 CIL.Extraction.Table.field

/-- The bytes attached to a field are found through its physical FieldRVA row. -/
def fieldDataAt (image : PreparedImage) (field row alignment : Nat) (bytes : List Nat) :
    Except AuditError Unit := do
  let flags ← image.layout.cell image.view field 0
  let index ← image.layout.cellOfRow image.view fieldRvaTable row 1
  let rva ← image.layout.cellOfRow image.view fieldRvaTable row 0
  if field != tokenOf CIL.Extraction.Table.field index || flags &&& 0x110 != 0x110 ||
      rva == 0 || bytes.isEmpty || !(alignment ∈ [1, 2, 4, 8]) || rva % alignment != 0 then
    throw (.invalidFieldData field)
  let offset ← mapRva image.layout.pe.sections rva bytes.length
  if offset % alignment != 0 then throw (.invalidFieldData field)
  unless ← image.view.hasBytesAt offset bytes do throw (.fieldDataMismatch field rva offset)

/-- A successful comparison places the claimed bytes in the image section at the RVA read
    from the FieldRVA row naming this field. -/
theorem bytes_of_fieldDataAt {image : PreparedImage} (bounded : image.view.Bounded)
    {field row alignment : Nat} {bytes : List Nat}
    (h : fieldDataAt image field row alignment bytes = .ok ()) :
    ∃ index rva offset,
      image.layout.cellOfRow image.view fieldRvaTable row 1 = .ok index ∧
      field = tokenOf CIL.Extraction.Table.field index ∧
      image.layout.cellOfRow image.view fieldRvaTable row 0 = .ok rva ∧
      mapRva image.layout.pe.sections rva bytes.length = .ok offset ∧
      image.view.bytes offset bytes.length = .ok bytes := by
  unfold fieldDataAt at h
  obtain ⟨flags, _, h⟩ := CIL.Safety.except_bind_ok h
  obtain ⟨index, fieldRead, h⟩ := CIL.Safety.except_bind_ok h
  obtain ⟨rva, rvaRead, h⟩ := CIL.Safety.except_bind_ok h
  split at h
  · contradiction
  next permitted =>
    obtain ⟨offset, mapped, h⟩ := CIL.Safety.except_bind_ok h
    split at h
    · contradiction
    obtain ⟨same, compared, h⟩ := CIL.Safety.except_bind_ok h
    cases same with
    | false => contradiction
    | true =>
      have named : field = tokenOf CIL.Extraction.Table.field index := by
        by_cases named : field = tokenOf CIL.Extraction.Table.field index
        · exact named
        · simp [named] at permitted
      exact ⟨index, rva, offset, fieldRead, named, rvaRead, mapped,
        bytes_of_hasBytesAt bounded compared⟩

#print axioms bytes_of_fieldDataAt

/-- Physical indices shared by all accesses to static data in one assembly. -/
private structure StaticTables where
  image : PreparedImage
  fields : Std.TreeMap Nat Nat
  layouts : Std.TreeMap Nat Nat

/-- ClassLayout stores packing, declared size and the owning TypeDef. -/
def classLayoutTable : Nat := 0x0f

private def StaticTables.read (image : PreparedImage) : Except AuditError StaticTables := do
  return ⟨image, ← fieldRvaIndex image,
    ← dataTableIndex image classLayoutTable 2 CIL.Extraction.Table.typeDef⟩

/-- The admitted RVA field has an explicit-layout local value type. Its field signature
    identifies the TypeDef whose ClassLayout row supplies its packing and full byte count. -/
private def StaticTables.site (tables : StaticTables) (token : Nat)
    (site : CIL.Extraction.StaticFieldSite) : Except AuditError Unit := do
  let image := tables.image
  let cell := image.layout.cell image.view
  if CIL.Extraction.metadataTableOf token != CIL.Extraction.Table.field then
    throw (.invalidFieldData token)
  let flags ← cell token 0
  match site.rvaSize, tables.fields[token]? with
  | none, none =>
    unless flags &&& 0x110 == 0x10 do throw (.invalidFieldData token)
  | some size, some row =>
    let signature ← image.layout.blobAt image.view (← cell token 2)
    let .ok (.named true owner) := CIL.Extraction.decodeFieldSig signature
      | throw (.invalidFieldData token)
    let some layout := tables.layouts[owner]? | throw (.invalidFieldData token)
    let layoutCell := image.layout.cellOfRow image.view classLayoutTable layout
    let alignment ← layoutCell 0
    unless flags &&& 0x130 == 0x130 && (← cell owner 0) &&& 0x18 == 0x10 &&
        alignment == site.descriptor.alignment && (← layoutCell 1) == size &&
        size == site.descriptor.bytes.length do throw (.invalidFieldData token)
    fieldDataAt image token row alignment (site.descriptor.bytes.map BitVec.toNat)
  | _, _ => throw (.invalidFieldData token)

/-- Check every claimed static field at its decoded operand. The two physical tables of an
    assembly are indexed on its first static access. Constructor-initialized fields must have
    no FieldRVA. For image-backed fields the full data, size and alignment must agree. -/
def checkStaticData (images : List PinnedImage) (evidence : List CIL.Extraction.MethodEvidence) :
    Except AuditError Unit := do
  let prepared ← prepare images
  let mut indexed : Std.TreeMap CIL.AssemblyName StaticTables := {}
  for item in evidence do
    let sites := item.closed.staticFields
    let pcs := sites.map Prod.fst
    let some tokens := CIL.Extraction.siteTokens item.body.statics pcs
      | throw (.staticSiteMismatch item.original.token)
    for ((pc, site), token) in sites.zip tokens do
      let some (position, field) := item.body.staticFieldRow token
        | throw (.unresolvedStaticField item.original.token pc)
      let some slice := item.body.metadata.slices[position]?
        | throw (.unresolvedStaticField item.original.token pc)
      let .ok name := slice.assembly.name | throw .unnamedAssembly
      let tables ← match indexed[name]? with
        | some found => pure found
        | none => do StaticTables.read (← located prepared name)
      indexed := indexed.insert name tables
      tables.site field site

/-- All RVA static bytes used by the certified extraction occupy the whole field at the
    address and alignment recorded in the pinned image. -/
def StaticDataBound (images : List PinnedImage) (evidence : List CIL.Extraction.MethodEvidence) :
    Prop := ok (checkStaticData images evidence) = true

instance (images : List PinnedImage) (evidence : List CIL.Extraction.MethodEvidence) :
    Decidable (StaticDataBound images evidence) :=
  inferInstanceAs (Decidable (_ = true))

end StrictBinding
