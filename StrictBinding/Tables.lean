import StrictBinding.Pe

/-!
# Metadata tables

Decodes the `#~` stream header of an image and computes, from the image alone, where each row
of each table starts. A row's size depends on the row counts of other tables and on the heap
size flags (II.22 and II.24.2.6), so the schema of every table is spelled out here: a row's
position needs the size of all earlier tables. The heaps are read through the stream positions of
`StrictBinding.PeLayout`.
-/

namespace StrictBinding

/-- One column of a metadata table. -/
inductive Column where
  /-- An unsigned integer of this many bytes. -/
  | fixed (width : Nat)
  | string
  | guid
  | blob
  /-- A row index into one table. -/
  | index (table : Nat)
  /-- A tag of `bits` bits and a row index, into one of `tables` by tag. -/
  | coded (bits : Nat) (tables : List Nat)

namespace Column

/-- TypeDef, TypeRef or TypeSpec. -/
def typeDefOrRef : Column := .coded 2 [0x02, 0x01, 0x1B]

/-- Field, Param or Property. -/
def hasConstant : Column := .coded 2 [0x04, 0x08, 0x17]

/-- Every table that can carry a custom attribute. -/
def hasCustomAttribute : Column :=
  .coded 5 [0x06, 0x04, 0x01, 0x02, 0x08, 0x09, 0x0A, 0x00, 0x0E, 0x17, 0x14, 0x11, 0x1A, 0x1B,
    0x20, 0x23, 0x26, 0x27, 0x28, 0x2A, 0x2C, 0x2B]

/-- Field or Param. -/
def hasFieldMarshal : Column := .coded 1 [0x04, 0x08]

/-- TypeDef, MethodDef or Assembly. -/
def hasDeclSecurity : Column := .coded 2 [0x02, 0x06, 0x20]

/-- TypeDef, TypeRef, ModuleRef, MethodDef or TypeSpec. -/
def memberRefParent : Column := .coded 3 [0x02, 0x01, 0x1A, 0x06, 0x1B]

/-- Event or Property. -/
def hasSemantics : Column := .coded 1 [0x14, 0x17]

/-- MethodDef or MemberRef. -/
def methodDefOrRef : Column := .coded 1 [0x06, 0x0A]

/-- Field or MethodDef. -/
def memberForwarded : Column := .coded 1 [0x04, 0x06]

/-- File, AssemblyRef or ExportedType. -/
def implementation : Column := .coded 2 [0x26, 0x23, 0x27]

/-- MethodDef or MemberRef, with tags two and three. -/
def customAttributeType : Column := .coded 3 [0x06, 0x0A]

/-- Module, ModuleRef, AssemblyRef or TypeRef. -/
def resolutionScope : Column := .coded 2 [0x00, 0x1A, 0x23, 0x01]

/-- TypeDef or MethodDef. -/
def typeOrMethodDef : Column := .coded 1 [0x02, 0x06]

end Column

/-- The columns of table `table`, for every table the metadata format defines up to
    GenericParamConstraint (`0x2C`). -/
def schema : Nat → Option (List Column)
  -- Module, TypeRef, TypeDef, FieldPtr, Field, MethodPtr
  | 0x00 => some [.fixed 2, .string, .guid, .guid, .guid]
  | 0x01 => some [Column.resolutionScope, .string, .string]
  | 0x02 => some [.fixed 4, .string, .string, Column.typeDefOrRef, .index 0x04, .index 0x06]
  | 0x03 => some [.index 0x04]
  | 0x04 => some [.fixed 2, .string, .blob]
  | 0x05 => some [.index 0x06]
  -- MethodDef, ParamPtr, Param, InterfaceImpl, MemberRef, Constant
  | 0x06 => some [.fixed 4, .fixed 2, .fixed 2, .string, .blob, .index 0x08]
  | 0x07 => some [.index 0x08]
  | 0x08 => some [.fixed 2, .fixed 2, .string]
  | 0x09 => some [.index 0x02, Column.typeDefOrRef]
  | 0x0A => some [Column.memberRefParent, .string, .blob]
  | 0x0B => some [.fixed 2, Column.hasConstant, .blob]
  -- CustomAttribute, FieldMarshal, DeclSecurity, ClassLayout, FieldLayout, StandAloneSig
  | 0x0C => some [Column.hasCustomAttribute, Column.customAttributeType, .blob]
  | 0x0D => some [Column.hasFieldMarshal, .blob]
  | 0x0E => some [.fixed 2, Column.hasDeclSecurity, .blob]
  | 0x0F => some [.fixed 2, .fixed 4, .index 0x02]
  | 0x10 => some [.fixed 4, .index 0x04]
  | 0x11 => some [.blob]
  -- EventMap, EventPtr, Event, PropertyMap, PropertyPtr, Property
  | 0x12 => some [.index 0x02, .index 0x14]
  | 0x13 => some [.index 0x14]
  | 0x14 => some [.fixed 2, .string, Column.typeDefOrRef]
  | 0x15 => some [.index 0x02, .index 0x17]
  | 0x16 => some [.index 0x17]
  | 0x17 => some [.fixed 2, .string, .blob]
  -- MethodSemantics, MethodImpl, ModuleRef, TypeSpec, ImplMap, FieldRVA
  | 0x18 => some [.fixed 2, .index 0x06, Column.hasSemantics]
  | 0x19 => some [.index 0x02, Column.methodDefOrRef, Column.methodDefOrRef]
  | 0x1A => some [.string]
  | 0x1B => some [.blob]
  | 0x1C => some [.fixed 2, Column.memberForwarded, .string, .index 0x1A]
  | 0x1D => some [.fixed 4, .index 0x04]
  -- EncLog, EncMap, Assembly, AssemblyProcessor, AssemblyOS, AssemblyRef
  | 0x1E => some [.fixed 4, .fixed 4]
  | 0x1F => some [.fixed 4]
  | 0x20 =>
    some [.fixed 4, .fixed 2, .fixed 2, .fixed 2, .fixed 2, .fixed 4, .blob, .string, .string]
  | 0x21 => some [.fixed 4]
  | 0x22 => some [.fixed 4, .fixed 4, .fixed 4]
  | 0x23 =>
    some [.fixed 2, .fixed 2, .fixed 2, .fixed 2, .fixed 4, .blob, .string, .string, .blob]
  -- AssemblyRefProcessor, AssemblyRefOS, File, ExportedType, ManifestResource, NestedClass
  | 0x24 => some [.fixed 4, .index 0x23]
  | 0x25 => some [.fixed 4, .fixed 4, .fixed 4, .index 0x23]
  | 0x26 => some [.fixed 4, .string, .blob]
  | 0x27 => some [.fixed 4, .fixed 4, .string, .string, Column.implementation]
  | 0x28 => some [.fixed 4, .fixed 4, .string, Column.implementation]
  | 0x29 => some [.index 0x02, .index 0x02]
  -- GenericParam, MethodSpec, GenericParamConstraint
  | 0x2A => some [.fixed 2, .fixed 2, Column.typeOrMethodDef, .string]
  | 0x2B => some [Column.methodDefOrRef, .blob]
  | 0x2C => some [.index 0x2A, Column.typeDefOrRef]
  | _ => none

/-- One more than the last table the schema covers. -/
def tableLimit : Nat := 0x2D

/-- The bytes of an index or coded index into tables with at most `rows` rows when the index
    carries `bits` tag bits: two while the largest row number and tag fit in sixteen bits. -/
def indexWidth (bits rows : Nat) : Nat := if rows < 2 ^ (16 - bits) then 2 else 4

/-- The bytes of a column, given the heap size flags and the row count of each table. -/
def columnWidth (heapSizes : Nat) (rows : Nat → Nat) : Column → Nat
  | .fixed width => width
  | .string => if heapSizes % 2 == 1 then 4 else 2
  | .guid => if heapSizes / 2 % 2 == 1 then 4 else 2
  | .blob => if heapSizes / 4 % 2 == 1 then 4 else 2
  | .index table => indexWidth 0 (rows table)
  | .coded bits tables => indexWidth bits ((tables.map rows).foldl Nat.max 0)

/-- The bytes of a row of a table with these columns. -/
def rowSize (heapSizes : Nat) (rows : Nat → Nat) (columns : List Column) : Nat :=
  (columns.map (columnWidth heapSizes rows)).foldl Nat.add 0

/-- Where one table's rows are: the file offset of the first row, the bytes per row and the
    number of rows. -/
structure TableRows where
  table : Nat
  start : Nat
  size : Nat
  count : Nat

/-- The row count of `table` among `counts`, zero when the table is absent. -/
def countOf (counts : List (Nat × Nat)) (table : Nat) : Nat :=
  ((counts.find? (·.1 == table)).map (·.2)).getD 0

/-- The positions of every nonempty table, in table order, when the first row of the first one is
    at `start`. -/
def tablePositions (heapSizes : Nat) (counts : List (Nat × Nat)) (start : Nat) :
    List TableRows × Nat :=
  let step (found : List TableRows × Nat) (table : Nat) : List TableRows × Nat :=
    let count := countOf counts table
    match schema table with
    | some columns =>
      if count == 0 then found
      else
        let size := rowSize heapSizes (countOf counts) columns
        (found.1 ++ [{ table, start := found.2, size, count }], found.2 + count * size)
    | none => found
  (List.range tableLimit).foldl step ([], start)

/-- The tables of an image and where they are. -/
structure MetadataLayout where
  pe : PeLayout
  /-- The heap size flags of the `#~` header: bit 0 widens `#Strings` indexes, bit 1 `#GUID`
      and bit 2 `#Blob`. -/
  heapSizes : Nat
  tables : List TableRows

/-- The heap size flags the audit reads: wide `#Strings`, `#GUID` and `#Blob` indexes and the
    extra data flag. Any other bit is rejected. -/
def knownHeapFlags : Nat := 0x47

/-- The flag that adds four bytes after the row counts. -/
def extraDataFlag : Nat := 0x40

/-- The bytes before the row counts of a `#~` stream: reserved, versions, flags, `Valid` and
    `Sorted`. -/
def tableHeaderBytes : Nat := 24

/-- The pointer tables (FieldPtr, MethodPtr, ParamPtr, EventPtr, PropertyPtr) and the
    edit-and-continue tables (EncLog, EncMap), as a mask of table numbers. -/
def indirectTableMask : Nat :=
  2 ^ 0x03 + 2 ^ 0x05 + 2 ^ 0x07 + 2 ^ 0x13 + 2 ^ 0x16 + 2 ^ 0x1E + 2 ^ 0x1F

/-- The tables present in the `Valid` mask, with their row counts, and the offset after the
    counts. -/
def readCounts (view : ImageView) (valid cursor : Nat) :
    Except AuditError (List (Nat × Nat) × Nat) :=
  (List.range 64).foldlM (init := ([], cursor)) fun (found, position) table =>
    if valid / 2 ^ table % 2 == 1 then do
      let count ← view.u position 4
      pure (found ++ [(table, count)], position + 4)
    else pure (found, position)

/-- The table positions of an image: the container, then the `#~` header and the tables it
    declares, all inside the stream. -/
def decodeMetadata (view : ImageView) : Except AuditError MetadataLayout := do
  let pe ← decodePe view
  let start := pe.tables.start
  let heapSizes ← view.u (start + 6) 1
  if Nat.land heapSizes (Nat.xor 0xFF knownHeapFlags) != 0 then
    throw (.tables (.unsupportedHeapSizes heapSizes))
  let valid ← view.u (start + 8) 8
  if valid / 2 ^ tableLimit != 0 then throw (.tables (.unsupportedTables valid))
  if Nat.land valid indirectTableMask != 0 then throw (.tables (.pointerTables valid))
  let (counts, afterCounts) ← readCounts view valid (start + tableHeaderBytes)
  let first := if heapSizes / extraDataFlag % 2 == 1 then afterCounts + 4 else afterCounts
  let (tables, end_) := tablePositions heapSizes counts first
  if end_ > start + pe.tables.size then throw (.tables .badTableStream)
  pure { pe, heapSizes, tables }

/-- Where the rows of `table` are, when it has any. -/
def MetadataLayout.rows? (layout : MetadataLayout) (table : Nat) : Option TableRows :=
  layout.tables.find? (·.table == table)

/-- The number of rows of `table`. -/
def MetadataLayout.rowCount (layout : MetadataLayout) (table : Nat) : Nat :=
  ((layout.rows? table).map (·.count)).getD 0

/-- The metadata token of row `row` of `table`: the table number above the 1-based row number. -/
def tokenOf (table row : Nat) : Nat := table * 2 ^ 24 + row

/-- The file offset of the row a token names, and its size; row zero and rows past the count are
    out of scope. -/
def MetadataLayout.rowAt (layout : MetadataLayout) (token : Nat) : Except AuditError (Nat × Nat) :=
  match layout.rows? (token / 2 ^ 24) with
  | some rows =>
    let row := token % 2 ^ 24
    if row == 0 || row > rows.count then throw (.tokenOutOfScope token)
    else pure (rows.start + (row - 1) * rows.size, rows.size)
  | none => throw (.tokenOutOfScope token)

/-- The offset within a row of column `column` of `table`, and its width. -/
def MetadataLayout.columnIn (layout : MetadataLayout) (table column : Nat) :
    Except AuditError (Nat × Nat) := do
  let some columns := schema table | throw (.tables (.noSuchColumn table column))
  let widths := columns.map (columnWidth layout.heapSizes layout.rowCount)
  let some width := widths[column]? | throw (.tables (.noSuchColumn table column))
  pure ((widths.take column).foldl Nat.add 0, width)

/-- The file offset and width of column `column` of the row a token names. -/
def MetadataLayout.cellAt (layout : MetadataLayout) (token column : Nat) :
    Except AuditError (Nat × Nat) := do
  let (row, _) ← layout.rowAt token
  let (offset, width) ← layout.columnIn (token / 2 ^ 24) column
  pure (row + offset, width)

/-- The unsigned integer in column `column` of the row a token names. -/
def MetadataLayout.cell (layout : MetadataLayout) (view : ImageView) (token column : Nat) :
    Except AuditError Nat := do
  let (offset, width) ← layout.cellAt token column
  view.u offset width

end StrictBinding
