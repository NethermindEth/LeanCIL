import CIL.Extraction.MetadataBinding

/-!
# Hand-built metadata for tests

`Builder` assembles the rows, heap entries and links of a `MetadataSlice` the way an image
lays them out, with every index two bytes wide. `string`, `blob`, `userString` and `row` add
an entry and return its offset or token; `finish` adds the `Assembly` row and the table stream
header for the row counts so far. The builder serves tests only: nothing trusts it, because the
decoder re-reads every byte it writes.
-/

namespace Tests.MetadataBuilder

open CIL CIL.Extraction

/-- The entries added so far. -/
structure Builder where
  rows : List ByteEntry := []
  strings : List ByteEntry := [(0, [0])]
  blobs : List ByteEntry := [(0, [0])]
  userStrings : List ByteEntry := []
  stringEnd : Nat := 1
  blobEnd : Nat := 1
  userEnd : Nat := 1
  counts : List (Nat × Nat) := []
  links : List MetadataLink := []
  corlib : Nat := 0

/-- The column widths of an image whose tables are all small. -/
def smallWidths : ColumnWidths := columnWidthsOf 0 fun _ => 0

/-- The `width` little-endian bytes of a number. -/
def littleEndian : Nat → Nat → List Nat
  | 0, _ => []
  | width + 1, value => value % 256 :: littleEndian width (value / 256)

/-- The compressed encoding of a length below `0x4000`. -/
def compressedLength (length : Nat) : List Nat :=
  if length < 0x80 then [length] else [0x80 + length / 256, length % 256]

/-- The bytes of a row of a table with the given column values. -/
def encodeRow (table : Nat) (columns : List Nat) : List Nat :=
  match columnWidths smallWidths table with
  | some widths => (widths.zip columns).flatMap fun (width, value) => littleEndian width value
  | none => []

/-- Add a `#Strings` entry of the given UTF-8 bytes and return its offset. -/
def Builder.addString (builder : Builder) (text : List Nat) : Builder × Nat :=
  let bytes := text ++ [0]
  ({ builder with strings := builder.strings ++ [(builder.stringEnd, bytes)],
                  stringEnd := builder.stringEnd + bytes.length }, builder.stringEnd)

/-- Add a `#Blob` entry with the length prefix and return its offset. -/
def Builder.addBlob (builder : Builder) (payload : List Nat) : Builder × Nat :=
  let bytes := compressedLength payload.length ++ payload
  ({ builder with blobs := builder.blobs ++ [(builder.blobEnd, bytes)],
                  blobEnd := builder.blobEnd + bytes.length }, builder.blobEnd)

/-- Add a `#US` entry with the length prefix and terminal byte, and return its offset. -/
def Builder.addUserString (builder : Builder) (units : List Nat) : Builder × Nat :=
  let payload := units.flatMap (littleEndian 2) ++ [if units.any userStringFlag then 1 else 0]
  let bytes := compressedLength payload.length ++ payload
  ({ builder with userStrings := builder.userStrings ++ [(builder.userEnd, bytes)],
                  userEnd := builder.userEnd + bytes.length }, builder.userEnd)

/-- Add a row of a table and return its token. -/
def Builder.addRow (builder : Builder) (table : Nat) (columns : List Nat) : Builder × Nat :=
  let count := ((builder.counts.lookup table).getD 0) + 1
  let token := tokenOf table count
  ({ builder with rows := builder.rows ++ [(token, encodeRow table columns)],
                  counts := (builder.counts.filter (·.1 != table)) ++ [(table, count)] }, token)

/-- Add a link. -/
def Builder.addLink (builder : Builder) (kind source slice target : Nat) : Builder :=
  { builder with links := builder.links ++ [⟨kind, source, slice, target⟩] }

/-- A builder step, so a world reads as a sequence of additions. -/
abbrev Step := StateM Builder

/-- A `#Strings` entry of the bytes of a text. -/
def string (text : String) : Step Nat :=
  modifyGet fun builder => let (next, offset) := builder.addString (bytesOf text); (offset, next)

/-- A `#Strings` entry of the given UTF-8 bytes. -/
def stringBytes (text : List Nat) : Step Nat :=
  modifyGet fun builder => let (next, offset) := builder.addString text; (offset, next)

/-- A `#Blob` entry. -/
def blob (payload : List Nat) : Step Nat :=
  modifyGet fun builder => let (next, offset) := builder.addBlob payload; (offset, next)

/-- A `#US` entry from the UTF-16 units of a text. -/
def userString (units : List Nat) : Step Nat :=
  modifyGet fun builder => let (next, offset) := builder.addUserString units; (offset, next)

/-- A row of a table. -/
def row (table : Nat) (columns : List Nat) : Step Nat :=
  modifyGet fun builder => let (next, token) := builder.addRow table columns; (token, next)

/-- A link from a token to a token of the slice at `slice`. -/
def link (kind source slice target : Nat) : Step Unit :=
  modify fun builder => builder.addLink kind source slice target

/-- The table stream header for row counts: version 2.0, two-byte heaps, the present tables
    flagged in `Valid` and their row counts. -/
def tableHeader (counts : List (Nat × Nat)) : List Nat :=
  let tables := (List.range 64).filter fun table => counts.any (·.1 == table)
  let valid := tables.foldl (fun mask table => mask + 2 ^ table) 0
  [0, 0, 0, 0, 2, 0, 0, 1] ++ littleEndian 8 valid ++ littleEndian 8 0 ++
    (tables.flatMap fun table => littleEndian 4 ((counts.lookup table).getD 0))

/-- An assembly name and the pinned identity it spells, with one `Assembly` row. -/
def assemblyBlock (builder : Builder) (name : List Nat) (identity : String) (version : Nat) :
    Builder × AssemblyMetadata :=
  let (builder, nameOffset) := builder.addString name
  let counts := builder.counts.filter (·.1 != Table.assembly) ++ [(Table.assembly, 1)]
  let row := littleEndian 4 0x8004 ++ littleEndian 2 version ++ [0, 0, 0, 0, 0, 0] ++
    littleEndian 4 0 ++ littleEndian 2 0 ++ littleEndian 2 nameOffset ++ littleEndian 2 0
  (builder, { identity := identity, tableHeader := tableHeader counts, assemblyRow := row,
              strings := [(0, [0]), (nameOffset, name ++ [0])], blobs := [(0, [0])] })

/-- The slice a builder describes, with the `Assembly` row of the given name and identity. -/
def finish (builder : Builder) (name : List Nat) (identity : String) (version : Nat) :
    MetadataSlice :=
  let (builder, assembly) := assemblyBlock builder name identity version
  { assembly := { assembly with
        tableHeader := tableHeader (builder.counts.filter (·.1 != Table.assembly) ++
          [(Table.assembly, 1)]) },
    rows := builder.rows, strings := builder.strings, blobs := builder.blobs,
    userStrings := builder.userStrings, corlib := builder.corlib, links := builder.links }

/-- The slice that `step` builds, and what it returns. -/
@[irreducible] def build {α : Type} (step : Step α) (name : List Nat) (identity : String) (version : Nat := 1) :
    MetadataSlice × α :=
  let (value, builder) := step.run {}
  (finish builder name identity version, value)

end Tests.MetadataBuilder
