import CIL.Extraction.MetadataBinding
import Tests.Support.FixtureAssembly

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

/-- A type of `System.Runtime`'s `System` namespace as a platform definition of this kind. -/
def runtimeType (name : String) (kind : PlatformKind) : PlatformDefinition :=
  { assembly := runtimeAssembly, parts := [bytesOf "System", bytesOf name], kind }

/-- The platform definition of `System.Object`, the base of a fixture's classes. -/
def objectPlatform : PlatformTable := platform_table% [runtimeType "Object" .objectRoot]

/-- The table with each definition changed or dropped by `edit`; an edit that keeps the name
    parts keeps the table's keys right. -/
def editPlatform (edit : PlatformDefinition → Option PlatformDefinition)
    (table : PlatformTable) : PlatformTable :=
  { table with entries := visit table.entries }
where
  /-- Keep every key and replace its associated definitions. -/
  visit : SearchTree (List PlatformDefinition) → SearchTree (List PlatformDefinition)
    | .leaf => .leaf
    | .node left key group right => .node (visit left) key (group.filterMap edit) (visit right)

/-- The table without its definitions of types with simple name `name`. -/
def removing (table : PlatformTable) (name : String) : PlatformTable :=
  editPlatform (fun entry => if entry.parts.getLastD [] == bytesOf name then none else some entry)
    table

/-- The table with its definitions of types with simple name `name` stating `kind`. -/
def restating (table : PlatformTable) (name : String) (kind : PlatformKind) : PlatformTable :=
  editPlatform (fun entry =>
    some (if entry.parts.getLastD [] == bytesOf name then { entry with kind } else entry)) table

/-- The fixture's rows, heaps and links in reverse insertion order, with the next heap offsets. -/
structure Builder where
  reversedRows : List ByteEntry := []
  reversedStrings : List ByteEntry := [(0, [0])]
  reversedBlobs : List ByteEntry := [(0, [0])]
  reversedUserStrings : List ByteEntry := []
  stringEnd : Nat := 1
  blobEnd : Nat := 1
  userEnd : Nat := 1
  counts : List (Nat × Nat) := []
  reversedLinks : List MetadataLink := []
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

/-- Add a `#Strings` entry of the given UTF-8 bytes and return its offset. Each operation takes
    the builder apart once, so that elaborator reduction reads the previous state once per field
    instead of once per use. -/
def Builder.addString : Builder → List Nat → Builder × Nat
  | ⟨rows, strings, blobs, userStrings, stringEnd, blobEnd, userEnd, counts, links, corlib⟩,
    text =>
    let bytes := text ++ [0]
    (⟨rows, (stringEnd, bytes) :: strings, blobs, userStrings, stringEnd + bytes.length, blobEnd,
      userEnd, counts, links, corlib⟩, stringEnd)

/-- Add a `#Blob` entry with the length prefix and return its offset. -/
def Builder.addBlob : Builder → List Nat → Builder × Nat
  | ⟨rows, strings, blobs, userStrings, stringEnd, blobEnd, userEnd, counts, links, corlib⟩,
    payload =>
    let bytes := compressedLength payload.length ++ payload
    (⟨rows, strings, (blobEnd, bytes) :: blobs, userStrings, stringEnd, blobEnd + bytes.length,
      userEnd, counts, links, corlib⟩, blobEnd)

/-- Add a `#US` entry with the length prefix and terminal byte, and return its offset. -/
def Builder.addUserString : Builder → List Nat → Builder × Nat
  | ⟨rows, strings, blobs, userStrings, stringEnd, blobEnd, userEnd, counts, links, corlib⟩,
    units =>
    let payload := units.flatMap (littleEndian 2) ++ [if units.any userStringFlag then 1 else 0]
    let bytes := compressedLength payload.length ++ payload
    (⟨rows, strings, blobs, (userEnd, bytes) :: userStrings, stringEnd, blobEnd,
      userEnd + bytes.length, counts, links, corlib⟩, userEnd)

/-- Add a row of a table and return its token. -/
def Builder.addRow : Builder → Nat → List Nat → Builder × Nat
  | ⟨rows, strings, blobs, userStrings, stringEnd, blobEnd, userEnd, counts, links, corlib⟩,
    table, columns =>
    let count := ((counts.lookup table).getD 0) + 1
    let token := tokenOf table count
    (⟨(token, encodeRow table columns) :: rows, strings, blobs, userStrings, stringEnd, blobEnd,
      userEnd, (counts.filter (·.1 != table)) ++ [(table, count)], links, corlib⟩, token)

/-- Add a link. -/
def Builder.addLink : Builder → Nat → Nat → Nat → Nat → Builder
  | ⟨rows, strings, blobs, userStrings, stringEnd, blobEnd, userEnd, counts, links, corlib⟩,
    kind, source, slice, target =>
    ⟨rows, strings, blobs, userStrings, stringEnd, blobEnd, userEnd, counts,
      ⟨kind, source, slice, target⟩ :: links, corlib⟩
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

/-- The assembly `name` at major version `version`, unsigned and neutral, as one `Assembly` row. -/
def assemblyBlock (builder : Builder) (name : List Nat) (version : Nat) :
    Builder × AssemblyMetadata :=
  let (builder, nameOffset) := builder.addString name
  let counts := builder.counts.filter (·.1 != Table.assembly) ++ [(Table.assembly, 1)]
  let row := littleEndian 4 0x8004 ++ littleEndian 2 version ++ [0, 0, 0, 0, 0, 0] ++
    littleEndian 4 0 ++ littleEndian 2 0 ++ littleEndian 2 nameOffset ++ littleEndian 2 0
  (builder, { tableHeader := tableHeader counts, assemblyRow := row,
              strings := [(0, [0]), (nameOffset, name ++ [0])], blobs := [(0, [0])] })

/-- The ascending runs in insertion order. Each added item precedes the current run in the
    fixture, so ties stay in their original order. -/
private def ascendingRuns {α : Type} (key : α → Nat) :
    List α → α → List α → List (List α) → List (List α)
  | [], first, rest, runs => (first :: rest) :: runs
  | item :: items, first, rest, runs =>
    if key item ≤ key first then ascendingRuns key items item (first :: rest) runs
    else ascendingRuns key items item [] ((first :: rest) :: runs)

/-- The stable merge of each adjacent pair of ascending runs. -/
private def mergePairs {α : Type} (key : α → Nat) : List (List α) → List (List α)
  | first :: second :: rest =>
    mergeBy (fun left right => key left ≤ key right) (first.length + second.length) first second ::
      mergePairs key rest
  | runs => runs

/-- Sort the runs in at most logarithmically many passes, with their count as a recursion bound. -/
private def mergeRuns {α : Type} (key : α → Nat) : Nat → List (List α) → List α
  | _, [] => []
  | _, [sorted] => sorted
  | 0, runs => runs.flatten
  | fuel + 1, runs => mergeRuns key fuel (mergePairs key runs)

/-- Order the accumulated rows or links by key, preserving insertion order for equal keys. -/
private def ordered {α : Type} (key : α → Nat) : List α → List α
  | [] => []
  | first :: rest =>
    let runs := ascendingRuns key rest first [] []
    mergeRuns key runs.length runs

/-- The slice a builder describes, with the `Assembly` row of the given name and version. -/
def finish (builder : Builder) (name : List Nat) (version : Nat) :
    MetadataSlice :=
  let (builder, assembly) := assemblyBlock builder name version
  { assembly := { assembly with
        tableHeader := tableHeader (builder.counts.filter (·.1 != Table.assembly) ++
          [(Table.assembly, 1)]) },
    rows := ordered (·.1) builder.reversedRows, strings := builder.reversedStrings.reverse,
    blobs := builder.reversedBlobs.reverse, userStrings := builder.reversedUserStrings.reverse,
    corlib := builder.corlib,
    links := ordered (fun link => link.kind * 0x100000000 + link.source) builder.reversedLinks }

/-- The slice that `step` builds, and what it returns. -/
def build {α : Type} (step : Step α) (name : List Nat) (version : Nat := 1) :
    MetadataSlice × α :=
  let (value, builder) := step.run {}
  (finish builder name version, value)

end Tests.MetadataBuilder
