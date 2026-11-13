import Std.Data.TreeMap
import CIL.Extraction.KernelEquation

/-!
# Metadata tables and heaps

An extraction carries the bytes of the metadata rows and heap entries a method uses, with one
small header block per pinned assembly. This file reads those bytes by ECMA-335 II.22 and II.24:
the table stream header, the widths it fixes for every column, the rows of the tables the
checker decodes, and the entries of the `#Strings`, `#Blob` and `#US` heaps. Each slice builds
one balanced search tree per kind, so a token costs one lookup.

Only the carried bytes are decoded. Whether they are the image's bytes at those positions is the
extractor's claim: every row must still have the length the header's widths give, every blob its
length prefix and every string one terminating zero.
-/

namespace CIL.Extraction

/-- A heap entry or table row: its key (a heap offset, or a token) and its bytes. -/
abbrev ByteEntry := Nat × List Nat

/-- The metadata an assembly's own identity is read from, shared by every method of the
    assembly: its table stream header, its `Assembly` row and the heap entries the row names. -/
structure AssemblyMetadata where
  /-- The pin identity the bytes must spell, with the public key token as the pin writes it. -/
  identity : String := ""
  /-- The public key token the pin writes, as sixteen lowercase hexadecimal digits, when the
      `Assembly` row has a public key; empty otherwise. -/
  keyToken : List Nat := []
  /-- The table stream bytes from the version fields through the last row count. -/
  tableHeader : List Nat := []
  /-- Row 1 of the `Assembly` table. -/
  assemblyRow : List Nat := []
  strings : List ByteEntry := []
  blobs : List ByteEntry := []
  deriving DecidableEq, Repr

/-- A fact the extractor states about a token of a slice, which the checker verifies against
    the carried rows: `kind` says what `target` is, in the slice with index `slice`. -/
structure MetadataLink where
  kind : Nat
  source : Nat
  slice : Nat
  target : Nat
  deriving DecidableEq, Repr

/-- A link names the definition a `TypeRef` or `MemberRef` token resolves to. -/
def linkDefinition : Nat := 0

/-- A link names the `TypeDef` that declares a `Field` or `MethodDef` token. -/
def linkDeclaring : Nat := 1

/-- A link names the `NestedClass` row of a nested `TypeDef` token. -/
def linkNesting : Nat := 2

/-- A link names the first `GenericParam` row of a `TypeDef` or `MethodDef` token. -/
def linkGenericParams : Nat := 3

/-- The rows and heap entries one method's tokens, definition and locals reach in one
    assembly, with the links that locate definitions among them. -/
structure MetadataSlice where
  assembly : AssemblyMetadata := {}
  /-- Table rows keyed by token: the table number times `2 ^ 24` plus the row number. -/
  rows : List ByteEntry := []
  /-- `#Strings` entries keyed by offset, through the terminating zero. -/
  strings : List ByteEntry := []
  /-- `#Blob` entries keyed by offset, including the compressed length. -/
  blobs : List ByteEntry := []
  /-- `#US` entries keyed by offset, including the length and the terminal byte. -/
  userStrings : List ByteEntry := []
  /-- The `AssemblyRef` row of the assembly that defines the primitive types, or 0. -/
  corlib : Nat := 0
  links : List MetadataLink := []
  deriving DecidableEq, Repr

/-- The metadata of one method body: the slice of its own assembly, which comes first, and the
    slices of the other pinned assemblies its tokens resolve into. -/
structure MethodMetadata where
  own : MetadataSlice := {}
  others : List MetadataSlice := []
  deriving DecidableEq, Repr

/-- Why metadata bytes, or a claim about them, are refused. -/
inductive MetadataError where
  | invalidByte
  | duplicateEntry (key : Nat)
  | unsupportedTableStream (detail : Nat)
  | malformedTableHeader
  | tokenOutOfScope (token : Nat)
  | missingRow (token : Nat)
  | unsupportedTable (token : Nat)
  | rowLength (token expected actual : Nat)
  | badCodedIndex (value : Nat)
  | missingHeap (heap offset : Nat)
  | malformedHeap (heap offset : Nat)
  | malformedUserString (offset : Nat)
  | truncatedSignature (offset : Nat)
  | unsupportedSignature (offset element : Nat)
  | unsupportedAssemblyRef (token : Nat)
  | unsupportedScope (token : Nat)
  | unsupportedBase (token : Nat)
  | unsupportedUserString (offset : Nat)
  | unsupportedModifier (token : Nat)
  | unresolvedType (token : Nat)
  | unresolvedMember (token : Nat)
  | operandMismatch (token : Nat)
  | scopeMismatch (token : Nat)
  | genericMismatch (token : Nat)
  | fieldIndexMismatch (token stated computed : Nat)
  | localMismatch (index : Nat)
  | methodMismatch (token : Nat)
  | identityMismatch
  /-- A reference into a pinned assembly whose slice the evidence does not carry. -/
  | missingSlice (token : Nat)
  | bodyLocation (token : Nat)
  | tablesMismatch
  deriving DecidableEq, Repr



/-- The heap number `MetadataError.missingHeap` reports for `#Strings`. -/
def stringsHeap : Nat := 0

/-- The heap number `MetadataError.missingHeap` reports for `#Blob`. -/
def blobHeap : Nat := 1

/-- The heap number `MetadataError.missingHeap` reports for `#US`. -/
def userStringHeap : Nat := 2

/-- The table number of a token: its top byte. -/
def metadataTableOf (token : Nat) : Nat := token / 0x1000000

/-- The row number of a token: its low three bytes. -/
def tokenRow (token : Nat) : Nat := token % 0x1000000

/-- The token of a row of a table. -/
def tokenOf (table row : Nat) : Nat := table * 0x1000000 + row

/-! The metadata table numbers of II.22 that the checker reads; a user string is table `0x70`
    and a standalone signature is table `0x11`. -/
namespace Table
def module : Nat := 0x00
def typeRef : Nat := 0x01
def typeDef : Nat := 0x02
def field : Nat := 0x04
def methodDef : Nat := 0x06
def memberRef : Nat := 0x0A
def standAloneSig : Nat := 0x11
def moduleRef : Nat := 0x1A
def typeSpec : Nat := 0x1B
def assembly : Nat := 0x20
def assemblyRef : Nat := 0x23
def nestedClass : Nat := 0x29
def genericParam : Nat := 0x2A
def methodSpec : Nat := 0x2B
def userString : Nat := 0x70
end Table

/-! ## Compressed integers and little-endian values -/

/-- The unsigned compressed integer at the front of the bytes (II.23.2) and the bytes after
    it; a first byte of `0xE0` or more is not one. -/
def decodeCompressed : List Nat → Option (Nat × List Nat)
  | [] => none
  | first :: rest =>
    if first < 0x80 then some (first, rest)
    else if first < 0xC0 then
      match rest with
      | second :: tail => some ((first - 0x80) * 0x100 + second, tail)
      | [] => none
    else if first < 0xE0 then
      match rest with
      | second :: third :: fourth :: tail =>
        some ((((first - 0xC0) * 0x100 + second) * 0x100 + third) * 0x100 + fourth, tail)
      | _ => none
    else none

/-- The little-endian value of the next `width` bytes, and the bytes after them. -/
def readLittle : Nat → List Nat → Option (Nat × List Nat)
  | 0, rest => some (0, rest)
  | width + 1, byte :: rest => do
    let (high, tail) ← readLittle width rest
    some (byte + 0x100 * high, tail)
  | _ + 1, [] => none

/-- Split bytes into little-endian columns of the given widths; the bytes must be used up. -/
def splitColumns : List Nat → List Nat → Option (List Nat)
  | [], [] => some []
  | [], _ :: _ => none
  | width :: widths, bytes => do
    let (value, rest) ← readLittle width bytes
    let values ← splitColumns widths rest
    some (value :: values)

/-! ## The table stream header -/

/-- How many bytes each kind of column takes, fixed by the row counts and heap sizes. -/
structure ColumnWidths where
  string : Nat
  blob : Nat
  field : Nat
  methodDef : Nat
  param : Nat
  typeDef : Nat
  genericParam : Nat
  typeDefOrRef : Nat
  resolutionScope : Nat
  memberRefParent : Nat
  methodDefOrRef : Nat
  typeOrMethodDef : Nat
  deriving DecidableEq, Repr

/-- The decoded table stream header: heap sizes, the row count of each present table and the
    column widths they imply. -/
structure TableHeader where
  heapSizes : Nat
  rowCounts : Std.TreeMap Nat Nat compare
  widths : ColumnWidths

/-- The row count of a table; an absent table has none. -/
def TableHeader.rows (header : TableHeader) (table : Nat) : Nat :=
  (header.rowCounts[table]?).getD 0

/-- The tables whose presence makes the header unsupported: the pointer tables of an
    uncompressed stream and the edit-and-continue tables. -/
def unsupportedTables : List Nat := [0x03, 0x05, 0x07, 0x13, 0x16, 0x1E, 0x1F]

/-- The width of an index into a table with `rows` rows. -/
def simpleWidth (rows : Nat) : Nat := if rows < 0x10000 then 2 else 4

/-- The width of a coded index of `bits` tag bits over tables with at most `rows` rows. -/
def codedWidth (bits rows : Nat) : Nat := if rows < 2 ^ (16 - bits) then 2 else 4

/-- The column widths of a header, as II.24.2.6 and II.22 define them. -/
def columnWidthsOf (heapSizes : Nat) (rows : Nat → Nat) : ColumnWidths :=
  { string := if heapSizes % 2 == 1 then 4 else 2,
    blob := if heapSizes / 4 % 2 == 1 then 4 else 2,
    field := simpleWidth (rows 0x04), methodDef := simpleWidth (rows 0x06),
    param := simpleWidth (rows 0x08), typeDef := simpleWidth (rows 0x02),
    genericParam := simpleWidth (rows 0x2A),
    typeDefOrRef := codedWidth 2 (max (rows 0x02) (max (rows 0x01) (rows 0x1B))),
    resolutionScope := codedWidth 2
      (max (rows 0x00) (max (rows 0x1A) (max (rows 0x23) (rows 0x01)))),
    memberRefParent := codedWidth 3
      (max (rows 0x02) (max (rows 0x01) (max (rows 0x1A) (max (rows 0x06) (rows 0x1B))))),
    methodDefOrRef := codedWidth 1 (max (rows 0x06) (rows 0x0A)),
    typeOrMethodDef := codedWidth 1 (max (rows 0x02) (rows 0x06)) }

/-- The row counts of the tables flagged in `valid`, read in table order from `bytes`. The
    count of tables left to examine is `fuel`; every byte must be used. -/
private def readRowCounts (valid : Nat) :
    Nat → Nat → List Nat → Except MetadataError (List (Nat × Nat))
  | 0, _, [] => .ok []
  | 0, _, _ :: _ => .error .malformedTableHeader
  | fuel + 1, table, bytes =>
    if valid / 2 ^ table % 2 == 1 then
      match readLittle 4 bytes with
      | some (count, rest) => do
        let counts ← readRowCounts valid fuel (table + 1) rest
        .ok ((table, count) :: counts)
      | none => .error .malformedTableHeader
    else readRowCounts valid fuel (table + 1) bytes

/-- Insert the row counts of a header into a map. -/
private def countMap : List (Nat × Nat) → Std.TreeMap Nat Nat compare → Std.TreeMap Nat Nat compare
  | [], map => map
  | (table, count) :: rest, map => countMap rest (map.insert table count)

/-- The number of tables in a 64-bit validity mask. -/
private def tableSlots : Nat := 64

/-- The `HeapSizes` byte, the `Valid` mask and the first row count sit at fixed offsets of the
    table stream: 6, 8 and 24 (II.24.2.6). -/
private def heapSizesOffset : Nat := 6
private def validOffset : Nat := 8
private def tableHeaderFixedSize : Nat := 24

/-- Decode the table stream header (II.24.2.6): the bytes from the reserved word through the
    last row count. Heap-size bits outside the three index flags, and pointer or
    edit-and-continue tables, are unsupported. -/
def decodeTableHeader (bytes : List Nat) : Except MetadataError TableHeader :=
  if !bytes.all (· < 256) then .error .invalidByte
  else if bytes.length < tableHeaderFixedSize then .error .malformedTableHeader
  else
    let heapSizes := bytes.getD heapSizesOffset 0
    match readLittle 8 (bytes.drop validOffset) with
    | some (valid, _) =>
      if heapSizes ≥ 8 then .error (.unsupportedTableStream heapSizes)
      else if unsupportedTables.any (fun table => valid / 2 ^ table % 2 == 1) then
        .error (.unsupportedTableStream 0x100)
      else do
        let present ← readRowCounts valid tableSlots 0 (bytes.drop tableHeaderFixedSize)
        let rowCounts := countMap present ∅
        .ok { heapSizes := heapSizes, rowCounts := rowCounts,
              widths := columnWidthsOf heapSizes fun table => (rowCounts[table]?).getD 0 }
    | none => .error .malformedTableHeader

/-! ## Rows -/

/-- The widths of the columns of a decoded table's row, or `none` for a table the checker does
    not read. The `Module` table is not read: its columns are not needed. -/
def columnWidths (widths : ColumnWidths) : Nat → Option (List Nat)
  | 0x01 => some [widths.resolutionScope, widths.string, widths.string]
  | 0x02 => some [4, widths.string, widths.string, widths.typeDefOrRef, widths.field,
      widths.methodDef]
  | 0x04 => some [2, widths.string, widths.blob]
  | 0x06 => some [4, 2, 2, widths.string, widths.blob, widths.param]
  | 0x0A => some [widths.memberRefParent, widths.string, widths.blob]
  | 0x11 => some [widths.blob]
  | 0x1B => some [widths.blob]
  | 0x20 => some [4, 2, 2, 2, 2, 4, widths.blob, widths.string, widths.string]
  | 0x23 => some [2, 2, 2, 2, 4, widths.blob, widths.string, widths.string, widths.blob]
  | 0x29 => some [widths.typeDef, widths.typeDef]
  | 0x2A => some [2, 2, widths.typeOrMethodDef, widths.string]
  | 0x2B => some [widths.methodDefOrRef, widths.blob]
  | _ => none

/-- The byte length of a row of a table the checker reads. -/
def rowSize (widths : ColumnWidths) (table : Nat) : Option Nat :=
  (columnWidths widths table).map List.sum

/-- A coded index as a token: the tag picks the table, the rest is the row. -/
def decodeCoded (tags : List Nat) (bits value : Nat) : Except MetadataError Nat :=
  match tags[value % 2 ^ bits]? with
  | some table => .ok (tokenOf table (value / 2 ^ bits))
  | none => .error (.badCodedIndex value)

/-- The tables a `TypeDefOrRef` coded index names, by tag. -/
def typeDefOrRefTags : List Nat := [0x02, 0x01, 0x1B]
/-- The tables a `ResolutionScope` coded index names, by tag. -/
def resolutionScopeTags : List Nat := [0x00, 0x1A, 0x23, 0x01]
/-- The tables a `MemberRefParent` coded index names, by tag. -/
def memberRefParentTags : List Nat := [0x02, 0x01, 0x1A, 0x06, 0x1B]
/-- The tables a `MethodDefOrRef` coded index names, by tag. -/
def methodDefOrRefTags : List Nat := [0x06, 0x0A]
/-- The tables a `TypeOrMethodDef` coded index names, by tag. -/
def typeOrMethodDefTags : List Nat := [0x02, 0x06]

/-- A `TypeRef` row: where its type lives, its name and its namespace. -/
structure TypeRefRow where
  scope : Nat
  name : Nat
  namespace_ : Nat
  deriving DecidableEq, Repr

/-- A `TypeDef` row. `extends_` is a token, or the row-0 token of table `0x02` for no base. -/
structure TypeDefRow where
  flags : Nat
  name : Nat
  namespace_ : Nat
  extends_ : Nat
  fieldList : Nat
  methodList : Nat
  deriving DecidableEq, Repr

/-- A `Field` row. -/
structure FieldRow where
  flags : Nat
  name : Nat
  signature : Nat
  deriving DecidableEq, Repr

/-- A `MethodDef` row. -/
structure MethodDefRow where
  rva : Nat
  implFlags : Nat
  flags : Nat
  name : Nat
  signature : Nat
  paramList : Nat
  deriving DecidableEq, Repr

/-- A `MemberRef` row: its parent as a token, its name and its signature blob. -/
structure MemberRefRow where
  parent : Nat
  name : Nat
  signature : Nat
  deriving DecidableEq, Repr

/-- An `AssemblyRef` row. -/
structure AssemblyRefRow where
  major : Nat
  minor : Nat
  build : Nat
  revision : Nat
  flags : Nat
  publicKeyOrToken : Nat
  name : Nat
  culture : Nat
  deriving DecidableEq, Repr

/-- An `Assembly` row. -/
structure AssemblyRow where
  major : Nat
  minor : Nat
  build : Nat
  revision : Nat
  flags : Nat
  publicKey : Nat
  name : Nat
  culture : Nat
  deriving DecidableEq, Repr

/-- A `NestedClass` row. -/
structure NestedClassRow where
  nested : Nat
  enclosing : Nat
  deriving DecidableEq, Repr

/-- A `GenericParam` row: its position, flags and owner token. -/
structure GenericParamRow where
  number : Nat
  flags : Nat
  owner : Nat
  name : Nat
  deriving DecidableEq, Repr

/-- A `MethodSpec` row: the instantiated method and its instantiation blob. -/
structure MethodSpecRow where
  method : Nat
  instantiation : Nat
  deriving DecidableEq, Repr

/-! ## Search trees -/

/-- A binary search tree keyed by number, built balanced from entries in ascending key order, so a
    lookup costs the logarithm of the entry count and the tree can be written out as a literal. -/
inductive SearchTree (α : Type) where
  | leaf
  | node (left : SearchTree α) (key : Nat) (value : α) (right : SearchTree α)
  deriving DecidableEq, Repr

namespace SearchTree

variable {α : Type}

/-- The value stored under `wanted`. -/
def find? : SearchTree α → Nat → Option α
  | .leaf, _ => none
  | .node left key value right, wanted =>
    match compare wanted key with
    | .lt => find? left wanted
    | .gt => find? right wanted
    | .eq => some value

/-- The entries in ascending key order. -/
def toList : SearchTree α → List (Nat × α)
  | .leaf => []
  | .node left key value right => left.toList ++ (key, value) :: right.toList

/-- The tree of the first `count` entries, taking `count / 2` of them to the left of the root, and
    the entries left over. `fuel` bounds the depth. -/
private def build : Nat → Nat → List (Nat × α) → SearchTree α × List (Nat × α)
  | 0, _, rest => (.leaf, rest)
  | fuel + 1, count, rest =>
    if count == 0 then (.leaf, rest)
    else
      let leftCount := count / 2
      let (left, afterLeft) := build fuel leftCount rest
      match afterLeft with
      | [] => (left, [])
      | (key, value) :: afterRoot =>
        let (right, remaining) := build fuel (count - 1 - leftCount) afterRoot
        (.node left key value right, remaining)

/-- The balanced tree of entries in ascending key order. -/
def ofSorted (entries : List (Nat × α)) : SearchTree α :=
  (build entries.length entries.length entries).1

/-- The first key that does not ascend strictly from its predecessor. -/
def firstOutOfOrder : Option Nat → List (Nat × α) → Option Nat
  | _, [] => none
  | none, (key, _) :: rest => firstOutOfOrder (some key) rest
  | some previous, (key, _) :: rest =>
    if previous < key then firstOutOfOrder (some key) rest else some key

/-- The balanced tree of the entries, which must have strictly ascending keys. -/
def ofEntries (entries : List (Nat × α)) : Except MetadataError (SearchTree α) :=
  match firstOutOfOrder none entries with
  | some key => .error (.duplicateEntry key)
  | none => .ok (ofSorted entries)

end SearchTree

/-- The lookup structures of one slice: one tree per kind of entry, and the instance field counts
    derived from the rows. They cost the size of the slice to build, so an extraction carries them
    as literals that one theorem equates with `MetadataSlice.tables`. -/
structure IndexTables where
  rows : SearchTree (List Nat)
  strings : SearchTree (List Nat)
  blobs : SearchTree (List Nat)
  userStrings : SearchTree (List Nat)
  /-- Links keyed by `kind * 2 ^ 32 + source`, giving the slice index and target token. -/
  links : SearchTree (Nat × Nat)
  /-- For each Field row of a carried type, the instance fields before it in its type. -/
  instanceBefore : SearchTree Nat
  /-- For each carried TypeDef whose fields are all carried, its number of instance fields. -/
  instanceTotal : SearchTree Nat
  deriving DecidableEq, Repr

/-! ## One slice, indexed -/
/-- One slice with a tree per kind of entry, so a token or offset is a single lookup. -/
structure MetadataIndex extends IndexTables where
  header : TableHeader
  corlib : Nat
  /-- The identity of the assembly the slice is cut from, as the `Assembly` row spells it. -/
  identity : List Nat

/-- The entries as a tree keyed by offset or token; they must be bytes with ascending keys. -/
def indexEntries (entries : List ByteEntry) : Except MetadataError (SearchTree (List Nat)) :=
  if !entries.all (fun entry => entry.2.all (· < 256)) then .error .invalidByte
  else SearchTree.ofEntries entries
/-- The bytes of a string literal, for comparison with heap entries. -/
def bytesOf (text : String) : List Nat := text.toByteArray.data.toList.map UInt8.toNat

/-- The entry of a heap map: the bytes, or `missingHeap`. -/
def heapEntry (heap : Nat) (entries : SearchTree (List Nat)) (offset : Nat) :
    Except MetadataError (List Nat) :=
  match entries.find? offset with
  | some bytes => .ok bytes
  | none => .error (.missingHeap heap offset)

/-- A `#Strings` entry without its terminating zero; the entry must have exactly one zero,
    at its end. -/
def stringBytes (entries : SearchTree (List Nat)) (offset : Nat) :
    Except MetadataError (List Nat) := do
  let bytes ← heapEntry stringsHeap entries offset
  match bytes.reverse with
  | 0 :: reversed =>
    if reversed.contains 0 then .error (.malformedHeap stringsHeap offset)
    else .ok reversed.reverse
  | _ => .error (.malformedHeap stringsHeap offset)

/-- A `#Blob` entry without its length prefix; the prefix must give the remaining length. -/
def blobBytes (entries : SearchTree (List Nat)) (offset : Nat) :
    Except MetadataError (List Nat) := do
  let bytes ← heapEntry blobHeap entries offset
  match decodeCompressed bytes with
  | some (length, rest) =>
    if rest.length == length then .ok rest else .error (.malformedHeap blobHeap offset)
  | none => .error (.malformedHeap blobHeap offset)

/-- The bytes of the UTF-16 code units of a string from its UTF-8 bytes. -/
def utf16Units : Nat → List Nat → Option (List Nat)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, first :: rest =>
    if first < 0x80 then (first :: ·) <$> utf16Units fuel rest
    else if first < 0xC0 then none
    else if first < 0xE0 then
      match rest with
      | second :: tail =>
        if second / 0x40 != 2 then none
        else ((first % 0x20 * 0x40 + second % 0x40) :: ·) <$> utf16Units fuel tail
      | [] => none
    else if first < 0xF0 then
      match rest with
      | second :: third :: tail =>
        let point := (first % 0x10 * 0x40 + second % 0x40) * 0x40 + third % 0x40
        if second / 0x40 != 2 || third / 0x40 != 2 || point < 0x800 then none
        else ((point :: ·) <$> utf16Units fuel tail)
      | _ => none
    else
      match rest with
      | second :: third :: fourth :: tail =>
        let point := ((first % 0x08 * 0x40 + second % 0x40) * 0x40 + third % 0x40) * 0x40 +
          fourth % 0x40
        if second / 0x40 != 2 || third / 0x40 != 2 || fourth / 0x40 != 2 ||
            point < 0x10000 || point > 0x10FFFF then none
        else
          let offset := point - 0x10000
          (fun units => (0xD800 + offset / 0x400) :: (0xDC00 + offset % 0x400) :: units) <$>
            utf16Units fuel tail
      | _ => none

/-- Whether a UTF-16 code unit sets the terminal flag of a `#US` entry (II.24.2.4). -/
def userStringFlag (unit : Nat) : Bool :=
  unit ≥ 0x100 || (0x01 ≤ unit && unit ≤ 0x08) || (0x0E ≤ unit && unit ≤ 0x1F) ||
    unit == 0x27 || unit == 0x2D || unit == 0x7F

/-- The little-endian 16-bit units of an even number of bytes. -/
private def littleUnits : Nat → List Nat → Option (List Nat)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, low :: high :: tail => ((low + 0x100 * high) :: ·) <$> littleUnits fuel tail
  | _ + 1, [_] => none

/-- The UTF-16 code units of a `#US` entry. Its length counts the units' bytes and the
    terminal byte, which is 1 exactly when a unit needs the flag. -/
def userStringUnits (entries : SearchTree (List Nat)) (offset : Nat) :
    Except MetadataError (List Nat) := do
  let bytes ← heapEntry userStringHeap entries offset
  let some (length, rest) := decodeCompressed bytes
    | throw (.malformedHeap userStringHeap offset)
  if rest.length != length then throw (.malformedHeap userStringHeap offset)
  let payload := rest.dropLast
  let terminal := rest.getLast?.getD 2
  let some units := littleUnits payload.length payload
    | throw (.malformedUserString offset)
  let flagged := units.any userStringFlag
  if terminal != (if flagged then 1 else 0) then throw (.malformedUserString offset)
  .ok units

/-! ## Rows by token -/

/-- The row bytes of a token: the token must be in scope of the header, the slice must carry
    its row, the table must be one the checker reads and the row must have the length the
    header's widths give. -/
def MetadataIndex.row (index : MetadataIndex) (token : Nat) : Except MetadataError (List Nat) :=
  let table := metadataTableOf token
  if tokenRow token == 0 || index.header.rows table < tokenRow token then
    .error (.tokenOutOfScope token)
  else match columnWidths index.header.widths table, index.rows.find? token with
  | none, _ => .error (.unsupportedTable token)
  | some widths, some bytes =>
    if bytes.length == widths.sum then .ok bytes
    else .error (.rowLength token widths.sum bytes.length)
  | some _, none => .error (.missingRow token)

/-- The columns of a row as numbers. -/
def MetadataIndex.columns (index : MetadataIndex) (token : Nat) :
    Except MetadataError (List Nat) := do
  let bytes ← index.row token
  match columnWidths index.header.widths (metadataTableOf token) with
  | some widths =>
    match splitColumns widths bytes with
    | some values => .ok values
    | none => .error (.rowLength token widths.sum bytes.length)
  | none => .error (.unsupportedTable token)

/-- A row of a given table; a token of another table is out of scope. -/
private def MetadataIndex.columnsOf (index : MetadataIndex) (table token : Nat) :
    Except MetadataError (List Nat) :=
  if metadataTableOf token == table then index.columns token else .error (.tokenOutOfScope token)

/-- The `TypeRef` row of a token. -/
def MetadataIndex.typeRef (index : MetadataIndex) (token : Nat) :
    Except MetadataError TypeRefRow := do
  match ← index.columnsOf Table.typeRef token with
  | [scope, name, namespace_] =>
    .ok { scope := ← decodeCoded resolutionScopeTags 2 scope, name, namespace_ }
  | _ => .error (.unsupportedTable token)

/-- The `TypeDef` row of a token. -/
def MetadataIndex.typeDef (index : MetadataIndex) (token : Nat) :
    Except MetadataError TypeDefRow := do
  match ← index.columnsOf Table.typeDef token with
  | [flags, name, namespace_, extends_, fieldList, methodList] =>
    .ok { flags, name, namespace_, extends_ := ← decodeCoded typeDefOrRefTags 2 extends_,
          fieldList, methodList }
  | _ => .error (.unsupportedTable token)

/-- The `Field` row of a token. -/
def MetadataIndex.field (index : MetadataIndex) (token : Nat) :
    Except MetadataError FieldRow := do
  match ← index.columnsOf Table.field token with
  | [flags, name, signature] => .ok { flags, name, signature }
  | _ => .error (.unsupportedTable token)

/-- The `MethodDef` row of a token. -/
def MetadataIndex.methodDef (index : MetadataIndex) (token : Nat) :
    Except MetadataError MethodDefRow := do
  match ← index.columnsOf Table.methodDef token with
  | [rva, implFlags, flags, name, signature, paramList] =>
    .ok { rva, implFlags, flags, name, signature, paramList }
  | _ => .error (.unsupportedTable token)

/-- The `MemberRef` row of a token. -/
def MetadataIndex.memberRef (index : MetadataIndex) (token : Nat) :
    Except MetadataError MemberRefRow := do
  match ← index.columnsOf Table.memberRef token with
  | [parent, name, signature] =>
    .ok { parent := ← decodeCoded memberRefParentTags 3 parent, name, signature }
  | _ => .error (.unsupportedTable token)

/-- The signature blob offset of a `StandAloneSig` or `TypeSpec` row. -/
def MetadataIndex.signatureOf (index : MetadataIndex) (table token : Nat) :
    Except MetadataError Nat := do
  match ← index.columnsOf table token with
  | [signature] => .ok signature
  | _ => .error (.unsupportedTable token)

/-- The `AssemblyRef` row of a token. -/
def MetadataIndex.assemblyRef (index : MetadataIndex) (token : Nat) :
    Except MetadataError AssemblyRefRow := do
  match ← index.columnsOf Table.assemblyRef token with
  | [major, minor, build, revision, flags, publicKeyOrToken, name, culture, _] =>
    .ok { major, minor, build, revision, flags, publicKeyOrToken, name, culture }
  | _ => .error (.unsupportedTable token)

/-- The `NestedClass` row of a token. -/
def MetadataIndex.nestedClass (index : MetadataIndex) (token : Nat) :
    Except MetadataError NestedClassRow := do
  match ← index.columnsOf Table.nestedClass token with
  | [nested, enclosing] =>
    .ok { nested := tokenOf Table.typeDef nested, enclosing := tokenOf Table.typeDef enclosing }
  | _ => .error (.unsupportedTable token)

/-- The `GenericParam` row of a token. -/
def MetadataIndex.genericParam (index : MetadataIndex) (token : Nat) :
    Except MetadataError GenericParamRow := do
  match ← index.columnsOf Table.genericParam token with
  | [number, flags, owner, name] =>
    .ok { number, flags, owner := ← decodeCoded typeOrMethodDefTags 1 owner, name }
  | _ => .error (.unsupportedTable token)

/-- The `MethodSpec` row of a token. -/
def MetadataIndex.methodSpec (index : MetadataIndex) (token : Nat) :
    Except MetadataError MethodSpecRow := do
  match ← index.columnsOf Table.methodSpec token with
  | [method, instantiation] =>
    .ok { method := ← decodeCoded methodDefOrRefTags 1 method, instantiation }
  | _ => .error (.unsupportedTable token)

/-- A `#Strings` entry of the slice. -/
def MetadataIndex.string (index : MetadataIndex) (offset : Nat) :
    Except MetadataError (List Nat) :=
  stringBytes index.strings offset

/-- A `#Blob` entry of the slice, without its length prefix. -/
def MetadataIndex.blob (index : MetadataIndex) (offset : Nat) :
    Except MetadataError (List Nat) :=
  blobBytes index.blobs offset

/-- A `#US` entry of the slice as UTF-16 code units. -/
def MetadataIndex.userString (index : MetadataIndex) (offset : Nat) :
    Except MetadataError (List Nat) :=
  userStringUnits index.userStrings offset

/-! ## The identity of an assembly -/

/-- The decimal ASCII digits of a number below `10 ^ fuel`. -/
def decimalDigits : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, value =>
    if value < 10 then [48 + value] else decimalDigits fuel (value / 10) ++ [48 + value % 10]

/-- The 16 lowercase hexadecimal digits of the eight bytes of a public key token. -/
def hexDigits : List Nat → List Nat
  | [] => []
  | byte :: rest =>
    let digit (value : Nat) : Nat := if value < 10 then 48 + value else 87 + value
    digit (byte / 16) :: digit (byte % 16) :: hexDigits rest

/-- The fixed words of an assembly identity as bytes: `, Version=`, `, Culture=`, `neutral`,
    `, PublicKeyToken=` and `null`. They are byte lists, not strings, so the kernel never
    evaluates a string literal to read an identity. -/
def versionMarker : List Nat := [44, 32, 86, 101, 114, 115, 105, 111, 110, 61]
def cultureMarker : List Nat := [44, 32, 67, 117, 108, 116, 117, 114, 101, 61]
def neutralCulture : List Nat := [110, 101, 117, 116, 114, 97, 108]
def tokenMarker : List Nat :=
  [44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101, 110, 61]
def nullToken : List Nat := [110, 117, 108, 108]

/-- The text of an assembly name as Cecil writes it:
    `Name, Version=a.b.c.d, Culture=culture, PublicKeyToken=token`. -/
def assemblySpelling (name : List Nat) (major minor build revision : Nat)
    (culture token : List Nat) :
    List Nat :=
  name ++ versionMarker ++ decimalDigits 5 major ++ [46] ++ decimalDigits 5 minor ++ [46] ++
    decimalDigits 5 build ++ [46] ++ decimalDigits 5 revision ++ cultureMarker ++
    (if culture.isEmpty then neutralCulture else culture) ++ tokenMarker ++ token

/-- The `AssemblyRef` row's identity. A flag other than 0 means a full public key (whose token
    needs SHA-1) or a retargetable reference (which Cecil spells apart): both are unsupported. -/
def MetadataIndex.assemblyRefIdentity (index : MetadataIndex) (token : Nat) :
    Except MetadataError (List Nat) := do
  let row ← index.assemblyRef token
  if row.flags != 0 then throw (.unsupportedAssemblyRef token)
  let name ← index.string row.name
  let culture ← index.string row.culture
  let publicToken ← index.blob row.publicKeyOrToken
  let spelled ←
    if publicToken.isEmpty then pure nullToken
    else if publicToken.length == 8 then pure (hexDigits publicToken)
    else throw (.unsupportedAssemblyRef token)
  .ok (assemblySpelling name row.major row.minor row.build row.revision culture spelled)

/-- The identity an `Assembly` row spells, with the key token the assembly states. A key token is
    the SHA-1 of the public key, which the kernel does not compute: it is the stated token when
    the row has a key, and the stated token must then be sixteen lowercase hexadecimal digits;
    with no key the identity says `null` and no token is stated. -/
def AssemblyMetadata.spelling (assembly : AssemblyMetadata) :
    Except MetadataError (List Nat) := do
  let header ← decodeTableHeader assembly.tableHeader
  let strings ← indexEntries assembly.strings
  let blobs ← indexEntries assembly.blobs
  let widths ← match columnWidths header.widths Table.assembly with
    | some widths => .ok widths
    | none => .error (.unsupportedTable (tokenOf Table.assembly 1))
  if assembly.assemblyRow.length != widths.sum then
    throw (.rowLength (tokenOf Table.assembly 1) widths.sum assembly.assemblyRow.length)
  let some columns := splitColumns widths assembly.assemblyRow
    | throw (.unsupportedTable (tokenOf Table.assembly 1))
  let [_, major, minor, build, revision, _, key, name, culture] := columns
    | throw (.unsupportedTable (tokenOf Table.assembly 1))
  let publicKey ← blobBytes blobs key
  let tokenBytes := assembly.keyToken
  let spelled ←
    if publicKey.isEmpty then
      if tokenBytes.isEmpty then pure nullToken else throw .identityMismatch
    else if tokenBytes.length == 16 && tokenBytes.all (fun digit =>
        (48 ≤ digit && digit ≤ 57) || (97 ≤ digit && digit ≤ 102)) then pure tokenBytes
    else throw .identityMismatch
  .ok (assemblySpelling (← stringBytes strings name) major minor build revision
    (← stringBytes strings culture) spelled)

/-- `identity` is the text the assembly's `Assembly` row spells, and it is the identity the
    assembly states. It costs the same for every method of the assembly, so an extraction proves
    it once and each method's evidence names the bytes. The second part is an equation between a
    string and bytes, so it is proved with `cil_kernel_rfl` and never evaluates the string. -/
abbrev AssemblyIdentified (assembly : AssemblyMetadata) (identity : List Nat) : Prop :=
  assembly.spelling.toOption = some identity ∧ spelled? identity = some assembly.identity

/-- The running instance field count before each of up to `count` consecutive `Field` rows from
    `row`, as far as the rows are carried, with the total and whether every row was carried. A
    field is static when bit 4 of the first flag byte is set. -/
private def fieldCounts (index : MetadataIndex) :
    Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat) × Nat × Bool
  | 0, _, instances, found => (found, instances, true)
  | count + 1, row, instances, found =>
    match index.rows.find? (tokenOf Table.field row) with
    | none => (found, instances, false)
    | some bytes =>
      let isStatic := bytes.getD 0 0 / 0x10 % 2 == 1
      fieldCounts index count (row + 1) (if isStatic then instances else instances + 1)
        ((tokenOf Table.field row, instances) :: found)

/-- The instance field counts of one carried type whose next type's row is carried: each count
    before a field, latest first, over the carried rows from the type's first field, which may be a
    prefix of its fields; and the total, only when every field is carried. -/
private def typeCounts (index : MetadataIndex) (token : Nat) :
    Option (List (Nat × Nat) × Option Nat) :=
  match index.typeDef token with
  | .error _ => none
  | .ok row =>
    let stop :=
      if tokenRow token == index.header.rows Table.typeDef then
        some (index.header.rows Table.field + 1)
      else (match index.typeDef (token + 1) with
        | .ok next => some next.fieldList
        | .error _ => none)
    match stop with
    | none => none
    | some stop =>
      let (found, instances, complete) := fieldCounts index (stop - row.fieldList) row.fieldList 0 []
      some (found, if complete then some instances else none)

/-- The instance field counts of every carried type, as entries in ascending key order. -/
private def fieldCountEntries (index : MetadataIndex) :
    Except MetadataError (SearchTree Nat × SearchTree Nat) :=
  let (before, total) := index.rows.toList.foldl (fun (before, total) (token, _) =>
    if metadataTableOf token == Table.typeDef then
      match typeCounts index token with
      | some (found, some count) => (found ++ before, (token, count) :: total)
      | some (found, none) => (found ++ before, total)
      | none => (before, total)
    else (before, total)) ([], [])
  do .ok (← SearchTree.ofEntries before.reverse, ← SearchTree.ofEntries total.reverse)

/-- Insert links into a list of entries keyed by kind and source, refusing a second link for one
    key. -/
private def linkEntries : List MetadataLink → List (Nat × (Nat × Nat))
  | [] => []
  | link :: rest => (link.kind * 0x100000000 + link.source, (link.slice, link.target)) :: linkEntries rest

/-- The lookup structures of a slice, built from its bytes: its entries as trees, and the instance
    field counts of its carried types. -/
def MetadataSlice.tables (slice : MetadataSlice) : Except MetadataError IndexTables := do
  let header ← decodeTableHeader slice.assembly.tableHeader
  let rows ← indexEntries slice.rows
  let strings ← indexEntries slice.strings
  let blobs ← indexEntries slice.blobs
  let userStrings ← indexEntries slice.userStrings
  let links ← SearchTree.ofEntries (linkEntries slice.links)
  let bare : IndexTables :=
    { rows := rows
      strings := strings
      blobs := blobs
      userStrings := userStrings
      links := links
      instanceBefore := .leaf
      instanceTotal := .leaf }
  let (before, total) ←
    fieldCountEntries { toIndexTables := bare, header := header, corlib := slice.corlib, identity := [] }
  .ok { bare with instanceBefore := before, instanceTotal := total }

/-- The index of a slice given its tables and the identity its assembly spells, which an
    `AssemblyIdentified` fact ties to the assembly's bytes and to the string it states. Cheap:
    independent of the number of rows. -/
def MetadataSlice.indexWith (slice : MetadataSlice) (tables : IndexTables)
    (identity : List Nat) : Except MetadataError MetadataIndex := do
  let header ← decodeTableHeader slice.assembly.tableHeader
  .ok { toIndexTables := tables, header := header, corlib := slice.corlib, identity := identity }

/-- Build the index of a slice from its bytes alone, refusing an identity the `Assembly` row does
    not spell as the assembly states it. -/
def MetadataSlice.index (slice : MetadataSlice) : Except MetadataError MetadataIndex := do
  let identity ← slice.assembly.spelling
  if spelled? identity != some slice.assembly.identity then throw .identityMismatch
  slice.indexWith (← slice.tables) identity

/-- The slices of one method's metadata, its own first. -/
def MethodMetadata.slices (metadata : MethodMetadata) : List MetadataSlice :=
  metadata.own :: metadata.others

/-- Each assembly spells the identity listed at its position. -/
def AllIdentified : List AssemblyMetadata → List (List Nat) → Prop
  | [], [] => True
  | assembly :: assemblies, identity :: identities =>
    AssemblyIdentified assembly identity ∧ AllIdentified assemblies identities
  | _, _ => False

instance (assembly : AssemblyMetadata) (identity : List Nat) :
    Decidable (AssemblyIdentified assembly identity) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance decideAllIdentified : (assemblies : List AssemblyMetadata) →
    (identities : List (List Nat)) → Decidable (AllIdentified assemblies identities)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse fun impossible => impossible
  | _ :: _, [] => isFalse fun impossible => impossible
  | assembly :: assemblies, identity :: identities =>
    haveI := decideAllIdentified assemblies identities
    inferInstanceAs (Decidable (AssemblyIdentified assembly identity ∧
      AllIdentified assemblies identities))

theorem AllIdentified.nil : AllIdentified [] [] := trivial

theorem AllIdentified.cons {assembly : AssemblyMetadata} {identity : List Nat}
    {assemblies : List AssemblyMetadata} {identities : List (List Nat)}
    (first : AssemblyIdentified assembly identity) (rest : AllIdentified assemblies identities) :
    AllIdentified (assembly :: assemblies) (identity :: identities) := ⟨first, rest⟩

/-- Each slice's assembly spells the identity listed for it, in the slices' order. -/
abbrev AssembliesIdentified (metadata : MethodMetadata) (identities : List (List Nat)) : Prop :=
  AllIdentified (metadata.slices.map (·.assembly)) identities

/-- The tables of the slices of one method's metadata, its own first. -/
def MethodMetadata.tables (metadata : MethodMetadata) : Except MetadataError (List IndexTables) :=
  metadata.slices.mapM MetadataSlice.tables

/-- Whether `tables` are what the decoder builds from the metadata's bytes. Only the kernel
    decides it, like `bodyMatches`. -/
@[irreducible] def tablesMatch (metadata : MethodMetadata) (tables : List IndexTables) : Bool :=
  match metadata.tables with
  | .ok built => built == tables
  | .error _ => false

end CIL.Extraction
