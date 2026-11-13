import StrictBinding.Image

/-!
# PE container

Decodes the parts of a PE file that locate CLI metadata: the DOS header, the PE and optional
headers, the section table, the CLI header, the metadata root and its stream headers. Every
offset is a file offset computed from the image constant itself, so a body or row claimed at a
relative virtual address is read where the section table maps that address.

`mapRva` follows the rule the extractor applies to static data: exactly one section holds the
address, and the bytes stay inside both the section's raw data and its mapped size.
-/

namespace StrictBinding

/-- A section header: its mapped extent and where its raw data sits in the file. -/
structure Section where
  virtualSize : Nat
  virtualAddress : Nat
  rawSize : Nat
  rawPointer : Nat

/-- A metadata stream: the file offset of its first byte and its size. -/
structure Stream where
  start : Nat
  size : Nat

/-- The positions in the file that locate metadata. Streams the file lacks have size zero. -/
structure PeLayout where
  sections : List Section
  /-- The file offset of the metadata root. -/
  metadata : Nat
  metadataSize : Nat
  /-- The `#~` stream of tables. -/
  tables : Stream
  strings : Stream
  userStrings : Stream
  guids : Stream
  blobs : Stream

/-- The streams of a metadata root as they are read: each at most once. -/
structure StreamSet where
  tables : Option Stream := none
  strings : Option Stream := none
  userStrings : Option Stream := none
  guids : Option Stream := none
  blobs : Option Stream := none

/-- The file holds this relative virtual address in the section's extent. -/
def Section.contains (header : Section) (rva : Nat) : Bool :=
  header.virtualAddress <= rva &&
    rva < header.virtualAddress + Nat.max header.virtualSize header.rawSize

/-- The file offset of `count` bytes at a relative virtual address: exactly one section holds the
    address, and the bytes end inside its raw data and its mapped size. -/
def mapRva (sections : List Section) (rva count : Nat) : Except AuditError Nat :=
  match sections.filter (·.contains rva) with
  | [header] =>
    let rawEnd := header.virtualAddress + header.rawSize
    let mappedEnd :=
      if header.virtualSize == 0 then rawEnd else header.virtualAddress + header.virtualSize
    if rva + count <= Nat.min rawEnd mappedEnd then
      .ok (header.rawPointer + (rva - header.virtualAddress))
    else .error (.pe (.unmappedRva rva count))
  | [] => .error (.pe (.unmappedRva rva count))
  | _ => .error (.pe (.ambiguousRva rva))

/-- The bytes of a section header: sizes and pointers at offsets 8 to 20. -/
def sectionHeaderBytes : Nat := 40

/-- The `count` section headers from `offset`. -/
def readSections (view : ImageView) (offset : Nat) : Nat → Except AuditError (List Section)
  | 0 => pure []
  | count + 1 => do
    let virtualSize ← view.u (offset + 8) 4
    let virtualAddress ← view.u (offset + 12) 4
    let rawSize ← view.u (offset + 16) 4
    let rawPointer ← view.u (offset + 20) 4
    let rest ← readSections view (offset + sectionHeaderBytes) count
    pure ({ virtualSize, virtualAddress, rawSize, rawPointer } :: rest)

/-- The longest stream name, with its terminator, the metadata format allows. -/
def streamNameBytes : Nat := 32

/-- The bytes of a NUL-terminated name at `offset`, without the terminator; `missing` is the error
    when no terminator ends the name within the allowed length. -/
def readName (view : ImageView) (offset : Nat) (missing : AuditError) :
    Nat → Except AuditError (List Nat)
  | 0 => throw missing
  | fuel + 1 => do
    let byte ← view.u offset 1
    if byte == 0 then pure []
    else
      let rest ← readName view (offset + 1) missing fuel
      pure (byte :: rest)

/-- Records a stream under its name once; a repeated or unknown name is rejected. -/
def StreamSet.add (streams : StreamSet) (name : List Nat) (stream : Stream) :
    Except AuditError StreamSet :=
  match name with
  | [0x23, 0x7E] =>
    if streams.tables.isSome then throw (.pe .badStream)
    else pure { streams with tables := some stream }
  | [0x23, 0x53, 0x74, 0x72, 0x69, 0x6E, 0x67, 0x73] =>
    if streams.strings.isSome then throw (.pe .badStream)
    else pure { streams with strings := some stream }
  | [0x23, 0x55, 0x53] =>
    if streams.userStrings.isSome then throw (.pe .badStream)
    else pure { streams with userStrings := some stream }
  | [0x23, 0x47, 0x55, 0x49, 0x44] =>
    if streams.guids.isSome then throw (.pe .badStream)
    else pure { streams with guids := some stream }
  | [0x23, 0x42, 0x6C, 0x6F, 0x62] =>
    if streams.blobs.isSome then throw (.pe .badStream)
    else pure { streams with blobs := some stream }
  | _ => throw (.pe .badStream)

/-- The stream headers from `offset`: each stream must lie inside the `metadataSize` bytes of the
    root that starts at `root`. -/
def readStreams (view : ImageView) (root metadataSize : Nat) :
    Nat → Nat → StreamSet → Except AuditError StreamSet
  | 0, _, streams => pure streams
  | count + 1, offset, streams => do
    let streamOffset ← view.u offset 4
    let size ← view.u (offset + 4) 4
    let name ← readName view (offset + 8) (.pe .badMetadataRoot) streamNameBytes
    if streamOffset + size > metadataSize then throw (.pe .badMetadataRoot)
    let streams ← streams.add name { start := root + streamOffset, size }
    let headerBytes := 8 + (name.length + 4) / 4 * 4
    readStreams view root metadataSize count (offset + headerBytes) streams

/-- The empty stream of a heap the file lacks. -/
def Stream.absent : Stream := { start := 0, size := 0 }

/-- The offset of the optional header's data directories: 96 bytes into a PE32 header and 112 into
    a PE32+ header. -/
def directoriesOffset (optional magic : Nat) : Except AuditError Nat :=
  if magic == 0x10B then pure (optional + 96)
  else if magic == 0x20B then pure (optional + 112)
  else throw (.pe (.badMagic magic))

/-- The CLI header's data directory is the fifteenth of sixteen, eight bytes each. -/
def cliDirectoryIndex : Nat := 14

/-- The bytes of a CLI header. -/
def cliHeaderBytes : Nat := 72

/-- The CLI header and metadata root of an image, located through the section table. -/
def decodePe (view : ImageView) : Except AuditError PeLayout := do
  if (← view.u 0 2) != 0x5A4D then throw (.pe .notDos)
  let pe ← view.u 0x3C 4
  if (← view.u pe 4) != 0x4550 then throw (.pe (.badSignature pe))
  let sectionCount ← view.u (pe + 6) 2
  let optionalSize ← view.u (pe + 20) 2
  let optional := pe + 24
  let directories ← directoriesOffset optional (← view.u optional 2)
  let directoryEnd := directories + 8 * (cliDirectoryIndex + 1)
  let directoryCount ← view.u (directories - 4) 4
  if directoryCount <= cliDirectoryIndex || directoryEnd > optional + optionalSize then
    throw (.pe .noCliHeader)
  let sections ← readSections view (optional + optionalSize) sectionCount
  let cliEntry := directories + 8 * cliDirectoryIndex
  let cli ← mapRva sections (← view.u cliEntry 4) cliHeaderBytes
  if (← view.u (cliEntry + 4) 4) < cliHeaderBytes || (← view.u cli 4) != cliHeaderBytes then
    throw (.pe .badCliHeader)
  let metadataSize ← view.u (cli + 12) 4
  let metadata ← mapRva sections (← view.u (cli + 8) 4) metadataSize
  if (← view.u metadata 4) != 0x424A5342 then throw (.pe .badMetadataRoot)
  let versionLength ← view.u (metadata + 12) 4
  if versionLength % 4 != 0 || versionLength > 255 then throw (.pe .badMetadataRoot)
  let streamCount ← view.u (metadata + 18 + versionLength) 2
  let streams ← readStreams view metadata metadataSize streamCount
    (metadata + 20 + versionLength) {}
  let some tables := streams.tables | throw (.pe .badMetadataRoot)
  pure { sections, metadata, metadataSize, tables,
         strings := streams.strings.getD Stream.absent,
         userStrings := streams.userStrings.getD Stream.absent,
         guids := streams.guids.getD Stream.absent, blobs := streams.blobs.getD Stream.absent }

end StrictBinding
