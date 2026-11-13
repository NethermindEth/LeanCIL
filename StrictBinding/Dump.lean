import StrictBinding.Identity

/-!
# Image facts

What the audit decodes from an image, as data: the sections, the metadata root, the streams, the
position and size of every table, the file offset of each MethodDef row's body and the assembly
identity. `facts` lists them in a fixed order and `Fact.line` prints one per line, so an
independent reader of the same file can be compared with the audit's own decoding.
-/

namespace StrictBinding

/-- One decoded fact about an image. Offsets are file offsets. -/
inductive Fact where
  /-- A section header: mapped size, relative virtual address, raw size and raw data offset. -/
  | sectionHeader (virtualSize virtualAddress rawSize rawPointer : Nat)
  /-- The metadata root: its offset and size. -/
  | metadata (offset size : Nat)
  /-- A nonempty stream: its name, offset and size. -/
  | stream (name : String) (offset size : Nat)
  /-- The heap size flags of the table stream. -/
  | heapSizes (flags : Nat)
  /-- A nonempty table: its number, row count, row size and the offset of its first row. -/
  | table (table count size offset : Nat)
  /-- A MethodDef row with a body: its row number, relative virtual address and file offset. -/
  | method (row rva offset : Nat)
  /-- The assembly identity, as code points. -/
  | identity (codePoints : List Nat)
  deriving DecidableEq, Repr

/-- The line that describes a fact: its kind, then its numbers, or the identity as text. -/
def Fact.line : Fact → String
  | .sectionHeader size address rawSize rawPointer =>
    s!"section {size} {address} {rawSize} {rawPointer}"
  | .metadata offset size => s!"metadata {offset} {size}"
  | .stream name offset size => s!"stream {name} {offset} {size}"
  | .heapSizes flags => s!"heapSizes {flags}"
  | .table number count size offset => s!"table {number} {count} {size} {offset}"
  | .method row rva offset => s!"method {row} {rva} {offset}"
  | .identity points => s!"identity {String.ofList (points.map Char.ofNat)}"

/-- The fact for a stream the file has; none for an absent one. -/
def streamFacts (name : String) (stream : Stream) : List Fact :=
  if stream.size == 0 then [] else [.stream name stream.start stream.size]

/-- The file offset of every MethodDef row that has a body, from its own relative virtual
    address. -/
def methodFacts (view : ImageView) (layout : MetadataLayout) : Except AuditError (List Fact) :=
  (List.range (layout.rowCount 0x06)).filterMapM fun index => do
    let rva ← layout.cell view (tokenOf 0x06 (index + 1)) 0
    if rva == 0 then pure none
    else pure (some (.method (index + 1) rva (← mapRva layout.pe.sections rva 1)))

/-- Everything the audit decodes from an image's container and tables. -/
def facts (image : ImageBytes) : Except AuditError (List Fact) := do
  let view ← ImageView.ofImage image
  let layout ← decodeMetadata view
  let pe := layout.pe
  let sections := pe.sections.map fun header =>
    .sectionHeader header.virtualSize header.virtualAddress header.rawSize header.rawPointer
  let streams := streamFacts "tables" pe.tables ++ streamFacts "strings" pe.strings ++
    streamFacts "userStrings" pe.userStrings ++ streamFacts "guids" pe.guids ++
    streamFacts "blobs" pe.blobs
  let tables := layout.tables.map fun rows => .table rows.table rows.count rows.size rows.start
  pure (sections ++ [.metadata pe.metadata pe.metadataSize] ++ streams ++
    [.heapSizes layout.heapSizes] ++ tables ++ (← methodFacts view layout) ++
    [.identity (← assemblyIdentity view layout)])

/-- The lines that describe an image, or the reason it does not decode. -/
def describe (image : ImageBytes) : Except AuditError (List String) :=
  (facts image).map (·.map Fact.line)

end StrictBinding
