import StrictBinding.Bind
import StrictBinding.Reads
import CIL.Extraction.MetadataBytes

/-!
# Carried metadata bound to images

An extraction carries, for each pinned assembly, its table stream header, the header decoded,
its `Assembly` row and the heap entries that row names (`CIL.Extraction.AssemblyMetadata`), and for
each method the rows and heap entries its tokens reach (`CIL.Extraction.MetadataSlice`). A carried
row does not hold the image's `#Strings` and `#Blob` offsets: each heap column holds a key, 0 for
offset 0, the rank of the entry among the entries carried, or `omittedKey` for an entry the
extraction does not carry; and a carried MethodDef row holds 0 for its RVA. `RowAt`, `StringAt`
and `SizedAt` state that carried bytes are the image's under such a numbering. `RowsMatch` states
it for carried rows and entries under one numbering per heap, which also needs an entry for every
key of the rows other than 0 and `omittedKey`, and a row cell holding the key of every entry;
`AssemblyMatches` adds the header for an assembly block. `rowsBound` and `assemblyBound` check
them, taking every position and length they compare from the image itself, with a fixed number
of image reads per row and per entry and one sort per heap; `rowsMatch_of_rowsBound` and
`assemblyMatches_of_assemblyBound` prove that their success means the propositions.
-/

namespace StrictBinding

open CIL.Extraction (AssemblyMetadata ByteEntry decodeTableHeader stringsHeap blobHeap sortPairs
  sortBy_perm pairBefore)
open CIL.Safety (except_bind_ok)

/-! ## Heap numbering -/

/-- The key a carried row writes for a nonzero image offset whose entry it does not carry: the
    largest value of a column of `width` bytes. -/
def omittedKey (width : Nat) : Nat := 2 ^ (8 * width) - 1

/-- The key a carried column of `width` bytes holds for an image offset under `keyOf`. -/
def canonicalKey (keyOf : Nat → Option Nat) (width offset : Nat) : Nat :=
  if offset == 0 then 0 else (keyOf offset).getD (omittedKey width)

/-- A numbering of image offsets: offset 0 has no key, no two offsets share a key, and every key
    is above 0 and below `omittedKey width`. -/
def Numbering (keyOf : Nat → Option Nat) (width : Nat) : Prop :=
  keyOf 0 = none ∧
    (∀ first second key, keyOf first = some key → keyOf second = some key → first = second) ∧
    ∀ offset key, keyOf offset = some key → 0 < key ∧ key < omittedKey width

/-- `key` names `offset`: key 0 names offset 0, and any other key names the offset the
    numbering gives it. -/
def Names (keyOf : Nat → Option Nat) (key offset : Nat) : Prop :=
  (key = 0 ∧ offset = 0) ∨ keyOf offset = some key

/-- The bytes of a `#Strings` index in the image's rows. -/
def stringWidth (image : PreparedImage) : Nat :=
  columnWidth image.layout.heapSizes image.layout.rowCount .string

/-- The bytes of a `#Blob` index in the image's rows. -/
def blobWidth (image : PreparedImage) : Nat :=
  columnWidth image.layout.heapSizes image.layout.rowCount .blob

/-! ## Rows -/

/-- The token of the one row of the `Assembly` table. -/
def assemblyToken : Nat := tokenOf 0x20 1

/-- The little-endian value of bytes. -/
def littleValue (bytes : List Nat) : Nat := bytes.foldr (fun byte value => byte + 256 * value) 0

/-- The `width` little-endian bytes of a value. -/
def littleBytes : Nat → Nat → List Nat
  | 0, _ => []
  | width + 1, value => value % 256 :: littleBytes width (value / 256)

/-- The heap a column indexes, when it indexes `#Strings` or `#Blob`. -/
def Column.heap? : Column → Option Nat
  | .string => some stringsHeap
  | .blob => some blobHeap
  | _ => none

/-- The image row with the RVA of a MethodDef row zeroed, as a carried row holds it: where a
    method's body is placed changes with the bodies before it. -/
def maskRva (image : PreparedImage) (token : Nat) (row : List Nat) : List Nat :=
  if token / 2 ^ 24 == CIL.Extraction.Table.methodDef then
    row.take image.rvaColumn.1 ++
      (row.drop image.rvaColumn.1 |>.take image.rvaColumn.2).map (fun _ => 0) ++
      row.drop (image.rvaColumn.1 + image.rvaColumn.2)
  else row

/-- A cell as a carried row holds it: a heap offset becomes its key, any other cell is kept. -/
def canonicalCell (strings blobs : Nat → Option Nat) (column : Column) (cell : List Nat) :
    List Nat :=
  match column with
  | .string => littleBytes cell.length (canonicalKey strings cell.length (littleValue cell))
  | .blob => littleBytes cell.length (canonicalKey blobs cell.length (littleValue cell))
  | _ => cell

/-- The cells of a row of these columns, each as a carried row holds it; the row must have
    exactly the columns' widths. -/
def canonicalCells (strings blobs : Nat → Option Nat) (token : Nat) :
    List ColumnPlace → List Nat → Except AuditError (List Nat)
  | [], [] => pure []
  | [], _ :: _ => throw (.rowMismatch token)
  | place :: rest, row => do
    let cell := row.take place.width
    if cell.length != place.width then throw (.rowMismatch token)
    else
      let tail ← canonicalCells strings blobs token rest (row.drop place.width)
      pure (canonicalCell strings blobs place.column cell ++ tail)

/-- The image row of `token` as a carried row holds it, under the numberings `strings` and
    `blobs`, with a MethodDef row's RVA zeroed. -/
def canonicalRow (image : PreparedImage) (strings blobs : Nat → Option Nat) (token : Nat)
    (row : List Nat) : Except AuditError (List Nat) :=
  match image.columnsOf (token / 2 ^ 24) with
  | some columns => canonicalCells strings blobs token columns (maskRva image token row)
  | none => throw (.tokenOutOfScope token)

/-- The carried row is the image row of its token under the numberings `strings` and `blobs`. -/
def RowAt (image : PreparedImage) (strings blobs : Nat → Option Nat) (token : Nat)
    (bytes : List Nat) : Prop :=
  ∃ offset row, image.layout.rowAt token = .ok (offset, bytes.length) ∧
    image.view.bytes offset bytes.length = .ok row ∧
    canonicalRow image strings blobs token row = .ok bytes

/-! ## Heap entries -/

/-- The image's NUL-terminated `#Strings` entry at `offset`, inside the heap. -/
def StringAt (image : PreparedImage) (offset : Nat) (bytes : List Nat) : Prop :=
  ∃ text, bytes = text ++ [0] ∧ 0 ∉ text ∧
    offset + bytes.length ≤ image.layout.pe.strings.size ∧
    image.view.bytes (image.layout.pe.strings.start + offset) bytes.length = .ok bytes

/-- The image's length prefix and exactly its payload at `offset`, inside `heap`. -/
def SizedAt (image : PreparedImage) (heap : Stream) (offset : Nat) (bytes : List Nat) : Prop :=
  ∃ prefixBytes length, blobPrefix image.view (heap.start + offset) = .ok (prefixBytes, length) ∧
    bytes.length = prefixBytes + length ∧ offset + bytes.length ≤ heap.size ∧
    image.view.bytes (heap.start + offset) bytes.length = .ok bytes

/-! ## Rows and entries under one numbering -/

/-- The keys the cells of `heap` hold in a carried row of these columns. -/
def rowKeys (heap : Nat) : List ColumnPlace → List Nat → List Nat
  | [], _ => []
  | place :: rest, row =>
    let tail := rowKeys heap rest (row.drop place.width)
    if place.column.heap? == some heap then littleValue (row.take place.width) :: tail else tail

/-- Every key the numbering gives is held by a cell of `heap` in a carried row, so a carried
    entry cannot be named by a key no row holds. -/
def Held (image : PreparedImage) (heap : Nat) (rows : List ByteEntry)
    (keyOf : Nat → Option Nat) : Prop :=
  ∀ offset key, keyOf offset = some key → ∃ row ∈ rows, ∃ columns,
    image.columnsOf (row.1 / 2 ^ 24) = some columns ∧ key ∈ rowKeys heap columns row.2

/-- Every key the numbering gives names a carried entry, so a carried row holds no key other
    than 0 and `omittedKey` without the entry it ranks. -/
def Covered (keyOf : Nat → Option Nat) (entries : List ByteEntry) : Prop :=
  ∀ offset key, keyOf offset = some key → ∃ entry ∈ entries, entry.1 = key

/-- The carried rows and `#Strings` and `#Blob` entries are the image's under one numbering per
    heap: each row is the image row of its token, each entry the image's entry at the offset its
    key names, every key of the rows other than 0 and `omittedKey` has an entry, and a row cell
    holds the key of every entry other than 0. -/
def RowsMatch (image : PreparedImage) (rows strings blobs : List ByteEntry) : Prop :=
  ∃ stringKeys blobKeys, Numbering stringKeys (stringWidth image) ∧
    Numbering blobKeys (blobWidth image) ∧
    (∀ row ∈ rows, RowAt image stringKeys blobKeys row.1 row.2) ∧
    (∀ entry ∈ strings, ∃ offset, Names stringKeys entry.1 offset ∧
      StringAt image offset entry.2) ∧
    (∀ entry ∈ blobs, ∃ offset, Names blobKeys entry.1 offset ∧
      SizedAt image image.layout.pe.blobs offset entry.2) ∧
    Covered stringKeys strings ∧ Covered blobKeys blobs ∧
    Held image stringsHeap rows stringKeys ∧ Held image blobHeap rows blobKeys

/-! ## The assembly block -/

/-- The offset of the `Valid` mask in a table stream. -/
def validMaskOffset : Nat := 8

/-- The bytes of the `Valid` mask. -/
def validMaskBytes : Nat := 8

/-- The bytes of each row count in a table stream header. -/
def rowCountBytes : Nat := 4

/-- The bytes of a table stream header whose `Valid` mask is `valid`: the fixed fields, then a
    row count for every table the mask marks present, including tables without rows. -/
def tableHeaderLength (valid : Nat) : Nat :=
  tableHeaderBytes + rowCountBytes *
    ((List.range (8 * validMaskBytes)).filter fun table => valid / 2 ^ table % 2 == 1).length

/-- The carried header is the image's `#~` stream from its reserved word through the last row
    count its own `Valid` mask declares. -/
def HeaderAt (image : PreparedImage) (tableHeader : List Nat) : Prop :=
  ∃ valid, image.view.u (image.layout.pe.tables.start + validMaskOffset) validMaskBytes =
      .ok valid ∧ tableHeader.length = tableHeaderLength valid ∧
    image.view.bytes image.layout.pe.tables.start tableHeader.length = .ok tableHeader

/-- The assembly block is the image's: its header bytes, the header they decode to, and its
    `Assembly` row and entries under a numbering of their own. -/
def AssemblyMatches (image : PreparedImage) (assembly : AssemblyMetadata) : Prop :=
  HeaderAt image assembly.tableHeader ∧
    decodeTableHeader assembly.tableHeader = .ok assembly.header ∧
    RowsMatch image [(assemblyToken, assembly.assemblyRow)] assembly.strings assembly.blobs

/-! ## Checks -/

/-- The header bytes are the image's through its last row count, and decode to the carried
    decoded header. -/
def headerBound (image : PreparedImage) (assembly : AssemblyMetadata) :
    Except AuditError Unit := do
  let tables := image.layout.pe.tables
  let valid ← image.view.u (tables.start + validMaskOffset) validMaskBytes
  if assembly.tableHeader.length != tableHeaderLength valid then
    throw (.headerMismatch image.identity)
  else
    let found ← image.view.hasBytesAt tables.start assembly.tableHeader
    if found && (decodeTableHeader assembly.tableHeader).toOption == some assembly.header then
      pure ()
    else throw (.headerMismatch image.identity)

/-- The `#Strings` and `#Blob` cells of carried rows that name a nonzero image offset, as
    (image offset, key) with key 0 for a cell holding `omittedKey`. -/
abbrev HeapCells := List (Nat × Nat) × List (Nat × Nat)

/-- The key a heap cell of `width` bytes contributes to `HeapCells`: 0 for `omittedKey`. -/
def cellKey (width key : Nat) : Nat := if key == omittedKey width then 0 else key

/-- A carried heap cell against the image offset its image cell holds: the cell must be `width`
    bytes, hold 0 exactly for offset 0, and gives the (offset, key) of a nonzero offset. -/
def heapCell (token width offset : Nat) (carried : List Nat) :
    Except AuditError (Option (Nat × Nat)) :=
  if carried != littleBytes width (littleValue carried) ||
      (offset == 0) != (littleValue carried == 0) then throw (.rowMismatch token)
  else if offset == 0 then pure none
  else pure (some (offset, cellKey width (littleValue carried)))

/-- A carried row against the image row of its token, cell by cell: a heap cell gives its
    (offset, key), any other cell must be the image's. -/
def rowCells (token : Nat) : List ColumnPlace → List Nat → List Nat → Except AuditError HeapCells
  | [], imageRow, carried =>
    if imageRow.isEmpty && carried.isEmpty then pure ([], []) else throw (.rowMismatch token)
  | place :: rest, imageRow, carried =>
    let imageCell := imageRow.take place.width
    let carriedCell := carried.take place.width
    if imageCell.length != place.width then throw (.rowMismatch token)
    else do
      let tail ← rowCells token rest (imageRow.drop place.width) (carried.drop place.width)
      match place.column with
      | .string => do
        let cell ← heapCell token place.width (littleValue imageCell) carriedCell
        pure (cell.toList ++ tail.1, tail.2)
      | .blob => do
        let cell ← heapCell token place.width (littleValue imageCell) carriedCell
        pure (tail.1, cell.toList ++ tail.2)
      | _ => if carriedCell == imageCell then pure tail else throw (.rowMismatch token)

/-- The heap cells of a carried row, checked against one read of the image row its token
    names. -/
def rowCellsAt (image : PreparedImage) (token : Nat) (carried : List Nat) :
    Except AuditError HeapCells := do
  let place ← image.layout.rowAt token
  if carried.length != place.2 then throw (.rowMismatch token)
  else
    let value ← image.view.slice place.1 place.2
    match image.columnsOf (token / 2 ^ 24) with
    | none => throw (.tokenOutOfScope token)
    | some columns =>
      rowCells token columns (maskRva image token (valueBytes place.2 value)) carried

/-- The heap cells of every carried row. -/
def rowsCells (image : PreparedImage) : List ByteEntry → Except AuditError HeapCells
  | [] => pure ([], [])
  | row :: rest => do
    let here ← rowCellsAt image row.1 row.2
    let later ← rowsCells image rest
    pure (here.1 ++ later.1, here.2 ++ later.2)

/-- Sorted pairs whose equal first components come only in equal pairs, without the repeats;
    `keyOf` picks the key an error reports. -/
def distinctPairs (heap : Nat) (keyOf : Nat × Nat → Nat) :
    List (Nat × Nat) → Except AuditError (List (Nat × Nat))
  | [] => pure []
  | first :: rest => do
    let later ← distinctPairs heap keyOf rest
    match rest with
    | [] => pure [first]
    | second :: _ =>
      if first.1 < second.1 then pure (first :: later)
      else if first == second then pure later
      else throw (.heapNumbering heap (keyOf second))

/-- Each image offset of the cells has one key, the omitted key 0 included. -/
def offsetsBound (heap : Nat) (cells : List (Nat × Nat)) : Except AuditError Unit := do
  let _ ← distinctPairs heap (·.2) (sortPairs cells)

/-- The (key, offset) of each cell whose key is not omitted. -/
def numberedCells (cells : List (Nat × Nat)) : List (Nat × Nat) :=
  (cells.filter (·.2 != 0)).map fun cell => (cell.2, cell.1)

/-- The numbered (key, offset) pairs ascending by key, each key once: every key is below the
    marker of `width` bytes and has one offset. -/
def keysBound (heap width : Nat) (cells : List (Nat × Nat)) :
    Except AuditError (List (Nat × Nat)) :=
  match (numberedCells cells).find? (omittedKey width ≤ ·.1) with
  | some pair => throw (.heapNumbering heap pair.1)
  | none => distinctPairs heap (·.1) (sortPairs (numberedCells cells))

/-- The carried entries ascend strictly by key, as the slice's lookup trees need. -/
def ascendingBound (heap : Nat) : List ByteEntry → Except AuditError Unit
  | first :: second :: rest =>
    if first.1 < second.1 then ascendingBound heap (second :: rest)
    else throw (.heapNumbering heap second.1)
  | _ => pure ()

/-- The entry is found at `offset`. -/
def entryBound (heap : Nat) (found : Nat → List Nat → Except AuditError Bool) (offset : Nat)
    (entry : ByteEntry) : Except AuditError Unit := do
  if (← found offset entry.2) then pure () else throw (.heapMismatch heap entry.1)

/-- The numbered pairs and the entries of `heap`, both ascending by key, joined: an entry with key
    0 is found at offset 0, every other entry at the offset of the pair with its key, and every
    pair has an entry. -/
def joinBound (heap : Nat) (found : Nat → List Nat → Except AuditError Bool) :
    List (Nat × Nat) → List ByteEntry → Except AuditError Unit
  | [], [] => pure ()
  | pair :: _, [] => throw (.heapNumbering heap pair.1)
  | numbered, entry :: rest =>
    if entry.1 == 0 then do
      entryBound heap found 0 entry
      joinBound heap found numbered rest
    else match numbered with
      | [] => throw (.heapNumbering heap entry.1)
      | pair :: later =>
        if pair.1 == entry.1 then do
          entryBound heap found pair.2 entry
          joinBound heap found later rest
        else throw (.heapNumbering heap (min pair.1 entry.1))

/-- Whether the bytes are one terminated `#Strings` entry that the image holds at `offset`. -/
def stringFound (image : PreparedImage) (offset : Nat) (bytes : List Nat) :
    Except AuditError Bool :=
  if bytes == bytes.dropLast ++ [0] && bytes.dropLast.all (· != 0) &&
      decide (offset + bytes.length ≤ image.layout.pe.strings.size) then
    image.view.hasBytesAt (image.layout.pe.strings.start + offset) bytes
  else pure false

/-- Whether the bytes are the length prefix and payload the image holds at `offset` in `heap`. -/
def sizedFound (image : PreparedImage) (heap : Stream) (offset : Nat) (bytes : List Nat) :
    Except AuditError Bool := do
  let blob ← blobPrefix image.view (heap.start + offset)
  if bytes.length == blob.1 + blob.2 && decide (offset + bytes.length ≤ heap.size) then
    image.view.hasBytesAt (heap.start + offset) bytes
  else pure false

/-- The carried rows and `#Strings` and `#Blob` entries are the image's under one numbering per
    heap. Each row and each entry takes one read of the image, and the numbering one sort of the
    heap cells per heap, so the check costs O((R + E) log (R + E)) comparisons for R rows and E
    entries, plus the bytes compared. -/
def rowsBound (image : PreparedImage) (rows strings blobs : List ByteEntry) :
    Except AuditError Unit := do
  let cells ← rowsCells image rows
  offsetsBound stringsHeap cells.1
  offsetsBound blobHeap cells.2
  let stringKeys ← keysBound stringsHeap (stringWidth image) cells.1
  let blobKeys ← keysBound blobHeap (blobWidth image) cells.2
  ascendingBound stringsHeap strings
  ascendingBound blobHeap blobs
  joinBound stringsHeap (stringFound image) stringKeys strings
  joinBound blobHeap (sizedFound image image.layout.pe.blobs) blobKeys blobs

/-- The assembly block is the image's: header, decoded header, and the `Assembly` row with its
    entries under a numbering of their own. -/
def assemblyBound (image : PreparedImage) (assembly : AssemblyMetadata) :
    Except AuditError Unit := do
  headerBound image assembly
  rowsBound image [(assemblyToken, assembly.assemblyRow)] assembly.strings assembly.blobs

/-! ## Soundness -/

/-- A thrown error is not a success. -/
theorem throw_ne_ok {α : Type} {error : AuditError} {value : α} :
    (throw error : Except AuditError α) ≠ .ok value := by
  intro thrown; cases thrown

#print axioms throw_ne_ok

/-- A successful header check means the carried header is the image's and decodes as carried. -/
theorem header_of_headerBound {image : PreparedImage} {assembly : AssemblyMetadata}
    (bounded : image.view.Bounded) (bound : headerBound image assembly = .ok ()) :
    HeaderAt image assembly.tableHeader ∧
      decodeTableHeader assembly.tableHeader = .ok assembly.header := by
  unfold headerBound at bound
  obtain ⟨valid, readValid, bound⟩ := except_bind_ok bound
  split at bound
  · exact absurd bound throw_ne_ok
  · rename_i sameLength
    obtain ⟨found, readFound, bound⟩ := except_bind_ok bound
    split at bound
    · rename_i matched
      simp only [Bool.and_eq_true, beq_iff_eq] at matched
      obtain ⟨isFound, decoded⟩ := matched
      subst isFound
      refine ⟨⟨valid, readValid, by simpa using sameLength, bytes_of_hasBytesAt bounded readFound⟩,
        ?_⟩
      revert decoded
      cases decodeTableHeader assembly.tableHeader <;> simp [Except.toOption]
    · exact absurd bound throw_ne_ok

#print axioms header_of_headerBound

/-- A string entry the check finds is the image's terminated entry at that offset. -/
theorem stringAt_of_stringFound {image : PreparedImage} (bounded : image.view.Bounded)
    {offset : Nat} {bytes : List Nat} (found : stringFound image offset bytes = .ok true) :
    StringAt image offset bytes := by
  unfold stringFound at found
  split at found
  · rename_i shape
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at shape
    exact ⟨bytes.dropLast, shape.1.1, fun inText => shape.1.2 0 inText rfl, shape.2,
      bytes_of_hasBytesAt bounded found⟩
  · cases found

#print axioms stringAt_of_stringFound

/-- A sized entry the check finds is the image's prefix and payload at that offset. -/
theorem sizedAt_of_sizedFound {image : PreparedImage} (bounded : image.view.Bounded)
    {heap : Stream} {offset : Nat} {bytes : List Nat}
    (found : sizedFound image heap offset bytes = .ok true) : SizedAt image heap offset bytes := by
  unfold sizedFound at found
  obtain ⟨blob, readPrefix, found⟩ := except_bind_ok found
  split at found
  · rename_i shape
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at shape
    exact ⟨blob.1, blob.2, readPrefix, shape.1, shape.2, bytes_of_hasBytesAt bounded found⟩
  · cases found

#print axioms sizedAt_of_sizedFound

/-- Two pairs in ascending order of first components, or the same pair. -/
def Linked (first second : Nat × Nat) : Prop := first.1 < second.1 ∨ first = second

/-- Ascending pairs ascend through a middle pair. -/
theorem linked_trans {first second third : Nat × Nat} (one : Linked first second)
    (two : Linked second third) : Linked first third := by
  rcases one with less | same
  · rcases two with less' | same'
    · exact .inl (Nat.lt_trans less less')
    · subst same'; exact .inl less
  · subst same; exact two

/-- A successful `distinctPairs` keeps exactly the pairs it was given, which ascend. -/
theorem distinctPairs_sound {heap : Nat} {keyOf : Nat × Nat → Nat} :
    ∀ {pairs distinct : List (Nat × Nat)}, distinctPairs heap keyOf pairs = .ok distinct →
      (∀ pair, pair ∈ distinct ↔ pair ∈ pairs) ∧ pairs.Pairwise Linked
  | [], distinct, checked => by
    simp only [distinctPairs, pure, Except.pure, Except.ok.injEq] at checked
    subst checked; simp
  | first :: rest, distinct, checked => by
    simp only [distinctPairs] at checked
    obtain ⟨later, laterChecked, checked⟩ := except_bind_ok checked
    obtain ⟨laterSame, laterLinked⟩ := distinctPairs_sound laterChecked
    cases rest with
    | nil =>
      simp only [pure, Except.pure, Except.ok.injEq] at checked
      subst checked; simp
    | cons second more =>
      simp only at checked
      by_cases ascends : first.1 < second.1
      · simp only [ascends, ite_true, pure, Except.pure, Except.ok.injEq] at checked
        subst checked
        refine ⟨fun pair => by simp only [List.mem_cons, laterSame], ?_⟩
        refine List.Pairwise.cons (fun other member => ?_) laterLinked
        rcases List.mem_cons.mp member with same | inMore
        · subst same; exact .inl ascends
        · exact linked_trans (.inl ascends) (List.rel_of_pairwise_cons laterLinked inMore)
      · by_cases equal : first = second
        · subst equal
          simp only [ascends, ite_false, beq_self_eq_true, ite_true, pure, Except.pure,
            Except.ok.injEq] at checked
          subst checked
          refine ⟨fun pair => ?_, ?_⟩
          · rw [laterSame]; simp
          · refine List.Pairwise.cons (fun other member => ?_) laterLinked
            rcases List.mem_cons.mp member with same | inMore
            · exact .inr same.symm
            · exact List.rel_of_pairwise_cons laterLinked inMore
        · have differ : (first == second) = false := by simpa using equal
          simp only [ascends, ite_false, differ] at checked
          exact absurd checked throw_ne_ok

#print axioms distinctPairs_sound

/-- In ascending pairs, a first component determines its pair. -/
theorem eq_of_pairwise_linked :
    ∀ {pairs : List (Nat × Nat)}, pairs.Pairwise Linked →
      ∀ first ∈ pairs, ∀ second ∈ pairs, first.1 = second.1 → first = second
  | [], _, _, member, _, _, _ => by cases member
  | head :: rest, linked, first, inFirst, second, inSecond, same => by
    have later := List.Pairwise.of_cons linked
    have fromHead : ∀ other ∈ rest, Linked head other := fun other member =>
      List.rel_of_pairwise_cons linked member
    rcases List.mem_cons.mp inFirst with isHead | firstInRest <;>
      rcases List.mem_cons.mp inSecond with isHead' | secondInRest
    · rw [isHead, isHead']
    · subst isHead
      rcases fromHead second secondInRest with less | equal
      · omega
      · exact equal
    · subst isHead'
      rcases fromHead first firstInRest with less | equal
      · omega
      · exact equal.symm
    · exact eq_of_pairwise_linked later first firstInRest second secondInRest same

#print axioms eq_of_pairwise_linked

/-- Sorted pairs that `distinctPairs` accepts: the same pairs, each first component once. -/
theorem sorted_sound {heap : Nat} {keyOf : Nat × Nat → Nat} {pairs distinct : List (Nat × Nat)}
    (checked : distinctPairs heap keyOf (sortPairs pairs) = .ok distinct) :
    (∀ pair, pair ∈ distinct ↔ pair ∈ pairs) ∧
      ∀ first ∈ pairs, ∀ second ∈ pairs, first.1 = second.1 → first = second := by
  obtain ⟨same, linked⟩ := distinctPairs_sound checked
  have perm := sortBy_perm pairBefore pairs.length pairs
  refine ⟨fun pair => (same pair).trans perm.mem_iff, fun first inFirst second inSecond => ?_⟩
  exact eq_of_pairwise_linked linked first (perm.mem_iff.mpr inFirst) second
    (perm.mem_iff.mpr inSecond)

#print axioms sorted_sound

/-- The key the cells give an offset: the key of a cell at that offset other than an omitted
    one. -/
def keyOfCells (cells : List (Nat × Nat)) (offset : Nat) : Option Nat :=
  (cells.find? fun cell => cell.1 == offset && cell.2 != 0).map (·.2)

/-- When an offset determines its cell, the cells give it exactly the key of its cell. -/
theorem keyOfCells_eq_some {cells : List (Nat × Nat)}
    (byOffset : ∀ first ∈ cells, ∀ second ∈ cells, first.1 = second.1 → first = second)
    {offset key : Nat} : keyOfCells cells offset = some key ↔ (offset, key) ∈ cells ∧ key ≠ 0 := by
  constructor
  · intro given
    unfold keyOfCells at given
    cases found : cells.find? (fun cell => cell.1 == offset && cell.2 != 0) with
    | none => simp [found] at given
    | some cell =>
      simp only [found, Option.map_some, Option.some.injEq] at given
      have matching := List.find?_some found
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at matching
      refine ⟨?_, given ▸ matching.2⟩
      have member := List.mem_of_find?_eq_some found
      rw [← matching.1, ← given]
      exact member
  · rintro ⟨member, nonzero⟩
    unfold keyOfCells
    cases found : cells.find? (fun cell => cell.1 == offset && cell.2 != 0) with
    | none =>
      have := List.find?_eq_none.mp found (offset, key) member
      simp [nonzero] at this
    | some cell =>
      have matching := List.find?_some found
      simp only [Bool.and_eq_true, beq_iff_eq] at matching
      have same := byOffset cell (List.mem_of_find?_eq_some found) (offset, key) member matching.1
      simp [same]

#print axioms keyOfCells_eq_some

/-- What a cell says of a numbering: the omitted key 0 that the offset has no key, any other key
    that it is the offset's key. -/
def Assigned (keyOf : Nat → Option Nat) (cell : Nat × Nat) : Prop :=
  (cell.2 = 0 → keyOf cell.1 = none) ∧ (cell.2 ≠ 0 → keyOf cell.1 = some cell.2)

/-- Every cell holds of the key the cells give, when an offset determines its cell. -/
theorem assigned_of_cells {cells : List (Nat × Nat)}
    (byOffset : ∀ first ∈ cells, ∀ second ∈ cells, first.1 = second.1 → first = second) :
    ∀ cell ∈ cells, Assigned (keyOfCells cells) cell := by
  intro cell member
  refine ⟨fun omitted => ?_, fun numbered => (keyOfCells_eq_some byOffset).mpr ⟨member, numbered⟩⟩
  cases given : keyOfCells cells cell.1 with
  | none => rfl
  | some key =>
    obtain ⟨other, nonzero⟩ := (keyOfCells_eq_some byOffset).mp given
    have := byOffset cell member (cell.1, key) other rfl
    rw [this] at omitted
    exact absurd omitted nonzero

#print axioms assigned_of_cells

/-- Pairs that `offsetsBound` accepts: an offset determines its cell. -/
theorem offsetsBound_sound {heap : Nat} {cells : List (Nat × Nat)}
    (checked : offsetsBound heap cells = .ok ()) :
    ∀ first ∈ cells, ∀ second ∈ cells, first.1 = second.1 → first = second := by
  unfold offsetsBound at checked
  obtain ⟨_, sorted, _⟩ := except_bind_ok checked
  exact (sorted_sound sorted).2

#print axioms offsetsBound_sound

/-- What `keysBound` guarantees: the numbered pairs are the swapped cells with a key, each key
    has one offset, and every key is below the marker. -/
theorem keysBound_sound {heap width : Nat} {cells numbered : List (Nat × Nat)}
    (checked : keysBound heap width cells = .ok numbered) :
    (∀ pair, pair ∈ numbered ↔ (pair.2, pair.1) ∈ cells ∧ pair.1 ≠ 0) ∧
      (∀ first second key, (first, key) ∈ cells → (second, key) ∈ cells → key ≠ 0 →
        first = second) ∧
      ∀ cell ∈ cells, cell.2 ≠ 0 → cell.2 < omittedKey width := by
  unfold keysBound at checked
  have inNumbered : ∀ pair : Nat × Nat,
      pair ∈ numberedCells cells ↔
        (pair.2, pair.1) ∈ cells ∧ pair.1 ≠ 0 := by
    intro pair
    simp only [numberedCells, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨cell, ⟨member, nonzero⟩, rfl⟩
      exact ⟨member, nonzero⟩
    · rintro ⟨member, nonzero⟩
      exact ⟨(pair.2, pair.1), ⟨member, nonzero⟩, rfl⟩
  split at checked
  · exact absurd checked throw_ne_ok
  · rename_i noneFound
    obtain ⟨same, byKey⟩ := sorted_sound checked
    refine ⟨fun pair => (same pair).trans (inNumbered pair), ?_, ?_⟩
    · intro first second key one two nonzero
      have := byKey (key, first) ((inNumbered _).mpr ⟨one, nonzero⟩) (key, second)
        ((inNumbered _).mpr ⟨two, nonzero⟩) rfl
      simpa using this
    · intro cell member nonzero
      have := List.find?_eq_none.mp noneFound (cell.2, cell.1)
        ((inNumbered _).mpr ⟨by simpa using member, nonzero⟩)
      simpa using this

#print axioms keysBound_sound

/-- A successful entry check found the entry at that offset. -/
theorem found_of_entryBound {heap : Nat} {found : Nat → List Nat → Except AuditError Bool}
    {offset : Nat} {entry : ByteEntry} (checked : entryBound heap found offset entry = .ok ()) :
    found offset entry.2 = .ok true := by
  unfold entryBound at checked
  obtain ⟨isFound, foundAt, checked⟩ := except_bind_ok checked
  cases isFound
  · exact absurd checked throw_ne_ok
  · exact foundAt

#print axioms found_of_entryBound

/-- A successful merge-join names each entry: key 0 at offset 0, any other at the offset of its
    numbered pair; and every numbered pair has an entry. -/
theorem joinBound_sound {heap : Nat} {found : Nat → List Nat → Except AuditError Bool}
    {holds : Nat → List Nat → Prop}
    (sound : ∀ offset bytes, found offset bytes = .ok true → holds offset bytes) :
    ∀ {numbered : List (Nat × Nat)} {entries : List ByteEntry},
      joinBound heap found numbered entries = .ok () →
      (∀ entry ∈ entries, ∃ offset,
        ((entry.1 = 0 ∧ offset = 0) ∨ (entry.1, offset) ∈ numbered) ∧ holds offset entry.2) ∧
      ∀ pair ∈ numbered, ∃ entry ∈ entries, entry.1 = pair.1
  | [], [], _ => by simp
  | _ :: _, [], checked => by
    simp only [joinBound] at checked
    exact absurd checked throw_ne_ok
  | numbered, entry :: rest, checked => by
    have unfolded : joinBound heap found numbered (entry :: rest) =
        if entry.1 == 0 then do
          entryBound heap found 0 entry
          joinBound heap found numbered rest
        else match numbered with
          | [] => throw (.heapNumbering heap entry.1)
          | pair :: later =>
            if pair.1 == entry.1 then do
              entryBound heap found pair.2 entry
              joinBound heap found later rest
            else throw (.heapNumbering heap (min pair.1 entry.1)) := by
      cases numbered <;> rfl
    rw [unfolded] at checked
    split at checked
    · rename_i zero
      have zero : entry.1 = 0 := by simpa using zero
      obtain ⟨_, entryChecked, restChecked⟩ := except_bind_ok checked
      obtain ⟨named, covered⟩ := joinBound_sound sound restChecked
      refine ⟨fun other member => ?_, fun pair member => ?_⟩
      · rcases List.mem_cons.mp member with same | inRest
        · subst same
          exact ⟨0, .inl ⟨zero, rfl⟩, sound _ _ (found_of_entryBound entryChecked)⟩
        · exact named other inRest
      · obtain ⟨other, inRest, sameKey⟩ := covered pair member
        exact ⟨other, List.mem_cons_of_mem _ inRest, sameKey⟩
    · cases numbered with
      | nil => exact absurd checked throw_ne_ok
      | cons pair later =>
        simp only at checked
        split at checked
        · rename_i sameKey
          have sameKey : pair.1 = entry.1 := by simpa using sameKey
          obtain ⟨_, entryChecked, restChecked⟩ := except_bind_ok checked
          obtain ⟨named, covered⟩ := joinBound_sound sound restChecked
          refine ⟨fun other member => ?_, fun numberedPair member => ?_⟩
          · rcases List.mem_cons.mp member with same | inRest
            · subst same
              refine ⟨pair.2, .inr ?_, sound _ _ (found_of_entryBound entryChecked)⟩
              rw [← sameKey]
              exact List.mem_cons_self
            · obtain ⟨offset, which, holdsAt⟩ := named other inRest
              exact ⟨offset, which.imp id (List.mem_cons_of_mem _), holdsAt⟩
          · rcases List.mem_cons.mp member with same | inLater
            · subst same
              exact ⟨entry, List.mem_cons_self, sameKey.symm⟩
            · obtain ⟨other, inRest, otherKey⟩ := covered numberedPair inLater
              exact ⟨other, List.mem_cons_of_mem _ inRest, otherKey⟩
        · exact absurd checked throw_ne_ok

#print axioms joinBound_sound

/-- One heap of a successful check: a numbering of its cells, every cell assigned by it, every
    entry named and found, every key covered, and every key from a cell. -/
theorem heap_of_bounds {heap width : Nat} {cells numbered : List (Nat × Nat)}
    {entries : List ByteEntry} {found : Nat → List Nat → Except AuditError Bool}
    {holds : Nat → List Nat → Prop}
    (sound : ∀ offset bytes, found offset bytes = .ok true → holds offset bytes)
    (nonzero : ∀ cell ∈ cells, cell.1 ≠ 0)
    (offsetsChecked : offsetsBound heap cells = .ok ())
    (keysChecked : keysBound heap width cells = .ok numbered)
    (joined : joinBound heap found numbered entries = .ok ()) :
    Numbering (keyOfCells cells) width ∧ (∀ cell ∈ cells, Assigned (keyOfCells cells) cell) ∧
      (∀ entry ∈ entries, ∃ offset, Names (keyOfCells cells) entry.1 offset ∧
        holds offset entry.2) ∧
      Covered (keyOfCells cells) entries ∧
      ∀ offset key, keyOfCells cells offset = some key → (offset, key) ∈ cells ∧ key ≠ 0 := by
  have byOffset := offsetsBound_sound offsetsChecked
  obtain ⟨inNumbered, byKey, below⟩ := keysBound_sound keysChecked
  obtain ⟨named, covered⟩ := joinBound_sound sound joined
  have given := fun {offset key : Nat} =>
    keyOfCells_eq_some byOffset (offset := offset) (key := key)
  refine ⟨⟨?_, ?_, ?_⟩, assigned_of_cells byOffset, ?_, ?_, fun _ _ found => given.mp found⟩
  · cases zeroKey : keyOfCells cells 0 with
    | none => rfl
    | some key => exact absurd rfl (nonzero _ (given.mp zeroKey).1)
  · intro first second key atFirst atSecond
    obtain ⟨inFirst, keyNonzero⟩ := given.mp atFirst
    exact byKey first second key inFirst (given.mp atSecond).1 keyNonzero
  · intro offset key atOffset
    obtain ⟨member, keyNonzero⟩ := given.mp atOffset
    exact ⟨Nat.pos_of_ne_zero keyNonzero, below _ member keyNonzero⟩
  · intro entry member
    obtain ⟨offset, which, holdsAt⟩ := named entry member
    refine ⟨offset, ?_, holdsAt⟩
    rcases which with zero | pair
    · exact .inl zero
    · exact .inr (given.mpr ((inNumbered _).mp pair))
  · intro offset key atOffset
    obtain ⟨entry, member, sameKey⟩ :=
      covered (key, offset) ((inNumbered _).mpr (given.mp atOffset))
    exact ⟨entry, member, sameKey⟩

#print axioms heap_of_bounds

/-- `littleBytes width` has `width` bytes. -/
theorem length_littleBytes : ∀ (width value : Nat), (littleBytes width value).length = width
  | 0, _ => rfl
  | width + 1, value => by simp [littleBytes, length_littleBytes width]

#print axioms length_littleBytes

/-- What a successful heap cell check states of the carried cell and the cell it returns. -/
theorem heapCell_sound {token width offset : Nat} {carried : List Nat}
    {result : Option (Nat × Nat)} (checked : heapCell token width offset carried = .ok result) :
    carried = littleBytes width (littleValue carried) ∧
      (offset = 0 ↔ littleValue carried = 0) ∧ (offset = 0 → result = none) ∧
      (offset ≠ 0 → result = some (offset, cellKey width (littleValue carried))) := by
  unfold heapCell at checked
  split at checked
  · exact absurd checked throw_ne_ok
  · rename_i shape
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at shape
    obtain ⟨canonical, zeros⟩ := shape
    have zeros : offset = 0 ↔ littleValue carried = 0 := by
      clear canonical checked
      constructor <;> intro isZero <;> simp_all
    refine ⟨canonical, zeros, fun isZero => ?_, fun nonzero => ?_⟩
    · simp only [isZero, beq_self_eq_true, ite_true, pure, Except.pure, Except.ok.injEq] at checked
      exact checked.symm
    · have : (offset == 0) = false := by simpa using nonzero
      simp only [this, Bool.false_eq_true, ite_false, pure, Except.pure,
        Except.ok.injEq] at checked
      exact checked.symm

#print axioms heapCell_sound

/-- A cell a heap cell check returns has a nonzero offset, and a key other than 0 is the carried
    cell's value. -/
theorem heapCell_cell {token width offset : Nat} {carried : List Nat}
    {result : Option (Nat × Nat)} (checked : heapCell token width offset carried = .ok result) :
    ∀ cell ∈ result.toList, cell.1 ≠ 0 ∧ (cell.2 ≠ 0 → cell.2 = littleValue carried) := by
  obtain ⟨-, -, isNone, isSome⟩ := heapCell_sound checked
  intro cell member
  by_cases zero : offset = 0
  · rw [isNone zero] at member; cases member
  · rw [isSome zero] at member
    simp only [Option.toList_some, List.mem_singleton] at member
    subst member
    refine ⟨zero, fun nonzero => ?_⟩
    simp only [cellKey] at nonzero ⊢
    split <;> simp_all

#print axioms heapCell_cell

/-- The image cell, canonicalized under a numbering its returned cell holds of, is the carried
    cell. -/
theorem canonical_of_heapCell {keyOf : Nat → Option Nat} {token width : Nat}
    {imageCell carried : List Nat} {result : Option (Nat × Nat)}
    (length : imageCell.length = width)
    (checked : heapCell token width (littleValue imageCell) carried = .ok result)
    (assigned : ∀ cell ∈ result.toList, Assigned keyOf cell) :
    littleBytes imageCell.length (canonicalKey keyOf imageCell.length (littleValue imageCell)) =
      carried := by
  obtain ⟨canonical, zeros, isNone, isSome⟩ := heapCell_sound checked
  rw [length, canonical]
  congr 1
  unfold canonicalKey
  by_cases zero : littleValue imageCell = 0
  · simp only [zero, beq_self_eq_true, ite_true]
    exact (zeros.mp zero).symm
  · have nonzero : (littleValue imageCell == 0) = false := by simpa using zero
    simp only [nonzero, Bool.false_eq_true, ite_false]
    have cellAssigned := assigned (littleValue imageCell, cellKey width (littleValue carried))
      (by rw [isSome zero]; simp)
    have keyNonzero : littleValue carried ≠ 0 := fun isZero => zero (zeros.mpr isZero)
    by_cases omitted : littleValue carried = omittedKey width
    · have : cellKey width (littleValue carried) = 0 := by simp [cellKey, omitted]
      rw [cellAssigned.1 this, omitted]
      rfl
    · have : cellKey width (littleValue carried) = littleValue carried := by
        simp [cellKey, omitted]
      have keyed := cellAssigned.2 (by simpa [this] using keyNonzero)
      simp only [this] at keyed
      rw [keyed]
      rfl

#print axioms canonical_of_heapCell

/-- A successful row check: every returned cell has a nonzero offset and, unless omitted, a key
    a cell of its heap holds in the carried row; and under any numberings the returned cells hold
    of, the image row canonicalizes to the carried row. -/
theorem rowCells_sound {token : Nat} :
    ∀ {columns : List ColumnPlace} {imageRow carried : List Nat} {cells : HeapCells},
      rowCells token columns imageRow carried = .ok cells →
      (∀ cell ∈ cells.1, cell.1 ≠ 0 ∧
        (cell.2 ≠ 0 → cell.2 ∈ rowKeys stringsHeap columns carried)) ∧
      (∀ cell ∈ cells.2, cell.1 ≠ 0 ∧ (cell.2 ≠ 0 → cell.2 ∈ rowKeys blobHeap columns carried)) ∧
      ∀ strings blobs, (∀ cell ∈ cells.1, Assigned strings cell) →
        (∀ cell ∈ cells.2, Assigned blobs cell) →
        canonicalCells strings blobs token columns imageRow = .ok carried
  | [], imageRow, carried, cells, checked => by
    simp only [rowCells] at checked
    split at checked
    · rename_i empty
      simp only [Bool.and_eq_true, List.isEmpty_iff] at empty
      obtain ⟨imageEmpty, carriedEmpty⟩ := empty
      subst imageEmpty carriedEmpty
      simp only [pure, Except.pure, Except.ok.injEq] at checked
      subst checked
      exact ⟨by simp, by simp, fun _ _ _ _ => rfl⟩
    · exact absurd checked throw_ne_ok
  | ⟨offset, width, column⟩ :: rest, imageRow, carried, cells, checked => by
    simp only [rowCells] at checked
    split at checked
    · exact absurd checked throw_ne_ok
    · rename_i lengthOk
      have imageLength : (imageRow.take width).length = width := by simpa using lengthOk
      obtain ⟨tail, tailChecked, checked⟩ := except_bind_ok checked
      obtain ⟨tailStrings, tailBlobs, tailCanonical⟩ := rowCells_sound tailChecked
      have canonicalHead : ∀ strings blobs, canonicalCells strings blobs token
          (⟨offset, width, column⟩ :: rest) imageRow =
          (canonicalCells strings blobs token rest (imageRow.drop width)).map
            (canonicalCell strings blobs column (imageRow.take width) ++ ·) := by
        intro strings blobs
        simp only [canonicalCells, imageLength, bne_self_eq_false, Bool.false_eq_true, ite_false]
        cases canonicalCells strings blobs token rest (imageRow.drop width) <;> rfl
      cases column with
      | string =>
        simp only at checked
        obtain ⟨cell, cellChecked, checked⟩ := except_bind_ok checked
        simp only [pure, Except.pure, Except.ok.injEq] at checked
        subst checked
        have fromCell := heapCell_cell cellChecked
        refine ⟨fun found member => ?_, fun found member => ?_,
          fun strings blobs inStrings inBlobs => ?_⟩
        · rcases List.mem_append.mp member with here | later
          · obtain ⟨nonzero, keyed⟩ := fromCell found here
            refine ⟨nonzero, fun keyNonzero => ?_⟩
            simp only [rowKeys, Column.heap?, stringsHeap, beq_self_eq_true, ite_true]
            exact List.mem_cons.mpr (.inl (keyed keyNonzero))
          · obtain ⟨nonzero, keyed⟩ := tailStrings found later
            refine ⟨nonzero, fun keyNonzero => ?_⟩
            simp only [rowKeys, Column.heap?, stringsHeap, beq_self_eq_true, ite_true]
            exact List.mem_cons_of_mem _ (keyed keyNonzero)
        · obtain ⟨nonzero, keyed⟩ := tailBlobs found member
          refine ⟨nonzero, fun keyNonzero => ?_⟩
          simpa [rowKeys, Column.heap?, stringsHeap, blobHeap] using keyed keyNonzero
        · rw [canonicalHead, tailCanonical strings blobs
            (fun found member => inStrings found (List.mem_append_right _ member)) inBlobs]
          simp only [Except.map, canonicalCell]
          rw [canonical_of_heapCell imageLength cellChecked
            (fun found member => inStrings found (List.mem_append_left _ member)),
            List.take_append_drop]
      | blob =>
        simp only at checked
        obtain ⟨cell, cellChecked, checked⟩ := except_bind_ok checked
        simp only [pure, Except.pure, Except.ok.injEq] at checked
        subst checked
        have fromCell := heapCell_cell cellChecked
        refine ⟨fun found member => ?_, fun found member => ?_,
          fun strings blobs inStrings inBlobs => ?_⟩
        · obtain ⟨nonzero, keyed⟩ := tailStrings found member
          refine ⟨nonzero, fun keyNonzero => ?_⟩
          simpa [rowKeys, Column.heap?, stringsHeap, blobHeap] using keyed keyNonzero
        · rcases List.mem_append.mp member with here | later
          · obtain ⟨nonzero, keyed⟩ := fromCell found here
            refine ⟨nonzero, fun keyNonzero => ?_⟩
            simp only [rowKeys, Column.heap?, blobHeap, beq_self_eq_true, ite_true]
            exact List.mem_cons.mpr (.inl (keyed keyNonzero))
          · obtain ⟨nonzero, keyed⟩ := tailBlobs found later
            refine ⟨nonzero, fun keyNonzero => ?_⟩
            simp only [rowKeys, Column.heap?, blobHeap, beq_self_eq_true, ite_true]
            exact List.mem_cons_of_mem _ (keyed keyNonzero)
        · rw [canonicalHead, tailCanonical strings blobs inStrings
            (fun found member => inBlobs found (List.mem_append_right _ member))]
          simp only [Except.map, canonicalCell]
          rw [canonical_of_heapCell imageLength cellChecked
            (fun found member => inBlobs found (List.mem_append_left _ member)),
            List.take_append_drop]
      | fixed | guid | index | coded =>
        simp only at checked
        split at checked
        · rename_i same
          have same : carried.take width = imageRow.take width := by simpa using same
          simp only [pure, Except.pure, Except.ok.injEq] at checked
          subst checked
          refine ⟨fun found member => ?_, fun found member => ?_,
            fun strings blobs inStrings inBlobs => ?_⟩
          · obtain ⟨nonzero, keyed⟩ := tailStrings found member
            exact ⟨nonzero, fun keyNonzero => by
              simpa [rowKeys, Column.heap?] using keyed keyNonzero⟩
          · obtain ⟨nonzero, keyed⟩ := tailBlobs found member
            exact ⟨nonzero, fun keyNonzero => by
              simpa [rowKeys, Column.heap?] using keyed keyNonzero⟩
          · rw [canonicalHead, tailCanonical strings blobs inStrings inBlobs]
            simp only [Except.map, canonicalCell]
            rw [← same, List.take_append_drop]
        · exact absurd checked throw_ne_ok

#print axioms rowCells_sound

/-- A successful check of one carried row against the row its token names. -/
theorem rowCellsAt_sound {image : PreparedImage} (bounded : image.view.Bounded) {token : Nat}
    {carried : List Nat} {cells : HeapCells}
    (checked : rowCellsAt image token carried = .ok cells) :
    ∃ columns, image.columnsOf (token / 2 ^ 24) = some columns ∧
      (∀ cell ∈ cells.1, cell.1 ≠ 0 ∧
        (cell.2 ≠ 0 → cell.2 ∈ rowKeys stringsHeap columns carried)) ∧
      (∀ cell ∈ cells.2, cell.1 ≠ 0 ∧ (cell.2 ≠ 0 → cell.2 ∈ rowKeys blobHeap columns carried)) ∧
      ∀ strings blobs, (∀ cell ∈ cells.1, Assigned strings cell) →
        (∀ cell ∈ cells.2, Assigned blobs cell) → RowAt image strings blobs token carried := by
  unfold rowCellsAt at checked
  obtain ⟨place, placed, checked⟩ := except_bind_ok checked
  split at checked
  · exact absurd checked throw_ne_ok
  · rename_i sameLength
    have sameLength : carried.length = place.2 := by simpa using sameLength
    obtain ⟨value, readRow, checked⟩ := except_bind_ok checked
    split at checked
    · exact absurd checked throw_ne_ok
    · rename_i columns found
      obtain ⟨stringCells, blobCells, canonical⟩ := rowCells_sound checked
      refine ⟨columns, found, stringCells, blobCells, fun strings blobs inStrings inBlobs =>
        ⟨place.1, valueBytes place.2 value, ?_, ?_, ?_⟩⟩
      · rw [placed, sameLength]
      · rw [sameLength]; exact bytes_of_slice bounded readRow
      · unfold canonicalRow
        rw [found]
        exact canonical strings blobs inStrings inBlobs

#print axioms rowCellsAt_sound

/-- A successful check of carried rows: each returned cell is from a row, and under numberings
    the cells hold of, every row is the image's. -/
theorem rowsCells_sound {image : PreparedImage} (bounded : image.view.Bounded) :
    ∀ {rows : List ByteEntry} {cells : HeapCells}, rowsCells image rows = .ok cells →
      (∀ cell ∈ cells.1, cell.1 ≠ 0 ∧ (cell.2 ≠ 0 → ∃ row ∈ rows, ∃ columns,
        image.columnsOf (row.1 / 2 ^ 24) = some columns ∧
          cell.2 ∈ rowKeys stringsHeap columns row.2)) ∧
      (∀ cell ∈ cells.2, cell.1 ≠ 0 ∧ (cell.2 ≠ 0 → ∃ row ∈ rows, ∃ columns,
        image.columnsOf (row.1 / 2 ^ 24) = some columns ∧
          cell.2 ∈ rowKeys blobHeap columns row.2)) ∧
      ∀ strings blobs, (∀ cell ∈ cells.1, Assigned strings cell) →
        (∀ cell ∈ cells.2, Assigned blobs cell) →
        ∀ row ∈ rows, RowAt image strings blobs row.1 row.2
  | [], cells, checked => by
    simp only [rowsCells, pure, Except.pure, Except.ok.injEq] at checked
    subst checked
    simp
  | row :: rest, cells, checked => by
    simp only [rowsCells] at checked
    obtain ⟨here, hereChecked, checked⟩ := except_bind_ok checked
    obtain ⟨later, laterChecked, checked⟩ := except_bind_ok checked
    simp only [pure, Except.pure, Except.ok.injEq] at checked
    subst checked
    obtain ⟨columns, found, hereStrings, hereBlobs, hereRow⟩ :=
      rowCellsAt_sound bounded hereChecked
    obtain ⟨laterStrings, laterBlobs, laterRows⟩ := rowsCells_sound bounded laterChecked
    refine ⟨fun cell member => ?_, fun cell member => ?_,
      fun strings blobs inStrings inBlobs other member => ?_⟩
    · rcases List.mem_append.mp member with inHere | inLater
      · obtain ⟨nonzero, held⟩ := hereStrings cell inHere
        exact ⟨nonzero, fun keyNonzero =>
          ⟨row, List.mem_cons_self, columns, found, held keyNonzero⟩⟩
      · obtain ⟨nonzero, held⟩ := laterStrings cell inLater
        refine ⟨nonzero, fun keyNonzero => ?_⟩
        obtain ⟨holder, inRest, rest⟩ := held keyNonzero
        exact ⟨holder, List.mem_cons_of_mem _ inRest, rest⟩
    · rcases List.mem_append.mp member with inHere | inLater
      · obtain ⟨nonzero, held⟩ := hereBlobs cell inHere
        exact ⟨nonzero, fun keyNonzero =>
          ⟨row, List.mem_cons_self, columns, found, held keyNonzero⟩⟩
      · obtain ⟨nonzero, held⟩ := laterBlobs cell inLater
        refine ⟨nonzero, fun keyNonzero => ?_⟩
        obtain ⟨holder, inRest, rest⟩ := held keyNonzero
        exact ⟨holder, List.mem_cons_of_mem _ inRest, rest⟩
    · rcases List.mem_cons.mp member with same | inRest
      · subst same
        exact hereRow strings blobs
          (fun cell inHere => inStrings cell (List.mem_append_left _ inHere))
          (fun cell inHere => inBlobs cell (List.mem_append_left _ inHere))
      · exact laterRows strings blobs
          (fun cell inLater => inStrings cell (List.mem_append_right _ inLater))
          (fun cell inLater => inBlobs cell (List.mem_append_right _ inLater)) other inRest

#print axioms rowsCells_sound

/-- When the rows check succeeds on a view of a well-formed image, the carried rows and entries
    are the image's under one numbering per heap. -/
theorem rowsMatch_of_rowsBound {image : PreparedImage} {rows strings blobs : List ByteEntry}
    (bounded : image.view.Bounded) (bound : rowsBound image rows strings blobs = .ok ()) :
    RowsMatch image rows strings blobs := by
  unfold rowsBound at bound
  obtain ⟨cells, cellsChecked, bound⟩ := except_bind_ok bound
  obtain ⟨_, stringOffsets, bound⟩ := except_bind_ok bound
  obtain ⟨_, blobOffsets, bound⟩ := except_bind_ok bound
  obtain ⟨stringKeys, stringKeysChecked, bound⟩ := except_bind_ok bound
  obtain ⟨blobKeys, blobKeysChecked, bound⟩ := except_bind_ok bound
  obtain ⟨_, _, bound⟩ := except_bind_ok bound
  obtain ⟨_, _, bound⟩ := except_bind_ok bound
  obtain ⟨_, stringsJoined, blobsJoined⟩ := except_bind_ok bound
  obtain ⟨stringCells, blobCells, rowsAt⟩ := rowsCells_sound bounded cellsChecked
  obtain ⟨stringNumbering, stringAssigned, stringEntries, stringCovered, stringFrom⟩ :=
    heap_of_bounds (fun _ _ => stringAt_of_stringFound bounded)
      (fun cell member => (stringCells cell member).1) stringOffsets stringKeysChecked
      stringsJoined
  obtain ⟨blobNumbering, blobAssigned, blobEntries, blobCovered, blobFrom⟩ :=
    heap_of_bounds (fun _ _ => sizedAt_of_sizedFound bounded)
      (fun cell member => (blobCells cell member).1) blobOffsets blobKeysChecked blobsJoined
  refine ⟨keyOfCells cells.1, keyOfCells cells.2, stringNumbering, blobNumbering,
    rowsAt _ _ stringAssigned blobAssigned, stringEntries, blobEntries, stringCovered,
    blobCovered, fun offset key given => ?_, fun offset key given => ?_⟩
  · obtain ⟨member, nonzero⟩ := stringFrom offset key given
    exact (stringCells _ member).2 nonzero
  · obtain ⟨member, nonzero⟩ := blobFrom offset key given
    exact (blobCells _ member).2 nonzero

#print axioms rowsMatch_of_rowsBound

/-- When the assembly check succeeds on a view of a well-formed image, the assembly block is the
    image's. -/
theorem assemblyMatches_of_assemblyBound {image : PreparedImage} {assembly : AssemblyMetadata}
    (bounded : image.view.Bounded) (bound : assemblyBound image assembly = .ok ()) :
    AssemblyMatches image assembly := by
  unfold assemblyBound at bound
  obtain ⟨_, headerChecked, rowsChecked⟩ := except_bind_ok bound
  obtain ⟨headerAt, decoded⟩ := header_of_headerBound bounded headerChecked
  exact ⟨headerAt, decoded, rowsMatch_of_rowsBound bounded rowsChecked⟩

#print axioms assemblyMatches_of_assemblyBound

/-- Every image `prepareOne` decodes has a view of a well-formed image. -/
theorem prepareOne_bounded {pinned : PinnedImage} {image : PreparedImage}
    (prepared : prepareOne pinned = .ok image) : image.view.Bounded := by
  unfold prepareOne at prepared
  obtain ⟨view, built, prepared⟩ := except_bind_ok prepared
  obtain ⟨_, _, prepared⟩ := except_bind_ok prepared
  obtain ⟨_, _, prepared⟩ := except_bind_ok prepared
  split at prepared
  · exact absurd prepared throw_ne_ok
  · obtain ⟨_, _, prepared⟩ := except_bind_ok prepared
    obtain ⟨_, _, prepared⟩ := except_bind_ok prepared
    injection prepared with prepared
    subst prepared
    exact ofImage_bounded built

#print axioms prepareOne_bounded

/-- Every image `prepareOne` decodes carries the column table of its own layout, so `RowAt` reads
    the schema's columns at the image's widths. -/
theorem prepareOne_columns {pinned : PinnedImage} {image : PreparedImage}
    (prepared : prepareOne pinned = .ok image) : image.columns = image.layout.columnTable := by
  unfold prepareOne at prepared
  obtain ⟨view, _, prepared⟩ := except_bind_ok prepared
  obtain ⟨_, _, prepared⟩ := except_bind_ok prepared
  obtain ⟨_, _, prepared⟩ := except_bind_ok prepared
  split at prepared
  · exact absurd prepared throw_ne_ok
  · obtain ⟨_, _, prepared⟩ := except_bind_ok prepared
    obtain ⟨_, _, prepared⟩ := except_bind_ok prepared
    injection prepared with prepared
    subst prepared
    rfl

#print axioms prepareOne_columns

end StrictBinding
