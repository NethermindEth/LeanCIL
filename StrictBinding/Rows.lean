import StrictBinding.Bind
import StrictBinding.Reads
import CIL.Extraction.MetadataBytes

/-!
# Carried metadata bound to images

An extraction carries, for each pinned assembly, its table stream header, the header decoded,
its `Assembly` row and the heap entries that row names
(`CIL.Extraction.AssemblyMetadata`). A carried row does not hold the image's `#Strings` and `#Blob`
offsets: each heap column holds a key, 0 for offset 0, the rank of the entry among the entries
carried, or `omittedKey` for an entry the extraction does not carry. `RowAt`, `StringAt` and
`SizedAt` state that carried bytes are the image's under such a numbering, and `AssemblyMatches`
states it for an assembly block. `assemblyBound` checks it, taking every position and length it
compares from the image itself, and `assemblyMatches_of_assemblyBound` proves that its success
means the proposition.
-/

namespace StrictBinding

open CIL.Extraction (AssemblyMetadata ByteEntry decodeTableHeader stringsHeap blobHeap)

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

/-- The columns of `table` with their widths in the image. -/
def columnsOf (image : PreparedImage) (table : Nat) : Option (List (Column × Nat)) :=
  (schema table).map fun columns => columns.map fun column =>
    (column, columnWidth image.layout.heapSizes image.layout.rowCount column)

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
    List (Column × Nat) → List Nat → Except AuditError (List Nat)
  | [], [] => pure []
  | [], _ :: _ => throw (.rowMismatch token)
  | (column, width) :: rest, row => do
    let cell := row.take width
    if cell.length != width then throw (.rowMismatch token)
    let tail ← canonicalCells strings blobs token rest (row.drop width)
    pure (canonicalCell strings blobs column cell ++ tail)

/-- The image row of `token` as a carried row holds it, under the numberings `strings` and
    `blobs`. -/
def canonicalRow (image : PreparedImage) (strings blobs : Nat → Option Nat) (token : Nat)
    (row : List Nat) : Except AuditError (List Nat) :=
  match columnsOf image (token / 2 ^ 24) with
  | some columns => canonicalCells strings blobs token columns row
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

/-- The assembly block is the image's: its header bytes, the header they decode to, its
    `Assembly` row under a numbering of its own entries, and each of those entries. -/
def AssemblyMatches (image : PreparedImage) (assembly : AssemblyMetadata) : Prop :=
  HeaderAt image assembly.tableHeader ∧
    decodeTableHeader assembly.tableHeader = .ok assembly.header ∧
    ∃ strings blobs, Numbering strings (stringWidth image) ∧ Numbering blobs (blobWidth image) ∧
      RowAt image strings blobs assemblyToken assembly.assemblyRow ∧
      (∀ entry ∈ assembly.strings, ∃ offset, Names strings entry.1 offset ∧
        StringAt image offset entry.2) ∧
      ∀ entry ∈ assembly.blobs, ∃ offset, Names blobs entry.1 offset ∧
        SizedAt image image.layout.pe.blobs offset entry.2

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

/-- The (image offset, carried key) of each cell of `heap` in two rows of these columns. -/
def heapPairs (heap : Nat) : List (Column × Nat) → List Nat → List Nat → List (Nat × Nat)
  | [], _, _ => []
  | (column, width) :: rest, imageRow, carriedRow =>
    let tail := heapPairs heap rest (imageRow.drop width) (carriedRow.drop width)
    if column.heap? == some heap then
      (littleValue (imageRow.take width), littleValue (carriedRow.take width)) :: tail
    else tail

/-- The pairs that number an entry: a nonzero offset with a key other than 0 and the marker. -/
def numberedPairs (width : Nat) (pairs : List (Nat × Nat)) : List (Nat × Nat) :=
  pairs.filter fun pair => pair.1 != 0 && pair.2 != 0 && pair.2 != omittedKey width

/-- The key a pair list gives an offset. -/
def keyOfPairs (pairs : List (Nat × Nat)) (offset : Nat) : Option Nat :=
  (pairs.find? (·.1 == offset)).map (·.2)

/-- Pairs that share an offset share a key, and pairs that share a key share an offset. -/
def Consistent (pairs : List (Nat × Nat)) : Prop :=
  ∀ first ∈ pairs, ∀ second ∈ pairs, (first.1 = second.1 ↔ first.2 = second.2)

/-- Whether a pair breaks a numbering among `pairs`: a zero offset or key, a key at or above
    `omittedKey width`, or another pair that shares exactly one of its offset and key. -/
def breaksNumbering (width : Nat) (pairs : List (Nat × Nat)) (pair : Nat × Nat) : Bool :=
  pair.1 == 0 || pair.2 == 0 || omittedKey width ≤ pair.2 ||
    pairs.any fun other => (pair.1 == other.1) != (pair.2 == other.2)

/-- The pairs number offsets. Each pair is compared with every other, so the cost is quadratic in
    the pairs, which are the at most three heap cells of one row. -/
def numberingBound (heap width : Nat) (pairs : List (Nat × Nat)) : Except AuditError Unit :=
  match pairs.find? (breaksNumbering width pairs) with
  | some pair => throw (.heapNumbering heap pair.2)
  | none => pure ()

/-- The carried `Assembly` row is the image's under the numbering its own heap cells give, with
    the `#Strings` and `#Blob` pairs of that numbering. -/
def assemblyRowBound (image : PreparedImage) (row : List Nat) :
    Except AuditError (List (Nat × Nat) × List (Nat × Nat)) := do
  let place ← image.layout.rowAt assemblyToken
  if row.length != place.2 then throw (.rowMismatch assemblyToken)
  else
    let value ← image.view.slice place.1 place.2
    let imageRow := valueBytes place.2 value
    match columnsOf image (assemblyToken / 2 ^ 24) with
    | none => throw (.tokenOutOfScope assemblyToken)
    | some columns =>
      let strings := numberedPairs (stringWidth image) (heapPairs stringsHeap columns imageRow row)
      let blobs := numberedPairs (blobWidth image) (heapPairs blobHeap columns imageRow row)
      numberingBound stringsHeap (stringWidth image) strings
      numberingBound blobHeap (blobWidth image) blobs
      if (canonicalRow image (keyOfPairs strings) (keyOfPairs blobs) assemblyToken
          imageRow).toOption == some row then pure (strings, blobs)
      else throw (.rowMismatch assemblyToken)

/-- The offset a carried key names among the pairs: 0 for key 0, else the pair's offset. -/
def entryOffset (heap : Nat) (pairs : List (Nat × Nat)) (key : Nat) : Except AuditError Nat :=
  if key == 0 then pure 0
  else
    match pairs.find? (·.2 == key) with
    | some pair => pure pair.1
    | none => throw (.heapNumbering heap key)

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

/-- Every carried entry of `heap` is found at the offset its key names among the pairs. -/
def entriesBound (heap : Nat) (found : Nat → List Nat → Except AuditError Bool)
    (pairs : List (Nat × Nat)) (entries : List ByteEntry) : Except AuditError Unit :=
  entries.forM fun entry => do
    let offset ← entryOffset heap pairs entry.1
    let isFound ← found offset entry.2
    if isFound then pure () else throw (.heapMismatch heap entry.1)

/-- The assembly block is the image's: header, decoded header, `Assembly` row and entries. Each
    entry, the row and the header take one read of the bytes compared, and the work is linear in
    those bytes up to the logarithmic joins of `ImageView.slice` and `bytesValue`. -/
def assemblyBound (image : PreparedImage) (assembly : AssemblyMetadata) :
    Except AuditError Unit := do
  headerBound image assembly
  let pairs ← assemblyRowBound image assembly.assemblyRow
  entriesBound stringsHeap (stringFound image) pairs.1 assembly.strings
  entriesBound blobHeap (sizedFound image image.layout.pe.blobs) pairs.2 assembly.blobs

/-! ## Soundness -/

/-- A thrown error is not a success. -/
theorem throw_ne_ok {α : Type} {error : AuditError} {value : α} :
    (throw error : Except AuditError α) ≠ .ok value := by
  intro thrown; cases thrown

#print axioms throw_ne_ok

/-- Every item a successful `forM` visits succeeds. -/
theorem forM_ok {ε α : Type} {check : α → Except ε Unit} :
    ∀ {items : List α}, items.forM check = .ok () → ∀ item ∈ items, check item = .ok ()
  | [], _, _, member => by cases member
  | item :: rest, done, other, member => by
    simp only [List.forM] at done
    obtain ⟨_, first, later⟩ := bind_ok done
    cases List.mem_cons.mp member with
    | inl same => subst same; exact first
    | inr inRest => exact forM_ok later other inRest

#print axioms forM_ok

/-- A successful header check means the carried header is the image's and decodes as carried. -/
theorem header_of_headerBound {image : PreparedImage} {assembly : AssemblyMetadata}
    (bounded : image.view.Bounded) (bound : headerBound image assembly = .ok ()) :
    HeaderAt image assembly.tableHeader ∧
      decodeTableHeader assembly.tableHeader = .ok assembly.header := by
  unfold headerBound at bound
  obtain ⟨valid, readValid, bound⟩ := bind_ok bound
  split at bound
  · exact absurd bound throw_ne_ok
  · rename_i sameLength
    obtain ⟨found, readFound, bound⟩ := bind_ok bound
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

/-- An offset the pairs give a key comes from a pair. -/
theorem pair_of_keyOfPairs {pairs : List (Nat × Nat)} {offset key : Nat}
    (given : keyOfPairs pairs offset = some key) :
    ∃ pair ∈ pairs, pair.1 = offset ∧ pair.2 = key := by
  unfold keyOfPairs at given
  cases found : pairs.find? (·.1 == offset) with
  | none => simp [found] at given
  | some pair =>
    simp only [found, Option.map_some, Option.some.injEq] at given
    exact ⟨pair, List.mem_of_find?_eq_some found,
      by simpa using List.find?_some found, given⟩

#print axioms pair_of_keyOfPairs

/-- Consistent pairs give each of their offsets its key. -/
theorem keyOfPairs_of_mem {pairs : List (Nat × Nat)} (consistent : Consistent pairs)
    {pair : Nat × Nat} (member : pair ∈ pairs) : keyOfPairs pairs pair.1 = some pair.2 := by
  unfold keyOfPairs
  cases found : pairs.find? (·.1 == pair.1) with
  | none =>
    have := List.find?_eq_none.mp found pair member
    simp at this
  | some other =>
    have sameOffset : other.1 = pair.1 := by simpa using List.find?_some found
    simp only [Option.map_some, Option.some.injEq]
    exact (consistent other (List.mem_of_find?_eq_some found) pair member).mp sameOffset

#print axioms keyOfPairs_of_mem

/-- Pairs the numbering check accepts are consistent and number their offsets. -/
theorem numbering_of_numberingBound {heap width : Nat} {pairs : List (Nat × Nat)}
    (bound : numberingBound heap width pairs = .ok ()) :
    Numbering (keyOfPairs pairs) width ∧ Consistent pairs := by
  unfold numberingBound at bound
  split at bound
  · exact absurd bound throw_ne_ok
  · rename_i none
    have good : ∀ pair ∈ pairs, breaksNumbering width pairs pair = false := by
      intro pair member
      simpa using List.find?_eq_none.mp none pair member
    have consistent : Consistent pairs := by
      intro first inFirst second inSecond
      have := good first inFirst
      simp only [breaksNumbering, Bool.or_eq_false_iff, List.any_eq_false] at this
      have agree := this.2 second inSecond
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at agree
      cases offsets : first.1 == second.1 <;> cases keys : first.2 == second.2 <;>
        simp_all
    refine ⟨⟨?_, ?_, ?_⟩, consistent⟩
    · cases given : keyOfPairs pairs 0 with
      | none => rfl
      | some key =>
        obtain ⟨pair, member, offsetZero, _⟩ := pair_of_keyOfPairs given
        have := good pair member
        simp [breaksNumbering, offsetZero] at this
    · intro first second key atFirst atSecond
      obtain ⟨one, inOne, oneOffset, oneKey⟩ := pair_of_keyOfPairs atFirst
      obtain ⟨two, inTwo, twoOffset, twoKey⟩ := pair_of_keyOfPairs atSecond
      rw [← oneOffset, ← twoOffset]
      exact (consistent one inOne two inTwo).mpr (oneKey.trans twoKey.symm)
    · intro offset key given
      obtain ⟨pair, member, _, pairKey⟩ := pair_of_keyOfPairs given
      have := good pair member
      simp only [breaksNumbering, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        decide_eq_false_iff_not, Nat.not_le] at this
      subst pairKey
      exact ⟨Nat.pos_of_ne_zero this.1.1.2, this.1.2⟩

#print axioms numbering_of_numberingBound

/-- A successful row check means the carried `Assembly` row is the image's under numberings of
    the pairs it returns, which are consistent. -/
theorem row_of_assemblyRowBound {image : PreparedImage} {row : List Nat}
    {strings blobs : List (Nat × Nat)} (bounded : image.view.Bounded)
    (bound : assemblyRowBound image row = .ok (strings, blobs)) :
    Numbering (keyOfPairs strings) (stringWidth image) ∧ Consistent strings ∧
      Numbering (keyOfPairs blobs) (blobWidth image) ∧ Consistent blobs ∧
      RowAt image (keyOfPairs strings) (keyOfPairs blobs) assemblyToken row := by
  unfold assemblyRowBound at bound
  obtain ⟨place, placed, bound⟩ := bind_ok bound
  split at bound
  · exact absurd bound throw_ne_ok
  · rename_i sameLength
    have sameLength : row.length = place.2 := by simpa using sameLength
    obtain ⟨value, readRow, bound⟩ := bind_ok bound
    split at bound
    · exact absurd bound throw_ne_ok
    · rename_i columns _
      obtain ⟨_, stringsNumbered, bound⟩ := bind_ok bound
      obtain ⟨_, blobsNumbered, bound⟩ := bind_ok bound
      split at bound
      · rename_i matched
        injection bound with bound
        injection bound with stringsEq blobsEq
        subst stringsEq blobsEq
        obtain ⟨stringsNumbering, stringsConsistent⟩ :=
          numbering_of_numberingBound stringsNumbered
        obtain ⟨blobsNumbering, blobsConsistent⟩ := numbering_of_numberingBound blobsNumbered
        refine ⟨stringsNumbering, stringsConsistent, blobsNumbering, blobsConsistent,
          place.1, valueBytes place.2 value, ?_, ?_, ?_⟩
        · rw [placed, sameLength]
        · rw [sameLength]; exact bytes_of_slice bounded readRow
        · revert matched
          cases canonicalRow image _ _ assemblyToken (valueBytes place.2 value) <;>
            simp [Except.toOption]
      · exact absurd bound throw_ne_ok

#print axioms row_of_assemblyRowBound

/-- A successful entry check finds each entry where its key names, among consistent pairs. -/
theorem entries_of_entriesBound {heap : Nat} {found : Nat → List Nat → Except AuditError Bool}
    {holds : Nat → List Nat → Prop}
    (sound : ∀ offset bytes, found offset bytes = .ok true → holds offset bytes)
    {pairs : List (Nat × Nat)} (consistent : Consistent pairs) {entries : List ByteEntry}
    (bound : entriesBound heap found pairs entries = .ok ()) :
    ∀ entry ∈ entries,
      ∃ offset, Names (keyOfPairs pairs) entry.1 offset ∧ holds offset entry.2 := by
  intro entry member
  have checked := forM_ok bound entry member
  obtain ⟨offset, located, checked⟩ := bind_ok checked
  obtain ⟨isFound, foundAt, checked⟩ := bind_ok checked
  split at checked
  · rename_i yes
    subst yes
    refine ⟨offset, ?_, sound _ _ foundAt⟩
    unfold entryOffset at located
    split at located
    · rename_i zero
      injection located with located
      exact .inl ⟨by simpa using zero, located.symm⟩
    · split at located
      · rename_i pair named
        injection located with located
        subst located
        have member := List.mem_of_find?_eq_some named
        have sameKey : pair.2 = entry.1 := by simpa using List.find?_some named
        exact .inr (sameKey ▸ keyOfPairs_of_mem consistent member)
      · exact absurd located throw_ne_ok
  · exact absurd checked throw_ne_ok

#print axioms entries_of_entriesBound

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
  obtain ⟨blob, readPrefix, found⟩ := bind_ok found
  split at found
  · rename_i shape
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at shape
    exact ⟨blob.1, blob.2, readPrefix, shape.1, shape.2, bytes_of_hasBytesAt bounded found⟩
  · cases found

#print axioms sizedAt_of_sizedFound

/-- When the assembly check succeeds on a view of a well-formed image, the assembly block is the
    image's. -/
theorem assemblyMatches_of_assemblyBound {image : PreparedImage} {assembly : AssemblyMetadata}
    (bounded : image.view.Bounded) (bound : assemblyBound image assembly = .ok ()) :
    AssemblyMatches image assembly := by
  unfold assemblyBound at bound
  obtain ⟨_, headerChecked, bound⟩ := bind_ok bound
  obtain ⟨⟨strings, blobs⟩, rowChecked, bound⟩ := bind_ok bound
  obtain ⟨_, stringsChecked, blobsChecked⟩ := bind_ok bound
  obtain ⟨headerAt, decoded⟩ := header_of_headerBound bounded headerChecked
  obtain ⟨stringsNumbering, stringsConsistent, blobsNumbering, blobsConsistent, rowAt⟩ :=
    row_of_assemblyRowBound bounded rowChecked
  exact ⟨headerAt, decoded, keyOfPairs strings, keyOfPairs blobs, stringsNumbering,
    blobsNumbering, rowAt,
    entries_of_entriesBound (fun _ _ => stringAt_of_stringFound bounded) stringsConsistent
      stringsChecked,
    entries_of_entriesBound (fun _ _ => sizedAt_of_sizedFound bounded) blobsConsistent
      blobsChecked⟩

#print axioms assemblyMatches_of_assemblyBound

/-- Every image `prepareOne` decodes has a view of a well-formed image. -/
theorem prepareOne_bounded {pinned : PinnedImage} {image : PreparedImage}
    (prepared : prepareOne pinned = .ok image) : image.view.Bounded := by
  unfold prepareOne at prepared
  obtain ⟨view, built, prepared⟩ := bind_ok prepared
  obtain ⟨_, _, prepared⟩ := bind_ok prepared
  obtain ⟨_, _, prepared⟩ := bind_ok prepared
  split at prepared
  · exact absurd prepared throw_ne_ok
  · obtain ⟨_, _, prepared⟩ := bind_ok prepared
    obtain ⟨_, _, prepared⟩ := bind_ok prepared
    injection prepared with prepared
    subst prepared
    exact ofImage_bounded built

#print axioms prepareOne_bounded

end StrictBinding
