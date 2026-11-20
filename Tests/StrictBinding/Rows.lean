import StrictBinding.Rows
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

/-!
# Strict binding tests: carried metadata

The assembly block an extraction carries for the fixture (`StrictFixture.assemblyBlock`, read by
System.Reflection.Metadata) is the image's, and `assemblyMatches_of_assemblyBound` turns the check
into the proposition. A block changed in one place is refused with the error that names the place:
the header bytes, the decoded header, the `Assembly` row, a key or an entry. Two changes are made
to the image instead, with the fixture's block carried unchanged. The fixture has no culture and
no public key, so variants whose culture is a suffix of the name, or whose eight-byte key is at
`#Blob` offset 1, cover two numbered string entries and a key entry at a nonzero offset. A carried
entry no row cell holds is refused by the check and by the proposition.

The rows and entries of `StrictFixture.slice`, every row of the carried tables with the entries
only its Field rows name omitted, are the image's under `rowsMatch_of_rowsBound`. A changed row,
token, key or entry is refused, and an image changed only in a MethodDef RVA is accepted.
-/

namespace Tests.StrictBinding.Rows

open _root_.StrictBinding
open CIL.Extraction (AssemblyMetadata ByteEntry MetadataSlice stringsHeap blobHeap)

/-- The fixture, prepared as the audit prepares a pinned image. -/
private def fixture : Except AuditError PreparedImage :=
  prepareOne { identity := StrictFixture.identity, image := StrictFixture.image }

/-- The assembly check of a carried block against a prepared image. -/
private def checked (prepared : Except AuditError PreparedImage) (assembly : AssemblyMetadata) :
    Except AuditError Unit :=
  prepared >>= (assemblyBound · assembly)

/-- The carried block of the fixture. -/
private def block : AssemblyMetadata := StrictFixture.assemblyBlock

/-- The offset of the major version in a carried `Assembly` row. -/
private def majorVersionAt : Nat := 4

/-- The offset of the `PublicKey` key in a carried `Assembly` row with two-byte heap indexes. -/
private def publicKeyAt : Nat := 16

/-- The offset of the `Name` key in a carried `Assembly` row with two-byte heap indexes. -/
private def nameAt : Nat := 18

/-- The offset of the `Culture` key in a carried `Assembly` row with two-byte heap indexes. -/
private def cultureAt : Nat := 20

/-- The fixture's carried `Assembly` row with the two-byte key at `offset` set to `key`. -/
private def rowWithKey (offset key : Nat) : List Nat := writeLittle block.assemblyRow offset 2 key

/-! ## The fixture's block -/

/-- The fixture's carried block passes the check. -/
theorem accepts_the_carried_assembly_block : ok (checked fixture block) = true := by
  decide +kernel
#print axioms accepts_the_carried_assembly_block

/-- The block is the fixture's in the sense of `AssemblyMatches`. -/
theorem the_carried_block_matches_the_fixture {image : PreparedImage}
    (prepared : fixture = .ok image) : AssemblyMatches image block := by
  apply assemblyMatches_of_assemblyBound (prepareOne_bounded prepared)
  have accepted := accepts_the_carried_assembly_block
  simp only [checked, prepared, bind, Except.bind] at accepted
  cases checkedBlock : assemblyBound image block with
  | error _ => simp [checkedBlock, ok] at accepted
  | ok _ => rfl
#print axioms the_carried_block_matches_the_fixture

/-- The TypeRef row count, at byte 28 of the header, is 10 instead of 11. -/
theorem rejects_a_changed_header_byte :
    failsWith (checked fixture { block with tableHeader := flipAt block.tableHeader 28 1 })
      (.headerMismatch StrictFixture.identity) = true := by
  decide +kernel
#print axioms rejects_a_changed_header_byte

/-- The `Valid` mask, from byte 8, also marks table 3 present. -/
theorem rejects_a_flipped_valid_bit :
    failsWith (checked fixture { block with tableHeader := flipAt block.tableHeader 8 0x08 })
      (.headerMismatch StrictFixture.identity) = true := by
  decide +kernel
#print axioms rejects_a_flipped_valid_bit

/-- A header four bytes longer or shorter than the image's `Valid` mask declares. -/
theorem rejects_a_header_length_off_by_four :
    failsWith (checked fixture { block with tableHeader := block.tableHeader ++ [0, 0, 0, 0] })
      (.headerMismatch StrictFixture.identity) = true ∧
    failsWith
      (checked fixture
        { block with tableHeader := block.tableHeader.take (block.tableHeader.length - 4) })
      (.headerMismatch StrictFixture.identity) = true := by
  decide +kernel
#print axioms rejects_a_header_length_off_by_four

/-- A decoded header with 12 TypeRef rows where the header bytes say 11. -/
theorem rejects_a_decoded_header_that_differs_from_the_bytes :
    failsWith
      (checked fixture
        { block with header := .ofCounts 0 (block.header.rowCounts.set 1 (0x01, 12)) })
      (.headerMismatch StrictFixture.identity) = true := by
  decide +kernel
#print axioms rejects_a_decoded_header_that_differs_from_the_bytes

/-- The carried `Sorted` mask, from byte 16, differs. Decoding ignores `Sorted`, so only the
    comparison with the image bytes refuses it. -/
theorem rejects_a_changed_sorted_byte :
    failsWith (checked fixture { block with tableHeader := flipAt block.tableHeader 16 1 })
      (.headerMismatch StrictFixture.identity) = true := by
  decide +kernel
#print axioms rejects_a_changed_sorted_byte

/-- The file offset of the image's `HashAlgId`, the first byte of its `Assembly` row. -/
private def hashAlgorithmAt : Nat := 1416

/-- The file offset of the image's `Sorted` mask, 16 bytes into its table stream at 792. -/
private def sortedMaskAt : Nat := 792 + 16

/-- The fixture image with the byte at `offset` changed, prepared under the fixture's identity. -/
private def changedImage (offset : Nat) : Except AuditError PreparedImage :=
  prepareOne { identity := StrictFixture.identity, image := flipByte StrictFixture.image offset 1 }

/-- The fixture's carried block against an image whose `HashAlgId` differs. -/
theorem rejects_an_image_with_a_changed_hash_algorithm :
    failsWith (checked (changedImage hashAlgorithmAt) block)
      (.rowMismatch assemblyToken) = true := by
  decide +kernel
#print axioms rejects_an_image_with_a_changed_hash_algorithm

/-- The fixture's carried block against an image whose `Sorted` mask differs. -/
theorem rejects_an_image_with_a_changed_sorted_byte :
    failsWith (checked (changedImage sortedMaskAt) block)
      (.headerMismatch StrictFixture.identity) = true := by
  decide +kernel
#print axioms rejects_an_image_with_a_changed_sorted_byte

/-- The major version in the `Assembly` row is 0 instead of 1. -/
theorem rejects_a_changed_assembly_row_byte :
    failsWith
      (checked fixture { block with assemblyRow := flipAt block.assemblyRow majorVersionAt 1 })
      (.rowMismatch assemblyToken) = true := by
  decide +kernel
#print axioms rejects_a_changed_assembly_row_byte

/-- The first byte of the carried name is `T` instead of `S`. -/
theorem rejects_a_changed_name_byte :
    failsWith
      (checked fixture
        { block with
          strings := block.strings.set 1 (1, flipAt (block.strings.getD 1 (0, [])).2 0 7) })
      (.heapMismatch stringsHeap 1) = true := by
  decide +kernel
#print axioms rejects_a_changed_name_byte

/-- Key 0 says the name is at offset 0, where the image's name is not. -/
theorem rejects_key_zero_for_a_nonzero_offset :
    failsWith (checked fixture { block with assemblyRow := rowWithKey nameAt 0 })
      (.rowMismatch assemblyToken) = true := by
  decide +kernel
#print axioms rejects_key_zero_for_a_nonzero_offset

/-- The omitted-entry marker says the culture is at a nonzero offset, where the image has 0. -/
theorem rejects_the_marker_for_offset_zero :
    failsWith
      (checked fixture { block with assemblyRow := rowWithKey cultureAt 0xFFFF })
      (.rowMismatch assemblyToken) = true := by
  decide +kernel
#print axioms rejects_the_marker_for_offset_zero

/-- Name key 1 without the entry it ranks. -/
theorem rejects_a_string_key_without_its_entry :
    failsWith (checked fixture { block with strings := block.strings.filter (·.1 != 1) })
      (.heapNumbering stringsHeap 1) = true := by
  decide +kernel
#print axioms rejects_a_string_key_without_its_entry

/-- Keys 0, for the empty culture and the absent key, need no carried entry. -/
theorem accepts_zero_keys_without_entries :
    ok (checked fixture
      { block with strings := block.strings.filter (·.1 != 0), blobs := [] }) = true := by
  decide +kernel
#print axioms accepts_zero_keys_without_entries

/-! ## Entries at a suffix of the name -/

/-- The `#Strings` offset of the fixture's name. -/
private def nameOffset : Nat := 207

/-- The `#Strings` offset of `Fixture`, the suffix of the name. -/
private def suffixOffset : Nat := 213

/-- `Fixture` with its terminator. -/
private def suffixBytes : List Nat := [70, 105, 120, 116, 117, 114, 101, 0]

/-- The fixture's name entry. -/
private def nameBytes : List Nat := (block.strings.getD 1 (0, [])).2

/-- The fixture's block with the name's suffix carried under key 2, which no row cell holds. -/
private def suffixBlock : AssemblyMetadata :=
  { block with strings := block.strings ++ [(2, suffixBytes)] }

/-- A carried entry under a key no row cell holds. -/
theorem rejects_an_entry_no_row_names :
    failsWith (checked fixture suffixBlock) (.heapNumbering stringsHeap 2) = true := by
  decide +kernel
#print axioms rejects_an_entry_no_row_names

/-- The `#Strings` keys of the fixture's carried row: 1 for the name and 0 for the culture. -/
private theorem fixture_string_keys :
    (match fixture with
     | .ok image =>
       (image.columnsOf (assemblyToken / 2 ^ 24)).map (rowKeys stringsHeap · block.assemblyRow)
     | .error _ => none) = some [1, 0] := by
  decide +kernel
#print axioms fixture_string_keys

/-- No numbering makes the suffix block the fixture's, since its key 2 is held by no row cell. -/
theorem the_suffix_block_does_not_match {image : PreparedImage} (prepared : fixture = .ok image) :
    ¬ AssemblyMatches image suffixBlock := by
  rintro ⟨_, _, _, _, _, _, _, entries, _, _, _, held, _⟩
  obtain ⟨offset, named, _⟩ := entries (2, suffixBytes) (by simp [suffixBlock])
  rcases named with ⟨two, _⟩ | given
  · cases two
  · obtain ⟨row, member, columns, found, inRow⟩ := held offset 2 given
    simp only [List.mem_singleton] at member
    subst member
    have keys := fixture_string_keys
    simp only [prepared, found, Option.map_some, Option.some.injEq] at keys
    change 2 ∈ rowKeys stringsHeap columns block.assemblyRow at inRow
    rw [keys] at inRow
    simp at inRow
#print axioms the_suffix_block_does_not_match

/-- The fixture with the culture cell of its `Assembly` row set to `offset`. -/
private def culturedImage (offset : Nat) : ImageBytes :=
  match fixture with
  | .ok image =>
    match image.layout.cellAt assemblyToken 8 with
    | .ok (cell, width) =>
      ImageBytes.ofBytes (writeLittle (imageBytes StrictFixture.image) cell width offset)
    | .error _ => StrictFixture.image
  | .error _ => StrictFixture.image

/-- The variant whose culture is `culture`, at `offset`, prepared under the identity it spells. -/
private def cultured (offset : Nat) (culture : String) : Except AuditError PreparedImage :=
  prepareOne { image := culturedImage offset, identity :=
    "StrictFixture, Version=1.2.3.4, Culture=" ++ culture ++ ", PublicKeyToken=null" }

/-- The fixture's carried row with name key `name` and culture key `culture`. -/
private def rowWithNames (name culture : Nat) : List Nat :=
  writeLittle (rowWithKey nameAt name) cultureAt 2 culture

/-- The culture `Fixture` at the suffix of the name: two numbered entries, ranked by their
    bytes. -/
theorem accepts_a_culture_at_a_suffix_of_the_name :
    ok (checked (cultured suffixOffset "Fixture")
      { block with assemblyRow := rowWithNames 2 1,
                   strings := [(0, [0]), (1, suffixBytes), (2, nameBytes)] }) = true := by
  decide +kernel
#print axioms accepts_a_culture_at_a_suffix_of_the_name

/-- One key for the name and the culture, which are at different offsets. -/
theorem rejects_one_key_for_two_offsets :
    failsWith (checked (cultured suffixOffset "Fixture")
      { block with assemblyRow := rowWithNames 2 2, strings := [(0, [0]), (2, nameBytes)] })
      (.heapNumbering stringsHeap 2) = true := by
  decide +kernel
#print axioms rejects_one_key_for_two_offsets

/-- Two keys for the name and the culture, which are at one offset. -/
theorem rejects_two_keys_for_one_offset :
    failsWith (checked (cultured nameOffset "StrictFixture")
      { block with assemblyRow := rowWithNames 1 2,
                   strings := [(0, [0]), (1, nameBytes), (2, nameBytes)] })
      (.heapNumbering stringsHeap 2) = true := by
  decide +kernel
#print axioms rejects_two_keys_for_one_offset

/-! ## A public key at a nonzero offset -/

/-- The eight bytes of the key in the fixture's Assembly definition. -/
private def keyBytes : List Nat := [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]

/-- The fixture with its key blob, length prefix and key, written at `#Blob` offset 1 and named
    by its `Assembly` row. -/
private def keyedImage : ImageBytes :=
  match fixture with
  | .ok image =>
    match image.layout.cellAt assemblyToken 6 with
    | .ok (keyCell, keyWidth) =>
      let named := writeLittle (imageBytes StrictFixture.image) keyCell keyWidth 1
      ImageBytes.ofBytes
        (writeBytes named (image.layout.pe.blobs.start + 1) (keyBytes.length :: keyBytes))
    | .error _ => StrictFixture.image
  | .error _ => StrictFixture.image

/-- The variant, prepared under the identity its key spells. -/
private def keyed : Except AuditError PreparedImage :=
  prepareOne { image := keyedImage, identity :=
    "StrictFixture, Version=1.2.3.4, Culture=neutral, PublicKeyToken=4705f121e18edfe3" }

/-- The block an extraction carries for the variant: its key is the only blob, ranked 1. -/
private def keyedBlock : AssemblyMetadata :=
  { block with assemblyRow := rowWithKey publicKeyAt 1,
               blobs := [(1, keyBytes.length :: keyBytes)] }

/-- The variant's carried block, with its key at `#Blob` offset 1, passes the check. -/
theorem accepts_a_carried_key_at_a_nonzero_offset : ok (checked keyed keyedBlock) = true := by
  decide +kernel
#print axioms accepts_a_carried_key_at_a_nonzero_offset

/-- Blob key 1 without the entry it ranks. -/
theorem rejects_a_blob_key_without_its_entry :
    failsWith (checked keyed { keyedBlock with blobs := [] })
      (.heapNumbering blobHeap 1) = true := by
  decide +kernel
#print axioms rejects_a_blob_key_without_its_entry

/-- The last key byte is `0xee` instead of `0xef`. -/
theorem rejects_a_changed_key_byte :
    failsWith
      (checked keyed { keyedBlock with blobs := [(1, flipAt (keyBytes.length :: keyBytes) 8 1)] })
      (.heapMismatch blobHeap 1) = true := by
  decide +kernel
#print axioms rejects_a_changed_key_byte

/-- Key 0 says the key is at offset 0, where the image's key is not. -/
theorem rejects_key_zero_for_the_key_offset :
    failsWith
      (checked keyed { keyedBlock with assemblyRow := rowWithKey publicKeyAt 0 })
      (.rowMismatch assemblyToken) = true := by
  decide +kernel
#print axioms rejects_key_zero_for_the_key_offset

/-- The marker says the key is not carried, which holds; a carried key no row names is refused. -/
theorem accepts_the_marker_only_without_the_entry :
    ok (checked keyed
      { keyedBlock with assemblyRow := rowWithKey publicKeyAt 0xFFFF, blobs := [] }) = true ∧
    failsWith
      (checked keyed { keyedBlock with assemblyRow := rowWithKey publicKeyAt 0xFFFF })
      (.heapNumbering blobHeap 1) = true := by
  decide +kernel
#print axioms accepts_the_marker_only_without_the_entry

/-! ## Rows of a slice -/

/-- The slice an extraction could carry for the fixture. -/
private def slice : MetadataSlice := StrictFixture.slice

/-- The rows check of carried rows and entries against a prepared image. -/
private def rowsChecked (prepared : Except AuditError PreparedImage)
    (rows strings blobs : List ByteEntry) : Except AuditError Unit :=
  prepared >>= (rowsBound · rows strings blobs)

/-- The slice's rows with the row of `token` changed by `change`. -/
private def withRow (token : Nat) (change : List Nat → List Nat) : List ByteEntry :=
  slice.rows.map fun row => if row.1 == token then (row.1, change row.2) else row

/-- The token of the `Arithmetic.Tiny` MethodDef row. -/
private def tinyToken : Nat := 0x06000001

/-- The token of the `Arithmetic.Fat` MethodDef row. -/
private def fatToken : Nat := 0x06000002

/-- The token of the first `.ctor` MethodDef row. -/
private def constructorToken : Nat := 0x06000006

/-- The token of the `<Module>` TypeDef row, whose namespace is at `#Strings` offset 0. -/
private def moduleTypeToken : Nat := 0x02000001

/-- The token of the `Small` TypeDef row. -/
private def smallToken : Nat := 0x02000002

/-- The token of the `Overlay` TypeDef row. -/
private def overlayToken : Nat := 0x02000003

/-- The offset of the RVA in a MethodDef row. -/
private def rvaAt : Nat := 0

/-- The offset of the implementation flags in a MethodDef row, the byte after its RVA. -/
private def implementationAt : Nat := 4

/-- The offset of the flags in a MethodDef row. -/
private def flagsAt : Nat := 6

/-- The offset of the name key in a MethodDef row with two-byte heap indexes. -/
private def methodNameAt : Nat := 8

/-- The offset of the name key in a TypeDef row with two-byte heap indexes. -/
private def typeNameAt : Nat := 4

/-- The offset of the namespace key in a TypeDef row with two-byte heap indexes. -/
private def typeNamespaceAt : Nat := 6

/-- The slice's key of `Small`. -/
private def smallKey : Nat := 19

/-- The slice's key of `Fat`. -/
private def fatKey : Nat := 11

/-- The slice's key of `Tiny`. -/
private def tinyKey : Nat := 28

/-- The first `#Strings` key the slice does not use. -/
private def unusedKey : Nat := 32

/-- `.ctor` with its terminator. -/
private def constructorBytes : List Nat := [46, 99, 116, 111, 114, 0]

/-- The fixture with the byte at `column` of the row of `token` changed. -/
private def changedRow (token column : Nat) : Except AuditError PreparedImage :=
  match fixture with
  | .ok image =>
    match image.layout.rowAt token with
    | .ok (offset, _) =>
      prepareOne { identity := StrictFixture.identity,
                   image := flipByte StrictFixture.image (offset + column) 1 }
    | .error error => .error error
  | .error error => .error error

/-- The slice's rows, MethodDef RVAs zeroed and Field entries omitted, pass the check. -/
theorem accepts_the_carried_slice_rows :
    ok (rowsChecked fixture slice.rows slice.strings slice.blobs) = true := by
  decide +kernel
#print axioms accepts_the_carried_slice_rows

/-- The slice's rows and entries are the fixture's in the sense of `RowsMatch`. -/
theorem the_carried_slice_rows_match_the_fixture {image : PreparedImage}
    (prepared : fixture = .ok image) : RowsMatch image slice.rows slice.strings slice.blobs := by
  apply rowsMatch_of_rowsBound (prepareOne_bounded prepared)
  have accepted := accepts_the_carried_slice_rows
  simp only [rowsChecked, prepared, bind, Except.bind] at accepted
  cases checkedRows : rowsBound image slice.rows slice.strings slice.blobs with
  | error _ => simp [checkedRows, ok] at accepted
  | ok _ => rfl
#print axioms the_carried_slice_rows_match_the_fixture

/-- Where a body is placed is not a row fact: an image whose `Tiny` RVA differs still matches. -/
theorem accepts_an_image_with_a_changed_rva :
    ok (rowsChecked (changedRow tinyToken rvaAt) slice.rows slice.strings slice.blobs) = true := by
  decide +kernel
#print axioms accepts_an_image_with_a_changed_rva

/-- The mask is the four RVA bytes: an image change to the last of them is accepted, and a change
    to the first byte of ImplFlags after them is refused in the image and in the carried row. -/
theorem masks_exactly_the_rva :
    ok (rowsChecked (changedRow tinyToken (implementationAt - 1)) slice.rows slice.strings
      slice.blobs) = true ∧
    failsWith
      (rowsChecked (changedRow tinyToken implementationAt) slice.rows slice.strings slice.blobs)
      (.rowMismatch tinyToken) = true ∧
    failsWith
      (rowsChecked fixture (withRow tinyToken (flipAt · implementationAt 1)) slice.strings
        slice.blobs)
      (.rowMismatch tinyToken) = true := by
  decide +kernel
#print axioms masks_exactly_the_rva

/-- The mask reaches no other table: a TypeDef flags byte of `Small` changed in the image, or in
    the carried row, is refused. -/
theorem rejects_a_changed_typedef_flags_byte :
    failsWith (rowsChecked (changedRow smallToken 0) slice.rows slice.strings slice.blobs)
      (.rowMismatch smallToken) = true ∧
    failsWith
      (rowsChecked fixture (withRow smallToken (flipAt · 0 1)) slice.strings slice.blobs)
      (.rowMismatch smallToken) = true := by
  decide +kernel
#print axioms rejects_a_changed_typedef_flags_byte

/-- A carried MethodDef row holds its RVA as zero. -/
theorem rejects_a_carried_nonzero_rva :
    failsWith
      (rowsChecked fixture (withRow tinyToken (flipAt · rvaAt 1)) slice.strings slice.blobs)
      (.rowMismatch tinyToken) = true := by
  decide +kernel
#print axioms rejects_a_carried_nonzero_rva

/-- A flags byte of `Tiny` changed in the carried row, or in the image. -/
theorem rejects_a_changed_flags_byte :
    failsWith
      (rowsChecked fixture (withRow tinyToken (flipAt · flagsAt 1)) slice.strings slice.blobs)
      (.rowMismatch tinyToken) = true ∧
    failsWith (rowsChecked (changedRow tinyToken flagsAt) slice.rows slice.strings slice.blobs)
      (.rowMismatch tinyToken) = true := by
  decide +kernel
#print axioms rejects_a_changed_flags_byte

/-- The rows of `Tiny` and `Fat` carried under each other's tokens. -/
theorem rejects_swapped_row_tokens :
    failsWith
      (rowsChecked fixture
        (slice.rows.map fun row =>
          if row.1 == tinyToken then (fatToken, row.2)
          else if row.1 == fatToken then (tinyToken, row.2) else row)
        slice.strings slice.blobs)
      (.rowMismatch fatToken) = true := by
  decide +kernel
#print axioms rejects_swapped_row_tokens

/-- The row of `Tiny` one byte short. -/
theorem rejects_a_row_one_byte_short :
    failsWith (rowsChecked fixture (withRow tinyToken (·.dropLast)) slice.strings slice.blobs)
      (.rowMismatch tinyToken) = true := by
  decide +kernel
#print axioms rejects_a_row_one_byte_short

/-- A GenericParam row, a table the fixture does not have; an eleventh MethodDef row; MethodDef row
    0; and a row of table 0x2D, above the tables the schema covers. -/
theorem rejects_a_token_the_tables_do_not_have :
    failsWith
      (rowsChecked fixture (slice.rows ++ [(0x2A000001, List.replicate 8 0)])
        slice.strings slice.blobs)
      (.tokenOutOfScope 0x2A000001) = true ∧
    failsWith
      (rowsChecked fixture (slice.rows ++ [(0x0600000B, List.replicate 14 0)])
        slice.strings slice.blobs)
      (.tokenOutOfScope 0x0600000B) = true ∧
    failsWith
      (rowsChecked fixture (slice.rows ++ [(0x06000000, List.replicate 14 0)])
        slice.strings slice.blobs)
      (.tokenOutOfScope 0x06000000) = true ∧
    failsWith
      (rowsChecked fixture (slice.rows ++ [(0x2D000001, List.replicate 4 0)])
        slice.strings slice.blobs)
      (.tokenOutOfScope 0x2D000001) = true := by
  decide +kernel
#print axioms rejects_a_token_the_tables_do_not_have

/-- Key 0 says the name of `Small` is at offset 0, where it is not. -/
theorem rejects_key_zero_for_a_nonzero_row_offset :
    failsWith
      (rowsChecked fixture (withRow smallToken (writeLittle · typeNameAt 2 0))
        slice.strings slice.blobs)
      (.rowMismatch smallToken) = true := by
  decide +kernel
#print axioms rejects_key_zero_for_a_nonzero_row_offset

/-- The marker says the namespace of `<Module>` is at a nonzero offset, where it is at 0. -/
theorem rejects_the_marker_for_a_zero_row_offset :
    failsWith
      (rowsChecked fixture (withRow moduleTypeToken (writeLittle · typeNamespaceAt 2 0xFFFF))
        slice.strings slice.blobs)
      (.rowMismatch moduleTypeToken) = true := by
  decide +kernel
#print axioms rejects_the_marker_for_a_zero_row_offset

/-- The key of `Small` for the name of `Overlay`, which is at another offset. -/
theorem rejects_one_row_key_for_two_offsets :
    failsWith
      (rowsChecked fixture (withRow overlayToken (writeLittle · typeNameAt 2 smallKey))
        slice.strings slice.blobs)
      (.heapNumbering stringsHeap smallKey) = true := by
  decide +kernel
#print axioms rejects_one_row_key_for_two_offsets

/-- A second key for `.ctor`, with its entry carried, in one of the rows that name it. -/
theorem rejects_two_row_keys_for_one_offset :
    failsWith
      (rowsChecked fixture (withRow constructorToken (writeLittle · methodNameAt 2 unusedKey))
        (slice.strings ++ [(unusedKey, constructorBytes)]) slice.blobs)
      (.heapNumbering stringsHeap unusedKey) = true := by
  decide +kernel
#print axioms rejects_two_row_keys_for_one_offset

/-- An entry under a key no row cell holds. -/
theorem rejects_a_slice_entry_no_row_names :
    failsWith
      (rowsChecked fixture slice.rows (slice.strings ++ [(unusedKey, [65, 0])]) slice.blobs)
      (.heapNumbering stringsHeap unusedKey) = true := by
  decide +kernel
#print axioms rejects_a_slice_entry_no_row_names

/-- The key of `Fat` without the entry it ranks. -/
theorem rejects_a_row_key_without_its_entry :
    failsWith
      (rowsChecked fixture slice.rows (slice.strings.filter (·.1 != fatKey)) slice.blobs)
      (.heapNumbering stringsHeap fatKey) = true := by
  decide +kernel
#print axioms rejects_a_row_key_without_its_entry

/-- The name of `Tiny` carried under the omitted-entry marker, in its row cell and as its entry:
    no numbering gives the marker, so the entry is one no row cell holds. -/
theorem rejects_an_entry_at_the_marker :
    failsWith
      (rowsChecked fixture (withRow tinyToken (writeLittle · methodNameAt 2 0xFFFF))
        (slice.strings.filter (·.1 != tinyKey) ++ [(0xFFFF, [84, 105, 110, 121, 0])]) slice.blobs)
      (.heapNumbering stringsHeap 0xFFFF) = true := by
  decide +kernel
#print axioms rejects_an_entry_at_the_marker

/-- The first two `#Blob` entries, keys 0 and 1, carried in descending order. -/
theorem rejects_entries_out_of_order :
    failsWith
      (rowsChecked fixture slice.rows slice.strings
        ((slice.blobs.take 2).reverse ++ slice.blobs.drop 2))
      (.heapNumbering blobHeap 0) = true := by
  decide +kernel
#print axioms rejects_entries_out_of_order

/-- The signature `int (int)` with its last byte changed, and the name `Fat` with a byte after
    its terminator. -/
theorem rejects_a_changed_slice_entry :
    failsWith
      (rowsChecked fixture slice.rows slice.strings (slice.blobs.set 3 (3, [3, 32, 0, 9])))
      (.heapMismatch blobHeap 3) = true ∧
    failsWith
      (rowsChecked fixture slice.rows (slice.strings.set fatKey (fatKey, [70, 97, 116, 0, 0]))
        slice.blobs)
      (.heapMismatch stringsHeap fatKey) = true := by
  decide +kernel
#print axioms rejects_a_changed_slice_entry

/-- Where `Tiny` names its own entry with the marker, the entry is one no row cell holds. -/
theorem rejects_the_marker_for_a_carried_entry :
    failsWith
      (rowsChecked fixture (withRow tinyToken (writeLittle · methodNameAt 2 0xFFFF))
        slice.strings slice.blobs)
      (.heapNumbering stringsHeap tinyKey) = true := by
  decide +kernel
#print axioms rejects_the_marker_for_a_carried_entry

/-- The marker in one `.ctor` row while the other rows name `.ctor` by its key: the offset of
    `.ctor` would be both numbered and omitted. -/
theorem rejects_a_marker_beside_a_key :
    failsWith
      (rowsChecked fixture (withRow constructorToken (writeLittle · methodNameAt 2 0xFFFF))
        slice.strings slice.blobs)
      (.heapNumbering stringsHeap 1) = true := by
  decide +kernel
#print axioms rejects_a_marker_beside_a_key

end Tests.StrictBinding.Rows
