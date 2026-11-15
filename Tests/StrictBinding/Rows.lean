import StrictBinding.Rows
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

/-!
# Strict binding tests: carried metadata

The assembly block an extraction carries for the fixture (`StrictFixture.assemblyBlock`, read by
System.Reflection.Metadata) is the image's, and `assemblyMatches_of_assemblyBound` turns the check
into the proposition. A block changed in one place is refused with the error that names the place:
the header bytes, the decoded header, the `Assembly` row, a key or an entry. Every change is made
to the carried block, never to the pinned image. The fixture has no public key, so a variant with
an eight-byte key at `#Blob` offset 1 covers a key entry at a nonzero offset.
-/

namespace Tests.StrictBinding.Rows

open _root_.StrictBinding
open CIL.Extraction (AssemblyMetadata stringsHeap blobHeap)

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

/-! ## A public key at a nonzero offset -/

/-- The key the variant carries: eight bytes without the `PublicKey` flag, so they are its
    token. -/
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
    "StrictFixture, Version=1.2.3.4, Culture=neutral, PublicKeyToken=0123456789abcdef" }

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

end Tests.StrictBinding.Rows
