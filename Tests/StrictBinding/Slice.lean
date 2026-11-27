import CIL.Extraction.KernelEquation
import StrictBinding.Slice
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation
import Tests.StrictBinding.PreparedData

/-! Whole metadata checks, user-string offsets, payloads, prefixes and heap bounds, and the
    slice's core-library AssemblyRef. -/

namespace Tests.StrictBinding.Slice

open _root_.StrictBinding
open CIL.Extraction (ByteEntry MetadataSlice userStringHeap)

/-- The fixture with the empty user string at heap offset 1. -/
private def fixture : Except AuditError PreparedImage :=
  prepareOne
    { identity := StrictFixture.identity, image := flipByte StrictFixture.image 2021 1 }

/-- The fixture's carried rows and independently numbered Assembly block, with its user string. -/
private def carried : MetadataSlice :=
  { StrictFixture.slice with userStrings := [(1, [1, 0])] }

/-- The complete check on the fixture. -/
private def checked (slice : MetadataSlice) : Except AuditError Unit :=
  fixture >>= fun image => sliceBound image slice

/-- The prepared data of the modified fixture. -/
private def prepared : PreparedImage :=
  (prepared_data% fixture).toOption.get (by rfl)

/-- The kernel binds the prepared data to the exact modified image. -/
private theorem fixture_eq : fixture = .ok prepared := by cil_kernel_rfl
#print axioms fixture_eq

/-- Every user-string or core-reference variant carries these same assembly and method rows. -/
private theorem shared_rows :
    assemblyBound prepared carried.assembly = .ok () ∧
    rowsBound prepared carried.rows carried.strings carried.blobs = .ok () := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms shared_rows

/-- The complete check on these same rows leaves the two varying claims to check. -/
private theorem checked_claims (entries : List ByteEntry) (corlib : Nat) :
    checked { carried with userStrings := entries, corlib := corlib } =
      (do userStringsBound prepared entries; corlibBound prepared corlib) := by
  simp only [checked, fixture_eq, Bind.bind, Except.bind, sliceBound, sliceContentsBound,
    shared_rows.1, shared_rows.2]
#print axioms checked_claims

/-- The complete carried metadata, including a one-byte length prefix, passes. -/
theorem accepts_fixture : ok (checked carried) = true := by
  rw [checked_claims]
  decide +kernel
#print axioms accepts_fixture

/-- A changed user-string byte is refused by the complete check. -/
theorem rejects_changed_byte :
    failsWith (checked { carried with userStrings := [(1, [1, 1])] })
      (.heapMismatch userStringHeap 1) = true := by
  rw [checked_claims]
  decide +kernel
#print axioms rejects_changed_byte

/-- A payload shorter than its image length prefix is refused. -/
theorem rejects_truncated_payload :
    failsWith (checked { carried with userStrings := [(1, [1])] })
      (.heapMismatch userStringHeap 1) = true := by
  rw [checked_claims]
  decide +kernel
#print axioms rejects_truncated_payload

/-- An extra byte after the exact payload is refused. -/
theorem rejects_extra_byte :
    failsWith (checked { carried with userStrings := [(1, [1, 0, 0])] })
      (.heapMismatch userStringHeap 1) = true := by
  rw [checked_claims]
  decide +kernel
#print axioms rejects_extra_byte

/-- A key names an image offset, so the same bytes at another offset are refused. -/
theorem rejects_wrong_offset :
    failsWith (checked { carried with userStrings := [(2, [1, 0])] })
      (.heapMismatch userStringHeap 2) = true := by
  rw [checked_claims]
  decide +kernel
#print axioms rejects_wrong_offset

/-- A later user string is checked even when the first entry matches. -/
theorem rejects_false_second_entry :
    failsWith (checked { carried with userStrings := [(1, [1, 0]), (2, [1, 1])] })
      (.heapMismatch userStringHeap 2) = true := by
  rw [checked_claims]
  decide +kernel
#print axioms rejects_false_second_entry

/-- A prepared view with an explicit user-string heap, for prefix and boundary tests. -/
private def heapImage (bytes : List Nat) (size : Nat) : Except AuditError PreparedImage := do
  let image <- fixture
  let view <- ImageView.ofImage (ImageBytes.ofBytes bytes)
  pure
    { image with
      view := view
      layout :=
        { image.layout with
          pe := { image.layout.pe with userStrings := { start := 0, size := size } } } }

/-- User-string checks over a bounded heap inside a larger view. -/
private def checkedHeap (bytes : List Nat) (size : Nat) (entries : List ByteEntry) :=
  heapImage bytes size >>= fun image => userStringsBound image entries

/-- Equal prefixes at different offsets still require equal payload bytes. -/
theorem rejects_wrong_offset_with_same_length :
    failsWith (checkedHeap [0, 1, 65, 1, 66] 5 [(3, [1, 65])])
      (.heapMismatch userStringHeap 3) = true := by
  simp only [checkedHeap, heapImage, fixture_eq]
  decide +kernel
#print axioms rejects_wrong_offset_with_same_length

/-- Bytes inside the image but starting beyond the heap cannot supply an entry. -/
theorem rejects_offset_past_heap_end :
    failsWith (checkedHeap [0, 1, 0, 1, 0] 2 [(3, [1, 0])])
      (.heapMismatch userStringHeap 3) = true := by
  simp only [checkedHeap, heapImage, fixture_eq]
  decide +kernel
#print axioms rejects_offset_past_heap_end

/-- Matching bytes beyond the declared heap end cannot extend an entry. -/
theorem rejects_crossing_heap_end :
    failsWith (checkedHeap [0, 3, 65, 0, 0] 4 [(1, [3, 65, 0, 0])])
      (.heapMismatch userStringHeap 1) = true := by
  simp only [checkedHeap, heapImage, fixture_eq]
  decide +kernel
#print axioms rejects_crossing_heap_end

/-- A two-byte prefix whose second byte is outside the heap is refused. -/
theorem rejects_prefix_at_heap_end :
    failsWith (checkedHeap [0, 128, 0] 2 [(1, [128, 0])])
      (.heapMismatch userStringHeap 1) = true := by
  simp only [checkedHeap, heapImage, fixture_eq]
  decide +kernel
#print axioms rejects_prefix_at_heap_end

/-- A length-prefixed UTF-16 user string containing repeated `A` characters. -/
private def textEntry (lengthPrefix : List Nat) (characters : Nat) : List Nat :=
  lengthPrefix ++ (List.replicate characters [65, 0]).flatten ++ [0]

/-- Sixty-four UTF-16 characters require a two-byte prefix for the 129-byte payload. -/
private def mediumEntry : List Nat := textEntry [128, 129] 64

/-- 8192 UTF-16 characters require a four-byte prefix for the 16385-byte payload. -/
private def longEntry : List Nat := textEntry [192, 0, 64, 1] 8192

/-- The two-byte length prefix and every payload byte match. -/
theorem accepts_two_byte_prefix :
    ok (checkedHeap (0 :: mediumEntry) (mediumEntry.length + 1) [(1, mediumEntry)]) = true := by
  simp only [checkedHeap, heapImage, fixture_eq]
  decide +kernel
#print axioms accepts_two_byte_prefix

/-- Both payload claims use the same physical 16,385-byte heap. -/
private theorem long_payload_checks :
    ok (checkedHeap (0 :: longEntry) (longEntry.length + 1) [(1, longEntry)]) = true ∧
    failsWith (checkedHeap (0 :: longEntry) (longEntry.length + 1) [(1, longEntry.dropLast)])
      (.heapMismatch userStringHeap 1) = true := by
  simp only [checkedHeap, heapImage, fixture_eq]
  decide +kernel
#print axioms long_payload_checks

/-- The four-byte length prefix and every payload byte match. -/
theorem accepts_four_byte_prefix :
    ok (checkedHeap (0 :: longEntry) (longEntry.length + 1) [(1, longEntry)]) = true :=
  long_payload_checks.1
#print axioms accepts_four_byte_prefix

/-- A four-byte prefix requires its entire declared payload. -/
theorem rejects_truncated_four_byte_payload :
    failsWith (checkedHeap (0 :: longEntry) (longEntry.length + 1) [(1, longEntry.dropLast)])
      (.heapMismatch userStringHeap 1) = true := long_payload_checks.2
#print axioms rejects_truncated_four_byte_payload

/-- The claim also accepts an interior offset whose bytes form a length-prefixed payload. -/
theorem accepts_interior_offset :
    ok (checkedHeap [0, 3, 1, 0, 0] 5 [(2, [1, 0])]) = true := by
  simp only [checkedHeap, heapImage, fixture_eq]
  decide +kernel
#print axioms accepts_interior_offset

/-- The Assembly block of a second image whose Assembly row differs in its major version, with its
    own heap numbering; `Tests.StrictBinding.Metadata.blocks` binds it to that image. -/
private def otherAssembly : CIL.Extraction.AssemblyMetadata :=
  { StrictFixture.assemblyBlock with
    assemblyRow := flipAt StrictFixture.assemblyBlock.assemblyRow 4 1 }

/-- A block from the second image is refused even though every carried method row is unchanged. -/
theorem rejects_other_assembly :
    failsWith (checked { carried with assembly := otherAssembly })
      (.rowMismatch assemblyToken) = true := by
  simp only [checked, fixture_eq]
  decide +kernel
#print axioms rejects_other_assembly

/-! ## Core-library reference -/

/-- The fixture's one AssemblyRef, `System.Runtime` with its publisher's token, as the core
    library of the slice. -/
theorem accepts_the_core_reference : ok (checked { carried with corlib := 1 }) = true := by
  rw [checked_claims]
  decide +kernel
#print axioms accepts_the_core_reference

/-- AssemblyRef 2, which the tables do not have, is refused. -/
theorem rejects_a_core_reference_the_tables_do_not_have :
    failsWith (checked { carried with corlib := 2 })
      (.tokenOutOfScope (tokenOf 0x23 2)) = true := by
  rw [checked_claims]
  decide +kernel
#print axioms rejects_a_core_reference_the_tables_do_not_have

/-- The fixture with its AssemblyRef naming the fixture itself, a library without a core name. -/
private def selfReferencing : Except AuditError PreparedImage := do
  let image ← fixture
  let (offset, width) ← image.layout.cellAt (tokenOf 0x23 1) 6
  let name ← image.layout.cell image.view (tokenOf 0x20 1) 7
  let bytes := imageBytes (flipByte StrictFixture.image 2021 1)
  prepareOne { identity := StrictFixture.identity,
               image := ImageBytes.ofBytes (writeLittle bytes offset width name) }

/-- A slice that names a library without a core name as its core library is refused. -/
theorem rejects_a_core_reference_to_another_library :
    failsWith (selfReferencing >>= fun image => corlibBound image 1)
      (.corlibMismatch StrictFixture.identity 1) = true := by
  simp only [selfReferencing, fixture_eq]
  decide +kernel
#print axioms rejects_a_core_reference_to_another_library

end Tests.StrictBinding.Slice
