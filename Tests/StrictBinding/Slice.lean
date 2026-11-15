import StrictBinding.Slice
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

/-! Whole metadata checks and user-string offsets, payloads, prefixes and heap bounds. -/

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

/-- The complete carried metadata, including a one-byte length prefix, passes. -/
theorem accepts_fixture : ok (checked carried) = true := by decide +kernel
#print axioms accepts_fixture

/-- A changed user-string byte is refused by the complete check. -/
theorem rejects_changed_byte :
    failsWith (checked { carried with userStrings := [(1, [1, 1])] })
      (.heapMismatch userStringHeap 1) = true := by decide +kernel
#print axioms rejects_changed_byte

/-- A payload shorter than its image length prefix is refused. -/
theorem rejects_truncated_payload :
    failsWith (checked { carried with userStrings := [(1, [1])] })
      (.heapMismatch userStringHeap 1) = true := by decide +kernel
#print axioms rejects_truncated_payload

/-- An extra byte after the exact payload is refused. -/
theorem rejects_extra_byte :
    failsWith (checked { carried with userStrings := [(1, [1, 0, 0])] })
      (.heapMismatch userStringHeap 1) = true := by decide +kernel
#print axioms rejects_extra_byte

/-- A key names an image offset, so the same bytes at another offset are refused. -/
theorem rejects_wrong_offset :
    failsWith (checked { carried with userStrings := [(2, [1, 0])] })
      (.heapMismatch userStringHeap 2) = true := by decide +kernel
#print axioms rejects_wrong_offset

/-- A later user string is checked even when the first entry matches. -/
theorem rejects_false_second_entry :
    failsWith (checked { carried with userStrings := [(1, [1, 0]), (2, [1, 1])] })
      (.heapMismatch userStringHeap 2) = true := by decide +kernel
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
      (.heapMismatch userStringHeap 3) = true := by decide +kernel
#print axioms rejects_wrong_offset_with_same_length

/-- Bytes inside the image but starting beyond the heap cannot supply an entry. -/
theorem rejects_offset_past_heap_end :
    failsWith (checkedHeap [0, 1, 0, 1, 0] 2 [(3, [1, 0])])
      (.heapMismatch userStringHeap 3) = true := by decide +kernel
#print axioms rejects_offset_past_heap_end

/-- Matching bytes beyond the declared heap end cannot extend an entry. -/
theorem rejects_crossing_heap_end :
    failsWith (checkedHeap [0, 3, 65, 0, 0] 4 [(1, [3, 65, 0, 0])])
      (.heapMismatch userStringHeap 1) = true := by decide +kernel
#print axioms rejects_crossing_heap_end

/-- A two-byte prefix whose second byte is outside the heap is refused. -/
theorem rejects_prefix_at_heap_end :
    failsWith (checkedHeap [0, 128, 0] 2 [(1, [128, 0])])
      (.heapMismatch userStringHeap 1) = true := by decide +kernel
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
  decide +kernel
#print axioms accepts_two_byte_prefix

/-- The four-byte length prefix and every payload byte match. -/
theorem accepts_four_byte_prefix :
    ok (checkedHeap (0 :: longEntry) (longEntry.length + 1) [(1, longEntry)]) = true := by
  decide +kernel
#print axioms accepts_four_byte_prefix

/-- A four-byte prefix requires its entire declared payload. -/
theorem rejects_truncated_four_byte_payload :
    failsWith (checkedHeap (0 :: longEntry) (longEntry.length + 1) [(1, longEntry.dropLast)])
      (.heapMismatch userStringHeap 1) = true := by decide +kernel
#print axioms rejects_truncated_four_byte_payload

/-- The claim also accepts an interior offset whose bytes form a length-prefixed payload. -/
theorem accepts_interior_offset :
    ok (checkedHeap [0, 3, 1, 0, 0] 5 [(2, [1, 0])]) = true := by decide +kernel
#print axioms accepts_interior_offset

/-- A second image differs in the Assembly row's major version. -/
private def otherImage : Except AuditError PreparedImage :=
  prepareOne
    { identity := "StrictFixture, Version=0.2.3.4, Culture=neutral, PublicKeyToken=null",
      image := flipByte StrictFixture.image 1420 1 }

/-- The Assembly block copied from that second image, with its own heap numbering. -/
private def otherAssembly : CIL.Extraction.AssemblyMetadata :=
  { StrictFixture.assemblyBlock with
    identity := "StrictFixture, Version=0.2.3.4, Culture=neutral, PublicKeyToken=null",
    assemblyRow := flipAt StrictFixture.assemblyBlock.assemblyRow 4 1 }

/-- The second block belongs to its own image. -/
theorem accepts_other_assembly :
    ok (otherImage >>= fun image => assemblyBound image otherAssembly) = true := by decide +kernel
#print axioms accepts_other_assembly

/-- A block from the second image is refused even though every carried method row is unchanged. -/
theorem rejects_other_assembly :
    failsWith (checked { carried with assembly := otherAssembly })
      (.rowMismatch assemblyToken) = true := by decide +kernel
#print axioms rejects_other_assembly

end Tests.StrictBinding.Slice
