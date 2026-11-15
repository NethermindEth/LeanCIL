import StrictBinding.Rows

/-!
Carried user strings and complete metadata slices checked against one prepared image.
Assembly entries and row entries have separate numberings, as the extractor emits them.
-/

namespace StrictBinding

open CIL.Extraction (ByteEntry MetadataSlice userStringHeap)
open CIL.Safety (except_bind_ok)

/-- Each keyed offset has the image's prefix and exact payload inside the heap.
    Entry starts reached by a heap walk or named by code are outside this claim. -/
def UserStringsMatch (image : PreparedImage) (entries : List ByteEntry) : Prop :=
  forall entry, List.Mem entry entries -> SizedAt image image.layout.pe.userStrings entry.1 entry.2

/-- User strings at image offsets, with fixed prefix reads and one full comparison per entry.
    The cost is linear in the entries and their bytes, independent of rows and methods. -/
def userStringsBound (image : PreparedImage) : List ByteEntry -> Except AuditError Unit
  | [] => pure ()
  | entry :: rest => do
    entryBound userStringHeap (sizedFound image image.layout.pe.userStrings) entry.1 entry
    userStringsBound image rest

/-- Success binds each user string's prefix, length, bounds and bytes to the image. -/
theorem userStringsMatch_of_userStringsBound {image : PreparedImage}
    (bounded : image.view.Bounded) {entries : List ByteEntry}
    (bound : userStringsBound image entries = .ok ()) : UserStringsMatch image entries := by
  induction entries with
  | nil => intro entry member; cases member
  | cons entry rest onRest =>
    cases except_bind_ok bound with
    | intro value results =>
      intro other member
      cases member with
      | head => exact sizedAt_of_sizedFound bounded (found_of_entryBound results.1)
      | tail _ member => exact onRest results.2 other member

#print axioms userStringsMatch_of_userStringsBound

/-- Assembly and row heaps have separate numberings; user-string keys are image offsets.
    Identity, key tokens, corlib and links are outside this claim. -/
def SliceMatches (image : PreparedImage) (slice : MetadataSlice) : Prop :=
  And (AssemblyMatches image slice.assembly)
    (And (RowsMatch image slice.rows slice.strings slice.blobs)
      (UserStringsMatch image slice.userStrings))

/-- The Assembly block, rows and carried heaps checked against one prepared image.
    Cost is the assembly and row checks plus the user-string entries and bytes compared. -/
def sliceBound (image : PreparedImage) (slice : MetadataSlice) : Except AuditError Unit := do
  assemblyBound image slice.assembly
  rowsBound image slice.rows slice.strings slice.blobs
  userStringsBound image slice.userStrings

/-- Success binds the assembly block, rows and all carried heaps to the prepared image. -/
theorem sliceMatches_of_sliceBound {image : PreparedImage} {slice : MetadataSlice}
    (bounded : image.view.Bounded) (bound : sliceBound image slice = .ok ()) :
    SliceMatches image slice := by
  cases except_bind_ok bound with
  | intro value results =>
    cases except_bind_ok results.2 with
    | intro value checks =>
      exact And.intro (assemblyMatches_of_assemblyBound bounded results.1)
        (And.intro (rowsMatch_of_rowsBound bounded checks.1)
          (userStringsMatch_of_userStringsBound bounded checks.2))

#print axioms sliceMatches_of_sliceBound

end StrictBinding
