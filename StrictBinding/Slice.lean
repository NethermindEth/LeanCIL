import StrictBinding.Rows

/-!
Carried user strings and complete metadata slices checked against one prepared image.
Assembly entries and row entries have separate numberings, as the extractor emits them.
-/

namespace StrictBinding

open CIL.Extraction (ByteEntry MetadataSlice checkedTokenOf userStringHeap)
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

/-- The core-library AssemblyRef a slice names, when it names one, is a row of the image that
    names a core library with its publisher's token. -/
def CoreReferenceAt (image : PreparedImage) (corlib : Nat) : Prop :=
  corlib = 0 ∨ ∃ token,
    checkedTokenOf CIL.Extraction.Table.assemblyRef corlib AuditError.rowOverflow = .ok token ∧
      coreAssemblyAt image token 0 = .ok true

/-- The core-library AssemblyRef row of a slice, if any, names a core library in the image. One
    row read, so the cost does not grow with the slice. -/
def corlibBound (image : PreparedImage) (corlib : Nat) : Except AuditError Unit := do
  if corlib == 0 then return
  let token ← checkedTokenOf CIL.Extraction.Table.assemblyRef corlib .rowOverflow
  unless ← coreAssemblyAt image token 0 do throw (.corlibMismatch image.identity corlib)

/-- A successful core-library check means `CoreReferenceAt`. -/
theorem coreReferenceAt_of_corlibBound {image : PreparedImage} {corlib : Nat}
    (bound : corlibBound image corlib = .ok ()) : CoreReferenceAt image corlib := by
  unfold corlibBound at bound
  unfold CoreReferenceAt
  by_cases none : corlib = 0
  · exact Or.inl none
  · right
    simp only [none, beq_iff_eq, if_false] at bound
    obtain ⟨token, tokenRead, bound⟩ := except_bind_ok bound
    obtain ⟨core, coreRead, bound⟩ := except_bind_ok bound
    refine ⟨token, tokenRead, ?_⟩
    cases core
    · exact absurd bound throw_ne_ok
    · exact coreRead

#print axioms coreReferenceAt_of_corlibBound

/-- Assembly and row heaps have separate numberings; user-string keys are image offsets. The
    core-library AssemblyRef names a core library. Links are outside this claim. -/
def SliceMatches (image : PreparedImage) (slice : MetadataSlice) : Prop :=
  And (AssemblyMatches image slice.assembly)
    (And (RowsMatch image slice.rows slice.strings slice.blobs)
      (And (UserStringsMatch image slice.userStrings) (CoreReferenceAt image slice.corlib)))

/-- The rows, carried heaps and core-library AssemblyRef of a slice checked against one prepared
    image, without its Assembly block. Cost is the row check plus the user-string entries and
    bytes compared, plus one AssemblyRef row. -/
def sliceContentsBound (image : PreparedImage) (slice : MetadataSlice) :
    Except AuditError Unit := do
  rowsBound image slice.rows slice.strings slice.blobs
  userStringsBound image slice.userStrings
  corlibBound image slice.corlib

/-- The Assembly block, rows and carried heaps checked against one prepared image.
    Cost is the assembly check plus the cost of `sliceContentsBound`. -/
def sliceBound (image : PreparedImage) (slice : MetadataSlice) : Except AuditError Unit := do
  assemblyBound image slice.assembly
  sliceContentsBound image slice

/-- A successful Assembly block check and contents check bind the whole slice to the image. -/
theorem sliceMatches_of_bounds {image : PreparedImage} {slice : MetadataSlice}
    (bounded : image.view.Bounded) (assembly : assemblyBound image slice.assembly = .ok ())
    (contents : sliceContentsBound image slice = .ok ()) : SliceMatches image slice := by
  unfold sliceContentsBound at contents
  obtain ⟨_, rowsChecked, contents⟩ := except_bind_ok contents
  obtain ⟨_, userStringsChecked, corlibChecked⟩ := except_bind_ok contents
  exact And.intro (assemblyMatches_of_assemblyBound bounded assembly)
    (And.intro (rowsMatch_of_rowsBound bounded rowsChecked)
      (And.intro (userStringsMatch_of_userStringsBound bounded userStringsChecked)
        (coreReferenceAt_of_corlibBound corlibChecked)))

#print axioms sliceMatches_of_bounds

/-- Success binds the assembly block, rows and all carried heaps to the prepared image. -/
theorem sliceMatches_of_sliceBound {image : PreparedImage} {slice : MetadataSlice}
    (bounded : image.view.Bounded) (bound : sliceBound image slice = .ok ()) :
    SliceMatches image slice := by
  cases except_bind_ok bound with
  | intro value results =>
    cases value
    exact sliceMatches_of_bounds bounded results.1 results.2

#print axioms sliceMatches_of_sliceBound

end StrictBinding
