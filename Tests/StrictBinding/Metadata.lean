import StrictBinding.Evidence
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

/-! Method metadata pages compose over one image preparation, and the distinct Assembly blocks
    reject a false block of a later method. -/

namespace Tests.StrictBinding.Metadata

open _root_.StrictBinding
open CIL.Extraction (MethodMetadata MethodEvidence)

/-- The identity of the fixture with its major version changed from one to zero. -/
private def otherIdentity : String :=
  "StrictFixture, Version=0.2.3.4, Culture=neutral, PublicKeyToken=null"

/-- Two distinct assembly versions, with the changed version after the original. -/
private def pinned : List PinnedImage :=
  [{ identity := StrictFixture.identity, image := StrictFixture.image },
   { identity := otherIdentity, image := flipByte StrictFixture.image 1420 1 }]

/-- A method carrying the fixture's rows and heaps. -/
private def first : MethodMetadata := { own := StrictFixture.slice }

/-- A method in the other assembly also carrying metadata from the fixture. -/
private def second : MethodMetadata :=
  { own := { assembly := { StrictFixture.assemblyBlock with
      identity := otherIdentity,
      assemblyRow := flipAt StrictFixture.assemblyBlock.assemblyRow 4 1 } },
    others := [StrictFixture.slice] }

/-- Two different methods, one on each page. -/
private def claims : List MethodMetadata := [first, second]

/-- Both images decode under their own distinct identities. -/
theorem prepared : ok (prepare pinned) = true := by decide +kernel
#print axioms prepared

/-- The first page's method metadata belongs to its selected image. -/
theorem first_page : ClaimsHold methodMetadataBound pinned (claimPage claims 1 0) := by
  decide +kernel
#print axioms first_page

/-- The second page checks both the owning assembly and a referenced assembly. -/
theorem second_page : ClaimsHold methodMetadataBound pinned (claimPage claims 1 1) := by
  decide +kernel
#print axioms second_page

/-- Independently checked pages cover the complete method metadata claim list. -/
theorem composed_pages : ClaimsHold methodMetadataBound pinned claims :=
  claimsHold_of_pages (size := 1) (count := 2) prepared (by decide +kernel)
    (.succ second_page (.succ first_page .zero))
#print axioms composed_pages

/-- Each distinct Assembly block the two methods carry belongs to its selected image. -/
theorem blocks : ClaimsHold assemblyBlockBound pinned (assemblyBlocks claims) := by
  decide +kernel
#print axioms blocks

/-- Page results bind the metadata fields of evidence records to selected image bytes. -/
theorem evidence_from_pages (left right : MethodEvidence)
    (leftMetadata : left.body.metadata = first) (rightMetadata : right.body.metadata = second) :
    Exists fun images => And (prepare pinned = .ok images)
      (forall item, List.Mem item [left, right] ->
        forall slice, List.Mem slice item.body.metadata.slices ->
          Exists fun image => And (located images slice.assembly.identity = .ok image)
            (SliceMatches image slice)) := by
  apply sliceMatches_of_metadataRowsBound
  have carried : metadataClaims [left, right] = claims := by
    simp only [metadataClaims, claims, List.map_cons, List.map_nil, leftMetadata, rightMetadata]
  unfold MetadataRowsBound
  rw [carried]
  exact And.intro blocks composed_pages
#print axioms evidence_from_pages

/-- The second method falsely carries another version's row for its referenced assembly. -/
private def falseSecond : MethodMetadata :=
  { second with others := [{ StrictFixture.slice with
      assembly := { StrictFixture.assemblyBlock with
        assemblyRow := flipAt StrictFixture.assemblyBlock.assemblyRow 4 1 } }] }

/-- The changed block keeps the fixture's identity yet stays a distinct block to check, since
    blocks are compared whole. -/
theorem keeps_blocks_of_one_identity : (assemblyBlocks [first, falseSecond]).length = 3 := by
  decide +kernel
#print axioms keeps_blocks_of_one_identity

/-- A valid block of the first method cannot make a changed Assembly row of the second pass. -/
theorem rejects_false_second_block :
    failsWith (checkAll assemblyBlockBound pinned (assemblyBlocks [first, falseSecond]))
      (.rowMismatch assemblyToken) = true := by decide +kernel
#print axioms rejects_false_second_block

end Tests.StrictBinding.Metadata
