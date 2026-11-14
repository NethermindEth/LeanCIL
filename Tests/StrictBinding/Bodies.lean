import StrictBinding.Bind
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

/-!
# Strict binding tests: method bodies

Every method body of the fixture, read by System.Reflection.Metadata, must be found by the audit
at the place its own MethodDef row gives. Each rejection then changes one fact of a file or a
claim that passes and asserts the exact error: a body claimed under another token, bytes that
differ from the file, a row that points elsewhere, an address no section holds, a method without
an IL body, a token outside the table, an identity the file does not spell, an image that is not
well formed and a section table that misdirects the container. With two images pinned, a claim
is checked in the one its identity names. The expected positions come from
`StrictFixture.expectedFacts`, which the reader generated, never from the audit's own decoding.
-/

namespace Tests.StrictBinding.Bodies

open _root_.StrictBinding

/-- The relative virtual address and file offset the reader reports for MethodDef row `row`. -/
private def position (row : Nat) : Nat × Nat :=
  (StrictFixture.expectedFacts.filterMap fun fact =>
    match fact with
    | .method found rva offset => if found == row then some (rva, offset) else none
    | _ => none).headD (0, 0)

/-- The file offset of MethodDef row `row`, from the reader's table position and row size. -/
private def rowStart (row : Nat) : Nat :=
  (StrictFixture.expectedFacts.filterMap fun fact =>
    match fact with
    | .table 0x06 _ size offset => some (offset + (row - 1) * size)
    | _ => none).headD 0

/-- The MethodDef token of row `row`. -/
private def tokenOfRow (row : Nat) : Nat := tokenOf 0x06 row

/-- The bytes of the body of the method at index `index` of the fixture's bodies. -/
private def bodyBytes (index : Nat) : List Nat := (StrictFixture.bodies.getD index default).2.2

/-- The fixture image pinned under its own identity. -/
private def pinned : List PinnedImage :=
  [{ identity := StrictFixture.identity, image := StrictFixture.image }]

/-- A claim about the fixture's assembly. -/
private def claim (token : Nat) (bytes : List Nat) : BodyClaim :=
  { identity := StrictFixture.identity, token, bytes }

/-- The pinned fixture with its bytes changed. -/
private def pinnedWith (image : ImageBytes) : List PinnedImage :=
  [{ identity := StrictFixture.identity, image }]

/-- Every method body of the fixture, claimed under its own token. -/
private def claims : List BodyClaim :=
  StrictFixture.bodies.map fun (_, token, bytes) => claim token bytes

theorem every_fixture_body_is_found_at_its_row : ClaimsHold bodyClaimBound pinned claims := by
  decide +kernel
#print axioms every_fixture_body_is_found_at_its_row

/-- The ten claims in four pages of three, composed as a generated module composes its pages. -/
theorem every_fixture_body_is_found_in_pages : ClaimsHold bodyClaimBound pinned claims :=
  claimsHold_of_pages (size := 3) (count := 4) (by decide +kernel) (by decide +kernel)
    (.succ (by decide +kernel) (.succ (by decide +kernel) (.succ (by decide +kernel)
      (.succ (by decide +kernel) .zero))))
#print axioms every_fixture_body_is_found_in_pages

/-- The claims with one byte of the fifth body changed. -/
private def tamperedClaims : List BodyClaim :=
  claims.mapIdx fun index claim =>
    if index == 4 then { claim with bytes := claim.bytes.set 1 0xFF } else claim

/-- A changed body in the second page makes that page false, so the pages do not compose. -/
theorem rejects_a_changed_body_in_the_second_page :
    ¬ ClaimsHold bodyClaimBound pinned (claimPage tamperedClaims 3 1) := by decide +kernel
#print axioms rejects_a_changed_body_in_the_second_page

/-- The fixture has a tiny and a fat header body, which the claims cover. -/
theorem fixture_has_tiny_and_fat_bodies :
    (bodyBytes 0).head? = some 0x12 ∧ (bodyBytes 1).head? = some 0x13 := by decide +kernel
#print axioms fixture_has_tiny_and_fat_bodies

/-- Body bytes of another method do not belong to the token: the error names the row's own
    address and the offset it maps to. -/
theorem rejects_the_body_of_another_method :
    failsWith (checkAll bodyClaimBound pinned [claim (tokenOfRow 1) (bodyBytes 1)])
      (.bodyMismatch (tokenOfRow 1) (position 1).1 (position 1).2) = true := by
  decide +kernel
#print axioms rejects_the_body_of_another_method

/-- One changed byte of a claimed body is not the file's body. -/
theorem rejects_a_changed_byte_in_the_claim :
    failsWith (checkAll bodyClaimBound pinned [claim (tokenOfRow 1) ((bodyBytes 0).set 4 0x2B)])
      (.bodyMismatch (tokenOfRow 1) (position 1).1 (position 1).2) = true := by
  decide +kernel
#print axioms rejects_a_changed_byte_in_the_claim

/-- A claim that is true of the unchanged file is false of a file with one body byte changed. -/
theorem rejects_a_changed_byte_in_the_file :
    failsWith (checkAll bodyClaimBound
        (pinnedWith (flipByte StrictFixture.image ((position 1).2 + 4) 0x01))
        [claim (tokenOfRow 1) (bodyBytes 0)])
      (.bodyMismatch (tokenOfRow 1) (position 1).1 (position 1).2) = true := by
  decide +kernel
#print axioms rejects_a_changed_byte_in_the_file

/-- Where the file says a body is comes from its MethodDef row: when the row of the first method
    gives the address of the second, the first method's own bytes are not there. -/
theorem rejects_a_row_that_points_at_another_body :
    failsWith (checkAll bodyClaimBound
        (pinnedWith (flipByte StrictFixture.image (rowStart 1) 0x08))
        [claim (tokenOfRow 1) (bodyBytes 0)])
      (.bodyMismatch (tokenOfRow 1) (position 2).1 (position 2).2) = true := by
  decide +kernel
#print axioms rejects_a_row_that_points_at_another_body

/-- An address that no section holds is not mapped. -/
theorem rejects_a_row_outside_every_section :
    failsWith (checkAll bodyClaimBound
        (pinnedWith (flipByte StrictFixture.image (rowStart 1 + 2) 0x01))
        [claim (tokenOfRow 1) (bodyBytes 0)])
      (.pe (.unmappedRva ((position 1).1 + 0x10000) (bodyBytes 0).length)) = true := by
  decide +kernel
#print axioms rejects_a_row_outside_every_section

/-- A zero address means the method has no body. -/
theorem rejects_a_method_without_a_body :
    failsWith (checkAll bodyClaimBound (pinnedWith (flipBytes StrictFixture.image
          [(rowStart 1, (position 1).1 % 256), (rowStart 1 + 1, (position 1).1 / 256 % 256)]))
        [claim (tokenOfRow 1) (bodyBytes 0)])
      (.noIlBody (tokenOfRow 1)) = true := by
  decide +kernel
#print axioms rejects_a_method_without_a_body

/-- A method whose implementation flags say native has no IL body. -/
theorem rejects_a_native_method :
    failsWith (checkAll bodyClaimBound
        (pinnedWith (flipByte StrictFixture.image (rowStart 1 + 4) 0x01))
        [claim (tokenOfRow 1) (bodyBytes 0)])
      (.noIlBody (tokenOfRow 1)) = true := by
  decide +kernel
#print axioms rejects_a_native_method

/-- A body claimed under a TypeDef token is rejected. -/
theorem rejects_a_token_that_is_not_a_method :
    failsWith (checkAll bodyClaimBound pinned [claim (tokenOf 0x02 1) (bodyBytes 0)])
      (.notMethodDef (tokenOf 0x02 1)) = true := by
  decide +kernel
#print axioms rejects_a_token_that_is_not_a_method

/-- A MethodDef token past the last row is outside the table. -/
theorem rejects_a_row_past_the_table :
    failsWith (checkAll bodyClaimBound pinned [claim (tokenOfRow 11) (bodyBytes 0)])
      (.tokenOutOfScope (tokenOfRow 11)) = true := by
  decide +kernel
#print axioms rejects_a_row_past_the_table

/-- The identity of the fixture with another version. -/
private def otherVersion : String :=
  "StrictFixture, Version=2.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- An image pinned under an identity its Assembly row does not spell is rejected. -/
theorem rejects_an_identity_the_file_does_not_spell :
    failsWith (checkAll bodyClaimBound
        [{ identity := otherVersion, image := StrictFixture.image }] claims)
      (.identityMismatch otherVersion) = true := by
  decide +kernel
#print axioms rejects_an_identity_the_file_does_not_spell

/-- A claim about an assembly that no image is pinned for is rejected. -/
theorem rejects_a_claim_about_an_unpinned_assembly :
    failsWith (checkAll bodyClaimBound pinned
        [{ identity := "Other, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null",
           token := tokenOfRow 1, bytes := bodyBytes 0 }])
      (.unpinned "Other, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null") = true := by
  decide +kernel
#print axioms rejects_a_claim_about_an_unpinned_assembly

/-- Two images with one identity would let a claim name either. -/
theorem rejects_two_images_with_one_identity :
    failsWith (checkAll bodyClaimBound
        (pinned ++ pinned) claims) (.duplicateImage StrictFixture.identity) =
      true := by
  decide +kernel
#print axioms rejects_two_images_with_one_identity

/-- The file offset of the Assembly row, from the reader's table position. -/
private def assemblyRowStart : Nat :=
  (StrictFixture.expectedFacts.filterMap fun fact =>
    match fact with
    | .table 0x20 _ _ offset => some offset
    | _ => none).headD 0

/-- The fixture with its major version, which follows the four-byte hash algorithm of the
    Assembly row, changed from 1 to 2, and one byte of its first body changed. -/
private def otherImage : ImageBytes :=
  flipBytes StrictFixture.image [(assemblyRowStart + 4, 0x03), ((position 1).2 + 4, 0x01)]

/-- The identity the changed fixture's Assembly row spells. -/
private def otherIdentity : String :=
  "StrictFixture, Version=2.2.3.4, Culture=neutral, PublicKeyToken=null"

/-- The fixture and its changed copy pinned under their own identities, in either order. -/
private def bothPinned (otherFirst : Bool) : List PinnedImage :=
  let images := [{ identity := StrictFixture.identity, image := StrictFixture.image },
    { identity := otherIdentity, image := otherImage }]
  if otherFirst then images.reverse else images

/-- With two images pinned, each claim is checked in the image its identity names, whatever the
    order of the pins: the first body holds in the fixture and is not in the changed copy. -/
theorem finds_the_image_a_claim_names : ∀ otherFirst : Bool,
    ClaimsHold bodyClaimBound (bothPinned otherFirst) claims ∧
      failsWith (checkAll bodyClaimBound (bothPinned otherFirst)
          [{ identity := otherIdentity, token := tokenOfRow 1, bytes := bodyBytes 0 }])
        (.bodyMismatch (tokenOfRow 1) (position 1).1 (position 1).2) = true := by
  decide +kernel
#print axioms finds_the_image_a_claim_names

/-- A chunk at or above `2 ^ 512` is rejected before anything is decoded. -/
theorem rejects_a_chunk_out_of_bounds :
    failsWith (checkAll bodyClaimBound (pinnedWith { StrictFixture.image with
        pages := [(StrictFixture.image.pages.headD []).set 0
          ((StrictFixture.image.pages.headD []).headD 0 + 2 ^ 512)] }) claims)
      .malformedImage = true := by
  decide +kernel
#print axioms rejects_a_chunk_out_of_bounds

/-- The fixture's first section header is at `0x178`; its raw data pointer, `0x200`, moves to
    `0x400`. The CLI header is no longer where the section table sends its address. -/
theorem rejects_a_section_table_that_misdirects_the_container :
    failsWith (checkAll bodyClaimBound
        (pinnedWith (flipByte StrictFixture.image (0x178 + 21) 0x06)) claims)
      (.pe .badCliHeader) = true := by
  decide +kernel
#print axioms rejects_a_section_table_that_misdirects_the_container

end Tests.StrictBinding.Bodies
