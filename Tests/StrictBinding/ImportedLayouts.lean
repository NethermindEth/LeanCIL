import StrictBinding.ImportedLayouts
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

/-! Imported layout checks for a slot that selected StrictFixture.Overlay, and forged rows. -/

namespace Tests.StrictBinding.ImportedLayouts

open CIL.Extraction _root_.StrictBinding

/-- Two 32-bit fields at offsets zero and four occupy the eight-byte explicit Overlay. -/
private def overlay : RawLayout := {
  identity := StrictFixture.identity ++ "::StrictFixture.Overlay", explicit := true,
  declaration := [⟨name!"StrictFixture", name!"Overlay"⟩],
  packing := 0, declaredSize := 8, fields := [⟨.signed32, some 0⟩, ⟨.signed32, some 4⟩] }

/-- The import identity that names the slot in a rejection. -/
private def slotIdentity := "StrictFixture::Read(StrictFixture.Overlay)"

/-- A slot whose selected implementation layouts are `layouts`. -/
private def slot (layouts : List RawLayout) : CIL.ImportSlot :=
  { identity := slotIdentity, closureDigest := "", parameterCount := 1, hasThis := false,
    returnsValue := false, layouts := { published := layouts, actual := layouts } }

/-- Check the slots against the supplied version of the compiled implementation. -/
private def check (imports : List CIL.ImportSlot) (bytes := StrictFixture.image) :=
  checkImportedLayouts [⟨StrictFixture.identity, bytes⟩] imports

/-- The rejection of a forged row names its slot and its layout. -/
private def forged := AuditError.importedLayoutMismatch slotIdentity overlay.identity

/-- The image's own row is reconfirmed; a forged offset, size, packing, field type or layout kind
    is refused for its slot; no selected layout or a layout of an unpinned image is partial. -/
theorem selection :
    let missing := {overlay with identity := "Other, Version=1.0.0.0::Missing"}
    (check [slot [overlay]]).toOption = some true ∧
    failsWith (check [slot [{overlay with fields := [⟨.signed32, some 0⟩, ⟨.signed32, some 2⟩]}]])
      forged = true ∧
    failsWith (check [slot [{overlay with declaredSize := 16}]]) forged = true ∧
    failsWith (check [slot [{overlay with packing := 1}]]) forged = true ∧
    failsWith (check [slot [{overlay with fields := [⟨.signed32, some 0⟩, ⟨.unsigned32, some 4⟩]}]])
      forged = true ∧
    failsWith (check [slot [{overlay with explicit := false}]]) forged = true ∧
    (check []).toOption = some false ∧
    (check [slot []]).toOption = some false ∧
    (check [slot [missing], slot [overlay]]).toOption = some false ∧
    failsWith (check [slot [missing], slot [{overlay with packing := 1}]]) forged = true := by
  decide +kernel
#print axioms selection

/-- Altered FieldLayout and ClassLayout bytes in the image refuse the slot's unaltered row. -/
theorem altered_tables :
    let changed := fun (table column mask : Nat) => StrictFixture.expectedFacts.findSome? fun
      | .table number _ _ start =>
        if number == table then some (flipByte StrictFixture.image (start + column) mask) else none
      | _ => none
    let rejects := fun bytes => failsWith (check [slot [overlay]] bytes) forged
    (changed 15 2 8).map rejects = some true ∧
    (changed 16 6 4).map rejects = some true := by decide +kernel
#print axioms altered_tables

end Tests.StrictBinding.ImportedLayouts
