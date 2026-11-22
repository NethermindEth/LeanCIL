import StrictBinding.LayoutContent
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

/-! Physical layout checks for the compiled StrictFixture.Overlay and altered metadata. -/

namespace Tests.StrictBinding.LayoutContent

open CIL.Extraction _root_.StrictBinding

/-- Two 32-bit fields at offsets zero and four occupy the eight-byte explicit Overlay. -/
private def overlay : RawLayout := {
  identity := StrictFixture.identity ++ "::StrictFixture.Overlay", explicit := true,
  packing := 0, declaredSize := 8, fields := [⟨.signed32, some 0⟩, ⟨.signed32, some 4⟩] }

/-- Compare raw layouts against the supplied version of the same compiled assembly. -/
private def check (layouts : List RawLayout) (bytes := StrictFixture.image) :=
  checkLayoutContent [⟨StrictFixture.identity, bytes⟩] layouts []

/-- Missing images and empty selections leave the fact uncovered. A second conflicting layout
    still fails when the first layout lacks a pinned image. -/
theorem selection :
    let missing := {overlay with identity := "Other, Version=1.0.0.0::Missing"}
    (check [overlay]).toOption = some true ∧
    (check []).toOption = some false ∧
    (check [missing, overlay]).toOption = some false ∧
    failsWith (check [missing, {overlay with packing := 1}])
      (.layoutMismatch overlay.identity) = true := by decide +kernel
#print axioms selection

/-- The FieldLayout and ClassLayout rows reject altered offsets and sizes in the physical PE. -/
theorem altered_tables :
    let changed := fun (table column mask : Nat) => StrictFixture.expectedFacts.findSome? fun
      | .table number _ _ start =>
        if number == table then some (flipByte StrictFixture.image (start + column) mask) else none
      | _ => none
    let rejects := fun bytes => failsWith (check [overlay] bytes) (.layoutMismatch overlay.identity)
    (changed 15 2 8).map rejects = some true ∧
    (changed 16 6 4).map rejects = some true := by decide +kernel
#print axioms altered_tables

end Tests.StrictBinding.LayoutContent
