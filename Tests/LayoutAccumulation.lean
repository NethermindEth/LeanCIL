import CIL.Extraction.Layout

/-! Field accumulation preserves declaration order and all metadata rejection boundaries. -/
namespace Tests.LayoutAccumulation
open CIL CIL.Extraction

/-- Mixed widths expose any reversal of declaration order or alignment state. -/
def mixed : RawLayout := {
    explicit := false, packing := 0, declaredSize := 0,
    fields := [⟨.unsigned8, none⟩, ⟨.unsigned64, none⟩, ⟨.unsigned16, none⟩] }

/-- Field order and padding agree with sequential layout. -/
theorem ordered : computeLayout #[] mixed =
    some ⟨⟨24, [⟨0, 1, false⟩, ⟨8, 8, false⟩, ⟨16, 2, false⟩]⟩, 8⟩ := by decide +kernel
#print axioms ordered

/-- Explicit offsets can overlap and need not increase in declaration order. -/
theorem overlapping : computeLayout #[] { mixed with
      explicit := true, declaredSize := 16,
      fields := [⟨.unsigned64, some 2⟩, ⟨.unsigned32, some 0⟩] } =
    some ⟨⟨16, [⟨2, 8, false⟩, ⟨0, 4, false⟩]⟩, 8⟩ := by decide +kernel
#print axioms overlapping

/-- Empty layouts retain their one-byte size and missing nested layouts reject. -/
theorem emptyAndMissing :
    computeLayout #[] { mixed with fields := [] } = some ⟨⟨1, []⟩, 1⟩ ∧
    computeLayout #[] { mixed with fields := [⟨.aggregate 0, none⟩] } = none := by decide +kernel
#print axioms emptyAndMissing

/-- Invalid packing, mixed auto layout and absent or overflowing offsets still reject. -/
theorem invalid : computeLayout #[] { mixed with packing := 3 } = none ∧
    computeLayout #[] { mixed with auto := true } = none ∧
    computeLayout #[] { mixed with explicit := true, declaredSize := 32 } = none ∧
    computeLayout #[] { mixed with
        explicit := true, declaredSize := 65536,
        fields := [⟨.unsigned32, some 65535⟩] } = none := by decide +kernel
#print axioms invalid

/-- Architecture-dependent vector alignment and the scalar restriction are unchanged. -/
theorem vectorProfiles :
    computeLayout #[] { mixed with fields := [⟨.vector256, none⟩] } .scalar = none ∧
    computeLayout #[] { mixed with fields := [⟨.vector256, none⟩] } .arm64 =
      some ⟨⟨32, [⟨0, 32, false⟩]⟩, 16⟩ := by decide +kernel
#print axioms vectorProfiles
end Tests.LayoutAccumulation
