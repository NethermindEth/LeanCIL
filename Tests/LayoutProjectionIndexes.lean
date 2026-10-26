import CIL.Extraction.LayoutProjection

/-! Exact indexed projection checks, including malformed catalogs and nested references. -/
namespace Tests.LayoutProjectionIndexes
open CIL CIL.Extraction

/-- A single readable byte with a distinct metadata identity. -/
def leaf (identity : String) : RawLayout := {
  identity, explicit := false, packing := 0, declaredSize := 0,
  fields := [⟨.unsigned8, none⟩] }

/-- The layout shared by the one-byte leaves. -/
def byteLayout : ComputedLayout := ⟨⟨1, [⟨0, 1, false⟩]⟩, 1⟩

/-- Reordering distinct public leaves remains permitted. -/
theorem reordered : LayoutProjectionValid [leaf "a", leaf "b"]
    #[byteLayout, byteLayout] [leaf "b", leaf "a"] #[byteLayout, byteLayout] [1, 0]
    .scalar := by decide +kernel
#print axioms reordered

/-- Empty catalogs remain valid. -/
theorem empty : LayoutProjectionValid [] #[] [] #[] [] .scalar := by decide +kernel
#print axioms empty

/-- Duplicate artifact identity cannot be hidden by omitting it from the public catalog. -/
theorem duplicateArtifact : ¬ LayoutProjectionValid [leaf "a", leaf "a"]
    #[byteLayout, byteLayout] [leaf "a"] #[byteLayout] [0] .scalar := by decide +kernel
#print axioms duplicateArtifact

/-- Distinct spellings are compared by full identity. -/
theorem distinctCase : LayoutProjectionValid [leaf "a", leaf "A"]
    #[byteLayout, byteLayout] [leaf "A"] #[byteLayout] [1] .scalar := by decide +kernel
#print axioms distinctCase

/-- A public catalog cannot repeat an identity. -/
theorem duplicatePublic : ¬ LayoutProjectionValid [leaf "a"] #[byteLayout]
    [leaf "a", leaf "a"] #[byteLayout, byteLayout] [0, 0] .scalar := by decide +kernel
#print axioms duplicatePublic

/-- The ordered index uniqueness check rejects a distant duplicate. -/
theorem duplicateIndex : projectionDistinct [5, 2, 8, 1, 5] = false := by decide +kernel
#print axioms duplicateIndex

/-- Missing artifact entries retain option lookup failure. -/
theorem missingArtifact : ¬ projectionMetadataMatches [leaf "a"] [leaf "a"] [1] := by
  decide +kernel
#print axioms missingArtifact

/-- A missing nested public index cannot be silently retained. -/
theorem missingNested : ¬ projectionMetadataMatches [leaf "a"]
    [{ leaf "a" with fields := [⟨.aggregate 1, none⟩] }] [0] := by decide +kernel
#print axioms missingNested

/-- Nested public indices are expanded through the selected order. -/
theorem nestedExpansion : projectionMetadataMatches
    [leaf "private", leaf "a", { leaf "parent" with fields := [⟨.aggregate 1, none⟩] }]
    [leaf "a", { leaf "parent" with fields := [⟨.aggregate 0, none⟩] }] [1, 2] := by
  decide +kernel
#print axioms nestedExpansion
end Tests.LayoutProjectionIndexes
