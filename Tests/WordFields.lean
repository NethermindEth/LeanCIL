import CIL.Safety.ResolutionFacts
import CIL.Extraction.LayoutUses

namespace Tests.WordFields

/-- `T::Words`, four `UInt64` fields. -/
def wordsLayouts : List CIL.Extraction.RawLayout := [
  { identity := "T::Words", explicit := false, packing := 0, declaredSize := 0,
    fields := List.replicate 4 { type := .unsigned64 } }]

/-- The layout CoreCLR computes for `T::Words`: the fields at offsets 0, 8, 16 and 24. -/
def wordsComputed : Array CIL.Extraction.ComputedLayout := #[
  ⟨{ size := 32, fields := [{ offset := 0, width := 8 }, { offset := 8, width := 8 },
    { offset := 16, width := 8 }, { offset := 24, width := 8 }] }, 8⟩]

theorem words_valid : CIL.Extraction.LayoutsValid wordsLayouts wordsComputed .x64 := by
  decide +kernel
#print axioms words_valid

/-- The layout environment both methods use to resolve the four words. -/
@[cil_code] def wordsEnvironment : CIL.LayoutEnvironment :=
  { rawLayouts := wordsLayouts, layouts := wordsComputed }

/-- The field of `T::Words` at `index`. -/
def wordField (index : Nat) : CIL.Extraction.FieldRef :=
  { owner := .aggregate "T::Words" 0, index, name := name!"word",
    type := .primitive .uint64 }
/-- The first, second, third and fourth words. -/
def word0 : CIL.Extraction.FieldRef := wordField 0
/-- The output word at byte offset 8. -/
def word1 : CIL.Extraction.FieldRef := wordField 1
/-- The output word at byte offset 16. -/
def word2 : CIL.Extraction.FieldRef := wordField 2
/-- The output word at byte offset 24. -/
def word3 : CIL.Extraction.FieldRef := wordField 3

cil_field_shape wordsEnvironment word0
cil_field_shape wordsEnvironment word1
cil_field_shape wordsEnvironment word2
cil_field_shape wordsEnvironment word3

/-- Two-word arguments have 16 bytes of storage. -/
@[cil_code] def pairEnvironment : CIL.LayoutEnvironment :=
  { rawLayouts := [
      { identity := "T::Pair", explicit := false, packing := 0, declaredSize := 0,
        fields := [{ type := .unsigned64 }, { type := .unsigned64 }] }]
    layouts := #[⟨⟨16, [⟨0, 8, false⟩, ⟨8, 8, false⟩]⟩, 8⟩] }

theorem pair_valid : CIL.Extraction.LayoutsValid pairEnvironment.rawLayouts
    pairEnvironment.layouts .x64 := by decide +kernel
#print axioms pair_valid

def low : CIL.Extraction.FieldRef :=
  { owner := .aggregate "T::Pair" 0, index := 0, name := name!"Low",
    type := .primitive .uint64 }

def high : CIL.Extraction.FieldRef :=
  { low with index := 1, name := name!"High" }

cil_field_shape pairEnvironment low
cil_field_shape pairEnvironment high

end Tests.WordFields
