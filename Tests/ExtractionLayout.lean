import CIL.Extraction.LayoutUses

open CIL CIL.Extraction

namespace Tests.ExtractionLayout

def raw : List RawLayout := [
  { explicit := false, packing := 0, declaredSize := -1, fields := [⟨.unsigned8, none⟩, ⟨.unsigned32, none⟩] },
  { explicit := false, packing := 1, declaredSize := -1, fields := [⟨.unsigned8, none⟩, ⟨.aggregate 0, none⟩] }]

def computed : Array ComputedLayout := #[
  ⟨⟨8, [⟨0, 1, false⟩, ⟨4, 4, false⟩]⟩, 4⟩,
  ⟨⟨9, [⟨0, 1, false⟩, ⟨1, 8, true⟩]⟩, 1⟩]

example : LayoutsValid raw computed := by decide

-- The wrong offset is still in bounds, so the older layout.Valid check accepts it.
def wrong : ComputedLayout := ⟨⟨8, [⟨0, 1, false⟩, ⟨3, 4, false⟩]⟩, 4⟩
example : wrong.layout.Valid := by decide
example : validateLayouts raw #[wrong, computed[1]'(by decide)] = false := by decide
example : computeLayouts [{ explicit := false, packing := 0, declaredSize := -1, fields := [⟨.aggregate 0, none⟩] }] = none := by decide
example : computeLayouts [{ explicit := false, packing := 3, declaredSize := -1, fields := [] }] = none := by decide
example : computeLayouts [{ explicit := true, packing := 0, declaredSize := 4, fields := [⟨.unsigned64, some 0⟩] }] = none := by decide
example : computeLayouts [{ explicit := false, packing := 0, declaredSize := -1, fields := [] }] = some #[⟨⟨1, []⟩, 1⟩] := by decide
-- Declared size is not rounded to alignment; nested alignment remains independent of size.
example : computeLayouts [{ explicit := false, packing := 0, declaredSize := 9, fields := [⟨.unsigned64, none⟩] }] = some #[⟨⟨9, [⟨0, 8, false⟩]⟩, 8⟩] := by decide
-- Auto layout is sequential only for equal-width primitive fields: CoreCLR reorders mixed widths.
example : computeLayouts [{ explicit := false, auto := true, packing := -1, declaredSize := -1, fields := [⟨.unsigned64, none⟩, ⟨.unsigned64, none⟩] }] = some #[⟨⟨16, [⟨0, 8, false⟩, ⟨8, 8, false⟩]⟩, 8⟩] := by decide
example : computeLayouts [{ explicit := false, auto := true, packing := -1, declaredSize := -1, fields := [⟨.unsigned32, none⟩, ⟨.unsigned64, none⟩] }] = none := by decide
example : computeLayouts [{ explicit := false, auto := true, packing := -1, declaredSize := -1, fields := [⟨.unsigned64, some 0⟩, ⟨.unsigned64, none⟩] }] = none := by decide
example : computeLayouts [{ explicit := false, auto := true, packing := 4, declaredSize := -1, fields := [⟨.unsigned64, none⟩, ⟨.unsigned64, none⟩] }] = none := by decide
example : computeLayouts [{ explicit := false, auto := true, packing := -1, declaredSize := 32, fields := [⟨.unsigned64, none⟩, ⟨.unsigned64, none⟩] }] = none := by decide
example : computeLayouts [{ explicit := true, auto := true, packing := -1, declaredSize := 16, fields := [⟨.unsigned64, some 0⟩, ⟨.unsigned64, some 8⟩] }] = none := by decide
example : computeLayouts [{ explicit := false, auto := true, packing := -1, declaredSize := -1, fields := [] }] = none := by decide
example : computeLayouts [{ explicit := false, packing := 0, declaredSize := -1, fields := [⟨.unsigned64, none⟩] },
  { explicit := false, auto := true, packing := -1, declaredSize := -1, fields := [⟨.aggregate 0, none⟩, ⟨.aggregate 0, none⟩] }] = none := by decide

def goodMethod : Method := { code := [.fieldAt 4 4], locals := [], returnsValue := true }
def wrongMethod : Method := { goodMethod with code := [.fieldAt 3 4] }
example : MethodLayoutsValid raw computed goodMethod [.field 0 0 1 .load] := by decide
example : validateLayoutUse raw computed wrongMethod (.field 0 0 1 .load) = false := by decide
example : validateLayoutUse raw computed goodMethod (.field 0 1 1 .load) = false := by decide

end Tests.ExtractionLayout
