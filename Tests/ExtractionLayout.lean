import CIL.Extraction.ValueDecoding
import CIL.Resolution

/-! Raw and computed struct layouts and their field uses. -/

open CIL CIL.Extraction

namespace Tests.ExtractionLayout

/-- The sequential leaf and its packed parent whose second field embeds the leaf. -/
def raw : List RawLayout := [
  { identity := "Leaf", explicit := false, packing := 0, declaredSize := -1,
    fields := [⟨.unsigned8, none⟩, ⟨.unsigned32, none⟩] },
  { identity := "Parent", explicit := false, packing := 1, declaredSize := -1,
    fields := [⟨.unsigned8, none⟩, ⟨.aggregate 0, none⟩] }]

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

/-- The second field of Leaf holds an unsigned word at byte four. -/
private def leafWord : FieldRef :=
  { owner := .aggregate "Leaf" 0, index := 1, name := name!"word",
    type := .atom runtimeScope "System.UInt32" }

/-- The decoded load and its execution environment share the typed field operand. -/
theorem leaf_word_shape :
    let site : RawInstruction := ⟨0, 0x7b,
      .field leafWord.owner leafWord.index leafWord.type leafWord.name false⟩
    let environment : LayoutEnvironment := { rawLayouts := raw, layouts := computed }
    Instruction.ofRaw? none site = some (.ldfld leafWord) ∧
      environment.fieldShape leafWord = .value 4 4 false := ⟨rfl, by decide +kernel⟩
#print axioms leaf_word_shape

/-- Layout validation rejects the in-bounds offset three. A correct layout also refuses a
    field operand that names the parent with the leaf's row or holds the parent's nested field. -/
theorem leaf_word_forgeries :
    let environment : LayoutEnvironment := { rawLayouts := raw, layouts := computed }
    ¬ LayoutsValid raw (computed.set! 0 wrong) .x64 ∧
      environment.fieldShape { leafWord with owner := .aggregate "Parent" 0 } =
        .unsupported "Field owner is not a value type" ∧
      environment.fieldShape { leafWord with owner := .aggregate "Parent" 1 } =
        .unsupported "Field outside the checked layouts" := by decide +kernel
#print axioms leaf_word_forgeries

end Tests.ExtractionLayout
