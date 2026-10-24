import CIL.Imports

namespace CIL.Extraction

def ImportSlotLayoutsValid (slot : ImportSlot) (architecture : Architecture) : Prop :=
  slot.layouts.Valid architecture ∧
    match slot.signature with
    | none => slot.layouts = {}
    | some signature => signature.supported slot.layouts.actual = true ∧
      signature.parameters.length = slot.parameterCount ∧
      (signature.returnType != .void) = slot.returnsValue

instance (slot : ImportSlot) (architecture : Architecture) :
    Decidable (ImportSlotLayoutsValid slot architecture) := by
  unfold ImportSlotLayoutsValid
  cases slot.signature <;> dsimp <;> infer_instance

/-- Every typed slot carries the selected and published signature-scoped layout values. -/
def ImportedLayoutsValid (imports : List ImportSlot) (architecture : Architecture) : Prop :=
  ∀ slot ∈ imports, ImportSlotLayoutsValid slot architecture

instance (imports : List ImportSlot) (architecture : Architecture) :
    Decidable (ImportedLayoutsValid imports architecture) :=
  inferInstanceAs (Decidable (∀ slot ∈ imports, _))

theorem imported_layouts_checked {imports : List ImportSlot} {architecture : Architecture}
    (valid : ImportedLayoutsValid imports architecture) (slot : ImportSlot) (member : slot ∈ imports) :
    slot.layouts.published = slot.layouts.actual ∧
      LayoutsValid slot.layouts.actual slot.layouts.computed architecture :=
  ⟨(valid slot member).1.metadata, (valid slot member).1.layouts⟩

#print axioms imported_layouts_checked
end CIL.Extraction
