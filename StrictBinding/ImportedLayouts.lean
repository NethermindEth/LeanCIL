import StrictBinding.LayoutContent

/-!
# Imported layouts

An import slot carries the layouts its typed signature mentions, read from the selected
implementation assembly. This check reconstructs each of those layouts from the pinned image of
the implementation, so the layout facts an import relies on are the bytes of that image.
-/

namespace StrictBinding

open CIL.Extraction

/-- Every selected layout of every slot, paired with the slot that carries it. -/
def importedLayoutRows (imports : List CIL.ImportSlot) : List (CIL.ImportSlot × RawLayout) :=
  imports.flatMap fun slot => slot.layouts.actual.map (slot, ·)

/-- A selected layout agrees with its image in every field; a form the image reader does not
    reconstruct, such as a nested struct, leaves coverage partial. -/
private def checkImportedLayout (images : List PreparedImage)
    (row : CIL.ImportSlot × RawLayout) : Except AuditError Bool := do
  let some actual ← physicalLayout images row.2.identity row.2.declaration | return false
  if actual = row.2 then return true
  throw (.importedLayoutMismatch row.1.identity row.2.identity)

/-- Check every selected layout of every slot, even after one leaves coverage partial; with no
    selected layout there is nothing to reconfirm and coverage is partial. -/
def checkImportedLayouts (images : List PinnedImage) (imports : List CIL.ImportSlot) :
    Except AuditError Bool := do
  if (importedLayoutRows imports).isEmpty then return false
  let prepared ← prepare images
  let coverage ← (importedLayoutRows imports).mapM (checkImportedLayout prepared)
  return coverage.all id

/-- The consumer's coverage bit is the result of checking every slot's selected layouts. -/
def ImportedLayoutsChecked (images : List PinnedImage) (imports : List CIL.ImportSlot)
    (complete : Bool) : Prop :=
  (checkImportedLayouts images imports).toOption = some complete

instance (images : List PinnedImage) (imports : List CIL.ImportSlot) (complete : Bool) :
    Decidable (ImportedLayoutsChecked images imports complete) :=
  inferInstanceAs (Decidable (_ = _))

/-- Each selected layout of each slot, which the slot's published layouts equal, is the layout
    its pinned image defines. -/
theorem ImportedLayoutsChecked.physical {images : List PinnedImage}
    {imports : List CIL.ImportSlot} (checked : ImportedLayoutsChecked images imports true) :
    ∃ prepared, prepare images = .ok prepared ∧
      ∀ slot ∈ imports, ∀ layout ∈ slot.layouts.actual,
        physicalLayout prepared layout.identity layout.declaration = .ok (some layout) := by
  have done : checkImportedLayouts images imports = .ok true := by
    cases result : checkImportedLayouts images imports with
    | error err => simp [ImportedLayoutsChecked, result, Except.toOption] at checked
    | ok value => simpa [ImportedLayoutsChecked, result, Except.toOption] using checked
  unfold checkImportedLayouts at done
  split at done
  · cases done
  · obtain ⟨prepared, built, done⟩ := CIL.Safety.except_bind_ok done
    obtain ⟨coverage, read, done⟩ := CIL.Safety.except_bind_ok done
    refine ⟨prepared, built, ?_⟩
    intro slot slotMember layout member
    have row : (slot, layout) ∈ importedLayoutRows imports :=
      List.mem_flatMap.mpr ⟨slot, slotMember, List.mem_map.mpr ⟨layout, member, rfl⟩⟩
    obtain ⟨value, found, result⟩ := read_member row read
    have yes : value = true := List.all_eq_true.mp (Except.ok.inj done) value found
    subst value
    unfold checkImportedLayout at result
    obtain ⟨actual, physical, compared⟩ := CIL.Safety.except_bind_ok result
    cases actual with
    | none => cases compared
    | some actual =>
      by_cases same : actual = layout
      · exact same ▸ physical
      · simp [same, throw] at compared
#print axioms ImportedLayoutsChecked.physical

end StrictBinding
