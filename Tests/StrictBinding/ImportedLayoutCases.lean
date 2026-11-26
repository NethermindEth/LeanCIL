import Extracted
import LayoutImage
import StrictBinding.ImportedLayouts

/-! Imported layout checks of the compiled DeepCli.Layouts Overlay rows, as extracted and forged. -/

namespace ImportedLayoutCases
open StrictBinding CIL.Extraction

/-- The compiled assembly under the identity the extraction records for it. -/
private def images : List PinnedImage := [⟨Extracted.assembly0Scope, LayoutImage.image⟩]

/-- The import identity that names the slot in a refusal. -/
private def slotIdentity := "Gates.Reader::Read(Gates.Overlay&)"

/-- A slot that selected `layouts` from the compiled implementation. -/
private def slot (layouts : List RawLayout) : CIL.ImportSlot :=
  { identity := slotIdentity, closureDigest := "", parameterCount := 1, hasThis := false,
    returnsValue := true, layouts := { published := layouts, actual := layouts } }

/-- Check one slot whose every selected row is the extracted row after `forge`. -/
private def check (forge : RawLayout → RawLayout) :=
  checkImportedLayouts images [slot (Extracted.rawLayouts.map forge)]

/-- Whether the check refused a selected row of the slot as different from the image. -/
private def refused (result : Except AuditError Bool) : Bool :=
  match result with
  | .error (.importedLayoutMismatch slot _) => slot == slotIdentity
  | _ => false

/-- The rows the extractor read from the image are the image's. -/
theorem extracted : ImportedLayoutsChecked images [slot Extracted.rawLayouts] true := by
  decide +kernel
#print axioms extracted

/-- A forged offset, size, packing or layout kind is refused for its slot; a row of an unpinned
    scope or a slot without rows leaves coverage partial. -/
theorem forged :
    refused (check fun layout => { layout with
      fields := layout.fields.map fun field => { field with offset := field.offset.map (· + 4) } }) ∧
    refused (check fun layout => { layout with declaredSize := layout.declaredSize + 8 }) ∧
    refused (check fun layout => { layout with packing := 8 }) ∧
    refused (check fun layout => { layout with explicit := !layout.explicit }) ∧
    (check fun layout => { layout with identity := "Other, Version=1.0.0.0::Missing" }).toOption =
      some false ∧
    (checkImportedLayouts images [slot []]).toOption = some false := by decide +kernel
#print axioms forged

end ImportedLayoutCases
