import Extracted
import RvaImage
import StrictBinding.StaticData

/-! Check changes to the static descriptor of the compiled table against its original image. -/
namespace StaticSiteCases
open CIL.Extraction StrictBinding

private def images : List PinnedImage := [⟨Extracted.assembly0Scope, RvaImage.image⟩]

private def change (f : StaticFieldSite → StaticFieldSite) : List MethodEvidence :=
  Extracted.methodEvidence.map fun item =>
    let sites := item.closed.staticFields.map fun (pc, site) =>
      (pc, if site.rvaSize.isSome then f site else site)
    { item with closed := { item.closed with staticFields := sites } }

theorem compiled_table_agrees : StaticDataBound images Extracted.methodEvidence := by decide +kernel
#print axioms compiled_table_agrees

/-- The first byte agrees with the physical storage. Its ClassLayout still requires 32 bytes. -/
theorem rejects_matching_prefix : (match checkStaticData images (change fun site =>
    { site with rvaSize := some 1, descriptor.bytes := site.descriptor.bytes.take 1 }) with
  | .error (.invalidFieldData _) => true | _ => false) = true := by decide +kernel
#print axioms rejects_matching_prefix

/-- Swapping the bytes keeps the recorded size, alignment, token and mapped address. -/
theorem rejects_wrong_bytes : (match checkStaticData images (change fun site =>
    { site with descriptor.bytes := site.descriptor.bytes.reverse }) with
  | .error (.fieldDataMismatch _ _ _) => true | _ => false) = true := by decide +kernel
#print axioms rejects_wrong_bytes

/-- Removing the RVA marker would classify the same physical field as constructor-initialized. -/
theorem rejects_ordinary_field_claim : (match checkStaticData images (change fun site =>
    { site with rvaSize := none }) with
  | .error (.invalidFieldData _) => true | _ => false) = true := by decide +kernel
#print axioms rejects_ordinary_field_claim

end StaticSiteCases
