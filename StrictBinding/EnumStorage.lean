import StrictBinding.CarriedEnums
import CIL.Extraction.Translation

/-! Check every enum definition selected by the certified extraction against the supplied images. -/

namespace StrictBinding

open CIL CIL.Extraction

/-- Collect the declarations from the actual body metadata environments of the proof. -/
def methodEnumClaims (platform : PlatformTable) (methods : List MethodEvidence) :
    Except AuditError (List CarriedEnum) := do
  let groups ← methods.mapM fun item => do
    let .ok env := item.body.environment | throw (.rowMismatch item.original.token)
    unless env.platform == platform do throw (.rowMismatch item.original.token)
    return carriedEnums env
  return groups.flatten.eraseDups

/-- Read the backing field for every selected local or platform declaration. With no enum
    declaration, or a missing scope image, there is no complete enum receipt. -/
def checkEnumStorage (images : List PinnedImage) (platform : PlatformTable)
    (methods : List MethodEvidence) : Except AuditError Bool := do
  let prepared ← prepare images
  let localClaims ← methodEnumClaims platform methods
  let localCoverage ← localClaims.mapM (carriedEnumBound prepared)
  let externalClaims := platform.definitions
  let externalCoverage ← coveredEnumEntries prepared externalClaims
  let selected := !localClaims.isEmpty || externalClaims.any fun entry =>
    match entry.kind with | .enumType .. => true | _ => false
  return selected && localCoverage.all id && externalCoverage

/-- An explicit coverage bit distinguishes a complete audit from an incomplete selection.
    Both outcomes require every supplied definition to pass the physical checks. -/
def EnumStorageChecked (images : List PinnedImage) (platform : PlatformTable)
    (methods : List MethodEvidence) (complete : Bool) : Prop :=
  (checkEnumStorage images platform methods).toOption = some complete

instance (images : List PinnedImage) (platform : PlatformTable) (methods : List MethodEvidence)
    (complete : Bool) : Decidable (EnumStorageChecked images platform methods complete) :=
  inferInstanceAs (Decidable (_ = _))

end StrictBinding
