import Extracted
import DispatchImage
import StrictBinding.DispatchCatalogs
import Tests.StrictBinding.Mutation

/-! Physical MethodImpl controls for two explicit implementations with identical signatures. -/

namespace DispatchOverrideCases
open StrictBinding CIL.Extraction

private def images (image : ImageBytes) : List PinnedImage := [⟨Extracted.assembly0.identity, image⟩]

private def audit (image : ImageBytes) (items := Extracted.methodEvidence) :=
  ClassDispatch.check (images image) Extracted.assemblies items Extracted.imports

/-- Both explicit slots match the implementation catalog read from the assembly. -/
theorem original : DispatchCatalogsChecked (images DispatchImage.image) Extracted.assemblies
    Extracted.methodEvidence Extracted.imports true := by decide +kernel
#print axioms original

/-- The unrelated IDisposable implementation names an external declaration by MemberRef. -/
theorem unrelatedMemberRef :
    (do
      let image ← (prepareOne ⟨Extracted.assembly0.identity, DispatchImage.image⟩).toOption
      let declaration ← (image.layout.cellOfRow image.view 0x19 3 2).toOption
      return (image.layout.rowCount 0x19, declaration % 2)) = some (3, 1) := by decide +kernel
#print axioms unrelatedMemberRef

private def erase (item : MethodEvidence) : MethodEvidence := { item with
  dispatchTypes := item.dispatchTypes.map fun type => { type with
    methods := type.methods.map fun method => { method with overrides := [] } } }

private def mismatch (result : Except AuditError Bool) (expected : Nat) : Bool :=
  match result with
  | .error (.dispatchMismatch token) => token == expected
  | _ => false

/-- Omitting the explicit slots from the carried declarations changes the entry catalog. -/
theorem missingOverrides :
    mismatch (audit DispatchImage.image (Extracted.methodEvidence.map erase))
      Extracted.method0Original.token = true := by decide +kernel
#print axioms missingOverrides

private def crossed (owner : Bool) : Option Bool := do
  let image := DispatchImage.image
  let prepared ← (prepareOne ⟨Extracted.assembly0.identity, image⟩).toOption
  let cell := prepared.layout.cellOfRow prepared.view 0x19
  let body ← (cell 1 1).toOption
  let first ← (cell 1 2).toOption
  let second ← (cell 2 2).toOption
  guard (first != second && first < 256 && second < 256)
  let column := if owner then 0 else 2
  let (offset, _) ← (prepared.layout.cellAt 0x19000001 column).toOption
  let altered := Tests.StrictBinding.flipByte image offset (if owner then 1 else first ^^^ second)
  let expected := if owner then StrictBinding.tokenOf Table.methodDef (body / 2)
    else Extracted.method0Original.token
  return mismatch (audit altered) expected

/-- Moving the row to another class contradicts the body MethodDef's physical owner. -/
theorem crossedOwner : crossed true = some true := by decide +kernel
#print axioms crossedOwner

/-- Selecting the other declaration changes the catalog even though its signature agrees. -/
theorem crossedDeclaration : crossed false = some true := by decide +kernel
#print axioms crossedDeclaration

end DispatchOverrideCases
