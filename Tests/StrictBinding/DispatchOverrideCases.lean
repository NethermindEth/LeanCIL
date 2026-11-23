import Extracted
import DispatchImage
import NeighbourImage
import DerivedImage
import StrictBinding.DispatchCatalogs
import Tests.StrictBinding.Mutation

/-! Physical MethodImpl controls for two explicit implementations with identical signatures. -/

namespace DispatchOverrideCases
open StrictBinding CIL.Extraction

private def neighbour (bytes : ImageBytes) : PinnedImage := ⟨Extracted.assembly1.identity, bytes⟩

private def images (image : ImageBytes) : List PinnedImage :=
  [⟨Extracted.assembly0.identity, image⟩, neighbour NeighbourImage.image]

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

/-- Change only the major version of the AssemblyRef that supplies primitive signature types.
    The entry's bytes still bind, but the slot's physical Int32 result has a different scope. -/
private def changedPrimitiveScope : Option Bool := do
  let bytes := DispatchImage.image
  let pin : PinnedImage := ⟨Extracted.assembly0.identity, bytes⟩
  let image ← (prepareOne pin).toOption
  let row ← (List.range (image.layout.rowCount Table.assemblyRef)).find? fun index =>
    (referenceIdentity image (StrictBinding.tokenOf Table.assemblyRef (index + 1))).toOption ==
      some runtimeScope
  let token := StrictBinding.tokenOf Table.assemblyRef (row + 1)
  let (offset, width) ← (image.layout.cellAt token 0).toOption
  guard (width == 2)
  let changed := Tests.StrictBinding.flipByte bytes offset 1
  let altered ← (prepareOne { pin with image := changed }).toOption
  let _ ← (bodyBound altered Extracted.method0Original.token Extracted.method0Body.bytes).toOption
  let some call := Extracted.method0Original.code[1]? | none
  let .call site := call.operand | none
  let .managed slot := site.target | none
  return mismatch (audit changed) slot

theorem primitiveScopeMismatch : changedPrimitiveScope = some true := by decide +kernel
#print axioms primitiveScopeMismatch

/-- Omitting the explicit slots from the carried declarations changes the entry catalog. -/
theorem missingOverrides :
    mismatch (audit DispatchImage.image (Extracted.methodEvidence.map erase))
      Extracted.method0Original.token = true := by decide +kernel
#print axioms missingOverrides

/-- Erasing the managed reference from a carried parameter contradicts its physical signature. -/
private def eraseByref (item : MethodEvidence) : MethodEvidence := { item with
  dispatchTypes := item.dispatchTypes.map fun type => { type with
    methods := type.methods.map fun method => { method with
      parameters := method.parameters.map fun
        | .byref element => element
        | other => other } } }

/-- The same Int32 parameter passed by value does not match the byref declaration. -/
theorem byrefMismatch :
    mismatch (audit DispatchImage.image (Extracted.methodEvidence.map eraseByref))
      Extracted.method0Original.token = true := by decide +kernel
#print axioms byrefMismatch

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

/-- Reparenting the descendant changes its complete name while preserving its base and methods. -/
private def movedDescendant : Option Bool := do
  let bytes := DispatchImage.image
  let image ← (prepareOne ⟨Extracted.assembly0.identity, bytes⟩).toOption
  guard (nestedCount image == 1)
  let parent ← (enclosingOf image 1).toOption
  let some other ← (enumDefinition? image 0 [bytesOf "Geometry", bytesOf "Triangle"]).toOption
    | none
  guard (parent != other && parent < 256 && other < 256)
  let (offset, _) ← (image.layout.cellAt 0x29000001 enclosingTypeColumn).toOption
  let changed := Tests.StrictBinding.flipByte bytes offset (parent ^^^ other)
  let some call := Extracted.method0Original.code[1]? | none
  let .call site := call.operand | none
  let .managed slot := site.target | none
  return mismatch (audit changed) slot

/-- The dispatch certificate rejects a NestedClass row naming the wrong enclosing type. -/
theorem nestedOwnerMismatch : movedDescendant = some true := by decide +kernel
#print axioms nestedOwnerMismatch

/-- The physical pins may be supplied in either order. -/
theorem reversedPins : DispatchCatalogsChecked (images DispatchImage.image).reverse
    Extracted.assemblies Extracted.methodEvidence Extracted.imports true := by decide +kernel
#print axioms reversedPins

/-- An actual descendant in a second assembly or a missing pin leaves the catalog uncovered. -/
theorem incompleteHierarchy :
    let home : PinnedImage := ⟨Extracted.assembly0.identity, DispatchImage.image⟩
    DispatchCatalogsChecked [home, neighbour DerivedImage.image] Extracted.assemblies
        Extracted.methodEvidence Extracted.imports false ∧
      DispatchCatalogsChecked [home] Extracted.assemblies
        Extracted.methodEvidence Extracted.imports false := by decide +kernel
#print axioms incompleteHierarchy

end DispatchOverrideCases
