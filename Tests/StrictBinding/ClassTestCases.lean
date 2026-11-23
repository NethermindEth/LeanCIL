import Extracted
import TypeTestImage
import StrictBinding.DispatchCatalogs
import Tests.StrictBinding.Mutation

/-! Verify local class-test catalogs and reject altered bodies, declarations and image bytes. -/

namespace ClassTestCases
open CIL CIL.Extraction StrictBinding

/-- The SDK-built assembly containing the two type tests. -/
private def images : List PinnedImage := [⟨Extracted.assembly0.identity, TypeTestImage.image⟩]

/-- Both original opcodes select one physical class declaration. -/
theorem covered : DispatchCatalogsChecked images Extracted.assemblies
    Extracted.methodEvidence Extracted.imports true := by decide +kernel
#print axioms covered

/-- A contradiction in this method's class catalog must identify the original method. -/
private def rejected (items : List MethodEvidence) : Bool :=
  match ClassDispatch.check images Extracted.assemblies items Extracted.imports with
  | .error (.dispatchMismatch token) => token == Extracted.method0Original.token
  | _ => false

/-- Dropping the class declaration leaves both tests without their catalog. -/
theorem missingCatalog : rejected (Extracted.methodEvidence.map fun item =>
    {item with dispatchTypes := []}) = true := by decide +kernel
#print axioms missingCatalog

/-- Changing either operand while retaining its original body contradicts the physical token. -/
private def crossed (opcode : Nat) (item : MethodEvidence) : MethodEvidence :=
  {item with original := {item.original with code := item.original.code.map fun instruction =>
    if instruction.opcode == opcode then
      {instruction with operand := .type (.object Extracted.assembly0.identity "Geometry.Shape")}
    else instruction}}

/-- A different type in the nonthrowing test contradicts the original bytes. -/
theorem crossedIsinst : rejected (Extracted.methodEvidence.map (crossed 0x75)) = true := by
  decide +kernel
#print axioms crossedIsinst

/-- A different type in the throwing cast contradicts the original bytes. -/
theorem crossedCastclass : rejected (Extracted.methodEvidence.map (crossed 0x74)) = true := by
  decide +kernel
#print axioms crossedCastclass

/-- Change the target's physical name or abstract flag. The original body must still bind. -/
private def changedClassRejected (rename : Bool) : Option Bool := do
  let pin ← images.head?
  let original ← (prepareOne pin).toOption
  let instruction ← Extracted.method0Original.code.find? (·.opcode == 0x75)
  let bytes := Extracted.method0Body.bytes
  let first ← bytes.head?
  let operand := (if first % 4 == 2 then 1 else 12) + instruction.offset + 1
  let token := Tests.StrictBinding.readLittle bytes operand 4
  guard (tableOf token == Table.typeDef)
  let (offset, mask, expected) ← if rename then do
    let name ← (original.layout.cell original.view token typeNameColumn).toOption
    pure (original.layout.pe.strings.start + name, 1, token)
  else do
    let (flags, _) ← (original.layout.cellAt token typeDefFlagsColumn).toOption
    pure (flags, 0x80, Extracted.method0Original.token)
  let altered := {pin with image := Tests.StrictBinding.flipByte pin.image offset mask}
  let prepared ← (prepareOne altered).toOption
  let _ ← (bodyBound prepared Extracted.method0Original.token bytes).toOption
  let result := ClassDispatch.check [altered] Extracted.assemblies
    Extracted.methodEvidence Extracted.imports
  match result with
  | .error (.dispatchMismatch found) => return found == expected
  | _ => return false

/-- The original CIL body still matches the altered image, but its class declaration differs. -/
theorem changedPhysicalClass : changedClassRejected false = some true := by decide +kernel
#print axioms changedPhysicalClass

/-- A different name in the string heap identifies the contradicting TypeDef token. -/
theorem changedPhysicalName : changedClassRejected true = some true := by decide +kernel
#print axioms changedPhysicalName

end ClassTestCases
