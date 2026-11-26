import Extracted
import TypeTestImage
import StrictBinding.DispatchCatalogs
import Tests.StrictBinding.Mutation

/-! Verify local class-test catalogs and reject altered bodies, declarations and image bytes. -/

namespace ClassTestCases
open CIL CIL.Extraction StrictBinding

/-- The SDK-built assembly containing the two type tests. -/
private def images : List PinnedImage := [⟨Extracted.assembly0Scope, TypeTestImage.image⟩]

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

/-- Change the method type parameter named by the physical return signature of Pick. -/
theorem wrongGenericReturn : rejected (Extracted.methodEvidence.map fun item =>
    { item with dispatchTypes := item.dispatchTypes.map fun type =>
      { type with methods := type.methods.map fun method =>
        if method.name == "Pick" then { method with returnType := .parameter 0 }
        else method } }) = true := by decide +kernel
#print axioms wrongGenericReturn

/-- Removing the managed reference from Load's parameter contradicts the signature blob. -/
theorem wrongGenericByref : rejected (Extracted.methodEvidence.map fun item =>
    { item with dispatchTypes := item.dispatchTypes.map fun type =>
      { type with methods := type.methods.map fun method =>
        if method.name == "Load" then { method with parameters := [.parameter 0] }
        else method } }) = true := by decide +kernel
#print axioms wrongGenericByref

/-- Alter only the constraints of Pick's first type parameter in the proposed catalog. -/
private def changeConstraint (change : GenericConstraint → GenericConstraint) :
    List MethodEvidence := Extracted.methodEvidence.map fun item =>
  { item with dispatchTypes := item.dispatchTypes.map fun type =>
    { type with methods := type.methods.map fun method =>
      if method.name == "Pick" then
        { method with genericParameters := method.genericParameters.modify 0 change }
      else method } }

/-- Dropping the reference-type and default-constructor flags contradicts the GenericParam row. -/
theorem wrongParameterFlags :
    rejected (changeConstraint fun claim => { claim with flags := 0 }) = true := by decide +kernel
#print axioms wrongParameterFlags

/-- Swapping the two arguments of IScale contradicts the TypeSpec of the constraint. -/
theorem wrongConstraintArguments : rejected (changeConstraint fun claim =>
    { claim with interfaces := claim.interfaces.map fun constraint =>
      match constraint with
      | .apply (.apply head first) second => .apply (.apply head second) first
      | other => other }) = true := by decide +kernel
#print axioms wrongConstraintArguments

/-- Changing either operand while retaining its original body contradicts the physical token. -/
private def crossed (opcode : Nat) (item : MethodEvidence) : MethodEvidence :=
  {item with original := {item.original with code := item.original.code.map fun instruction =>
    if instruction.opcode == opcode then
      {instruction with operand := .type (.object Extracted.assembly0Scope "Geometry.Shape")}
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

/-- Flip a flag in the first physical GenericParam of Pick and retain the selected method body. -/
private def changedFlags (mask : Nat) : Option (Except AuditError Bool) := do
  let pin ← images.head?
  let original ← (prepareOne pin).toOption
  let types := Extracted.methodEvidence.flatMap (·.dispatchTypes)
  let pick ← (types.flatMap (·.methods)).find? (·.name == "Pick")
  let cell := original.layout.cellOfRow original.view Table.genericParam
  let ownerKey := 2 * (pick.token % 2^24) + 1
  let index ← (List.range (original.layout.rowCount Table.genericParam)).find? fun i =>
    (cell (i+1) 2).toOption == some ownerKey && (cell (i+1) 0).toOption == some 0
  let parameter := StrictBinding.tokenOf Table.genericParam (index + 1)
  let (offset, _) ← (original.layout.cellAt parameter 1).toOption
  let altered := {pin with image := Tests.StrictBinding.flipByte pin.image offset mask}
  let prepared ← (prepareOne altered).toOption
  let _ ← (bodyBound prepared Extracted.method0Original.token Extracted.method0Body.bytes).toOption
  return ClassDispatch.check [altered] Extracted.assemblies
    Extracted.methodEvidence Extracted.imports

/-- Removing the default-constructor flag contradicts the catalog even though the IL still binds. -/
theorem changedPhysicalConstraint : (match changedFlags 0x10 with
    | some (.error (.dispatchMismatch token)) => token == Extracted.method0Original.token
    | _ => false) = true := by decide +kernel
#print axioms changedPhysicalConstraint

/-- An unsupported variance flag on a method type parameter leaves coverage incomplete. -/
theorem variantMethodParameter : (changedFlags 1).bind Except.toOption = some false := by
  decide +kernel
#print axioms variantMethodParameter

end ClassTestCases
