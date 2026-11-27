import Extracted
import AppImage
import LibImage
import StrictBinding.DispatchCatalogs
import Tests.StrictBinding.Mutation

/-! Bind each class catalog in a two-assembly extraction to its physical method and image. -/
namespace TwoCatalogCases

open CIL.Extraction StrictBinding

/-- The entry method's physical assembly. -/
private def app : PinnedImage := ⟨Extracted.assembly0Scope, AppImage.image⟩

/-- The called method's physical assembly. -/
private def library : PinnedImage := ⟨Extracted.assembly1Scope, LibImage.image⟩

/-- Audit the method catalogs with the certified program's original pins and imports. -/
private def checked (images : List PinnedImage) (items : List MethodEvidence) :=
  ClassDispatch.check images Extracted.assemblies items Extracted.imports

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- The reference to Far.IScale on Near.First.Pick needs its defining image. -/
private def missingInterface : Except AuditError Bool := do
  let home ← prepareOne app
  let some owner ← enumDefinition? home 0 [bytesOf "Near", bytesOf "First"]
    | throw .uncoveredConstraint
  return (← (ClassDispatch.physicalHierarchy home owner false [home]).run).isNone

theorem missingConstraintImage : missingInterface.toOption = some true := by decide +kernel
#print axioms missingConstraintImage

/-- Change one open constraint on Pick while retaining every other catalog entry. -/
private def changePick (change : TypeExpr → TypeExpr) : List MethodEvidence :=
  Extracted.methodEvidence.map fun item =>
    { item with dispatchTypes := item.dispatchTypes.map fun entry =>
      { entry with methods := entry.methods.map fun method =>
        if method.name == "Pick" then
          { method with genericParameters := method.genericParameters.modify 0 fun constraint =>
            { constraint with interfaces := constraint.interfaces.map change } }
        else method } }

/-- Moving only the outer interface to the caller contradicts Pick's TypeRef. -/
private def wrongScope := changePick fun
  | .apply (.apply (.objectConstructor _ name) left) right =>
    .apply (.apply (.objectConstructor app.identity name) left) right
  | type => type

/-- Swapping the arguments of the interface inside Box preserves both outer applications. -/
private def crossedArguments := changePick fun
  | .apply (.apply outer (.apply box (.apply (.apply inner first) second))) right =>
    .apply (.apply outer (.apply box (.apply (.apply inner second) first))) right
  | type => type

/-- Change only the result of the library's Label method from a string reference to an atom. -/
private def wrongStringResult := Extracted.methodEvidence.modify 1 fun item =>
  { item with dispatchTypes := item.dispatchTypes.map fun entry =>
    { entry with methods := entry.methods.map fun method =>
      if method.name == "Label" then
        { method with returnType := .atom runtimeScope "System.String" .classType }
      else method } }

/-- Replace the final OBJECT parameter of Label with VOID in its physical signature blob. -/
private def voidParameter : Option Bool := do
  let methods := Extracted.method1DispatchTypes.flatMap (·.methods)
  let method ← methods.find? (·.name == "Label")
  let image ← (prepareOne library).toOption
  let key ← (image.layout.cell image.view method.token 4).toOption
  let blob ← (image.layout.blobAt image.view key).toOption
  guard (blob == [0, 2, 0x0E, 0x10, 0x0E, 0x1C])
  let start := image.layout.pe.blobs.start + key
  let (prefixSize, length) ← (blobPrefix image.view start).toOption
  let bytes := Tests.StrictBinding.flipByte library.image (start + prefixSize + length - 1) (0x1C ^^^ 1)
  let altered := { library with image := bytes }
  let prepared ← (prepareOne altered).toOption
  let _ ← (bodyBound prepared Extracted.method1Original.token Extracted.method1Body.bytes).toOption
  return match checked [app, altered] Extracted.methodEvidence with
    | .error (.dispatchMismatch token) => token == method.token
    | _ => false

theorem voidParameterMismatch : voidParameter = some true := by decide +kernel
#print axioms voidParameterMismatch

/-- Both pin orders locate the same declaring images. -/
theorem reversed : (checked [library, app] Extracted.methodEvidence).toOption = some true :=
  by decide +kernel
#print axioms reversed

/-- Omitting either pin leaves the two-assembly extraction uncovered. -/
theorem missing : (checked [app] Extracted.methodEvidence).toOption = some false ∧
    (checked [library] Extracted.methodEvidence).toOption = some false := by decide +kernel
#print axioms missing

/-- Replace the catalog while retaining the selected method's physical body and token. -/
private def withCatalog (index : Nat) (catalog : List DispatchType) :=
  Extracted.methodEvidence.modify index (fun item => { item with dispatchTypes := catalog })

/-- Outcomes for catalog changes checked against the same two physical images. -/
private structure CatalogResults where
  original : Except AuditError Bool
  constraintScope : Except AuditError Bool
  constraintArguments : Except AuditError Bool
  stringResult : Except AuditError Bool
  emptyCaller : Except AuditError Bool
  emptyCallee : Except AuditError Bool
  foreignCatalog : Except AuditError Bool

/-- Checking these outcomes together lets the kernel share reductions of the original images. -/
theorem catalogResults :
    let check := checked [app, library]
    let caller := Except.error (AuditError.dispatchMismatch Extracted.method0Original.token)
    let callee := Except.error (AuditError.dispatchMismatch Extracted.method1Original.token)
    CatalogResults.mk (check Extracted.methodEvidence) (check wrongScope) (check crossedArguments)
      (check wrongStringResult) (check (withCatalog 0 [])) (check (withCatalog 1 []))
      (check (withCatalog 0 Extracted.method1DispatchTypes)) =
      ⟨.ok true, caller, caller, callee, caller, callee, caller⟩ := by
  cil_kernel_rfl
#print axioms catalogResults

/-- The caller tests local, foreign and nested classes. Its callee tests its own class. -/
theorem covered : (checked [app, library] Extracted.methodEvidence).toOption = some true :=
  congrArg (fun cases => cases.original.toOption) catalogResults
#print axioms covered

/-- A constraint scoped to the caller contradicts the library's physical TypeRef. -/
theorem wrongConstraintScope : checked [app, library] wrongScope =
    .error (.dispatchMismatch Extracted.method0Original.token) :=
  congrArg CatalogResults.constraintScope catalogResults
#print axioms wrongConstraintScope

/-- The library's nested interface arguments bind in their declared order. -/
theorem wrongNestedArguments : checked [app, library] crossedArguments =
    .error (.dispatchMismatch Extracted.method0Original.token) :=
  congrArg CatalogResults.constraintArguments catalogResults
#print axioms wrongNestedArguments

/-- The physical string signature disagrees with a carried class atom. -/
theorem stringResultMismatch : checked [app, library] wrongStringResult =
    .error (.dispatchMismatch Extracted.method1Original.token) :=
  congrArg CatalogResults.stringResult catalogResults
#print axioms stringResultMismatch

/-- Both declarations are required at their physical method tokens. -/
theorem erased : checked [app, library] (withCatalog 0 []) =
      .error (.dispatchMismatch Extracted.method0Original.token) ∧
    checked [app, library] (withCatalog 1 []) =
      .error (.dispatchMismatch Extracted.method1Original.token) :=
  ⟨congrArg CatalogResults.emptyCaller catalogResults,
   congrArg CatalogResults.emptyCallee catalogResults⟩
#print axioms erased

/-- The other selected assembly's catalog cannot substitute for this class token. -/
theorem wrongImageCatalog : checked [app, library] (withCatalog 0 Extracted.method1DispatchTypes) =
    .error (.dispatchMismatch Extracted.method0Original.token) :=
  congrArg CatalogResults.foreignCatalog catalogResults
#print axioms wrongImageCatalog

/-- Move the declaring pin without changing this method's own body or MethodDef token. -/
private def wrongBody (index : Nat) (assembly : AssemblyPin) : Option Nat :=
  let moved := Extracted.methodEvidence.modify index fun item => { item with assembly }
  match checked [app, library] moved with
  | .error (.bodyMismatch token _ _) => some token
  | _ => none

/-- Both images have the same MethodDef token at the tested site. Moving either method to
    the other image fails the physical body check at that token. -/
theorem movedMethod :
    Extracted.method0Original.token = Extracted.method1Original.token ∧
    wrongBody 0 Extracted.assembly1 = some Extracted.method0Original.token ∧
    wrongBody 1 Extracted.assembly0 = some Extracted.method1Original.token := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms movedMethod

/-- The physical TypeRef used at a particular foreign class test in the caller. -/
private def testedReference (name : String) : Option Nat := do
  let instruction ← Extracted.method0Original.code.find? fun raw =>
    raw.opcode == 0x75 && raw.operand == .type (.object Extracted.assembly1Scope name)
  let bytes := Extracted.method0Body.bytes
  let first ← bytes.head?
  let start := (if first % 4 == 2 then 1 else 12) + instruction.offset + 1
  let token := Tests.StrictBinding.readLittle bytes start 4
  guard (tableOf token == Table.typeRef)
  return token

/-- Change a physical metadata cell while preserving the caller's exact method-body bytes. -/
private def replaceCell (pin : PinnedImage) (image : PreparedImage) (token column value : Nat) :
    Option PinnedImage := do
  let old ← (image.layout.cell image.view token column).toOption
  let (offset, width) ← (image.layout.cellAt token column).toOption
  guard (value < 256 ^ width)
  let changes := (List.range width).map fun i => (offset + i, ((old ^^^ value) / 256 ^ i) % 256)
  return {pin with image := Tests.StrictBinding.flipBytes pin.image changes}

/-- Change only the ordinal of Box's parameter in the library. The caller's nested constraint
    must read that TypeDef even though its own outer interface and IL are unchanged. -/
private def alteredNestedParameter : Option Bool := do
  let source ← (prepareOne library).toOption
  let some box ← (enumDefinition? source 0 [bytesOf "Far", bytesOf "Box`1"]).toOption | none
  let index ← (List.range (source.layout.rowCount Table.genericParam)).find? fun index =>
    (source.layout.cellOfRow source.view Table.genericParam (index + 1) 2).toOption ==
      some (2 * box)
  let parameter := StrictBinding.tokenOf Table.genericParam (index + 1)
  let altered ← replaceCell library source parameter 0 1
  let changed ← (prepareOne altered).toOption
  let _ ← (bodyBound changed Extracted.method1Original.token Extracted.method1Body.bytes).toOption
  match checked [app, altered] Extracted.methodEvidence with
  | .error (.typeDefMismatch row .kind) => return row == box
  | _ => return false

theorem nestedParameterOrdinal : alteredNestedParameter = some true := by decide +kernel
#print axioms nestedParameterOrdinal

/-- Changing the caller's TypeRef to the physically present outer class contradicts the
    bound operand at its own TypeRef token. Cycling a nested scope leaves coverage partial. -/
private def changedReference (cycle : Bool) : Option Bool := do
  let original ← (prepareOne app).toOption
  let nested ← testedReference "Far.Family/Child"
  let outerScope ← (original.layout.cell original.view nested 0).toOption
  guard (outerScope % 4 == 3)
  let second ← testedReference "Far.Second"
  let outer := StrictBinding.tokenOf Table.typeRef (outerScope / 4)
  let outerName ← (original.layout.cell original.view outer typeNameColumn).toOption
  let altered ← if cycle then replaceCell app original nested 0 ((nested % 2^24) * 4 + 3)
    else replaceCell app original second typeNameColumn outerName
  let prepared ← (prepareOne altered).toOption
  let _ ← (bodyBound prepared Extracted.method0Original.token Extracted.method0Body.bytes).toOption
  match checked [altered, library] Extracted.methodEvidence with
  | .error (.dispatchMismatch token) => return !cycle && token == second
  | .ok false => return cycle
  | _ => return false

/-- The audit checks the caller's referencing row and terminates on a cyclic enclosing scope. -/
theorem physicalReferences :
    changedReference false = some true ∧ changedReference true = some true := by
  exact ⟨by decide +kernel, by decide +kernel⟩
#print axioms physicalReferences

/-- The outer class exists, but has no nested class named Second. -/
private def missingChild : Option Bool := do
  let caller ← (prepareOne app).toOption
  let target ← (prepareOne library).toOption
  let nested ← testedReference "Far.Family/Child"
  let second ← testedReference "Far.Second"
  let name ← (caller.layout.cell caller.view second typeNameColumn).toOption
  let altered ← replaceCell app caller nested typeNameColumn name
  let some family ← (enumDefinition? target 0 [CIL.Extraction.bytesOf "Far",
    CIL.Extraction.bytesOf "Family"]).toOption | none
  match checked [altered, library] Extracted.methodEvidence with
  | .error (.typeDefMismatch row .typeName) => return row == family
  | _ => return false

/-- A conflicting nested name fails at the enclosing TypeDef in the supplied destination. -/
theorem missingChildRejected : missingChild = some true := by decide +kernel
#print axioms missingChildRejected

end TwoCatalogCases
