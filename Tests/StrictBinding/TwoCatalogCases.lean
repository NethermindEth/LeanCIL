import Extracted
import AppImage
import LibImage
import StrictBinding.DispatchCatalogs
import Tests.StrictBinding.Mutation

/-! Bind each class catalog in a two-assembly extraction to its physical method and image. -/
namespace TwoCatalogCases

open CIL.Extraction StrictBinding

/-- The entry method's physical assembly. -/
private def app : PinnedImage := ⟨Extracted.assembly0.identity, AppImage.image⟩

/-- The called method's physical assembly. -/
private def library : PinnedImage := ⟨Extracted.assembly1.identity, LibImage.image⟩

/-- Audit the method catalogs with the certified program's original pins and imports. -/
private def checked (images : List PinnedImage) (items : List MethodEvidence) :=
  ClassDispatch.check images Extracted.assemblies items Extracted.imports

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- The caller tests local, foreign and nested classes. Its callee tests its own class. -/
theorem covered : (checked [app, library] Extracted.methodEvidence).toOption = some true :=
  by decide +kernel
#print axioms covered

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

/-- Both declarations are required at their physical method tokens. -/
theorem erased : checked [app, library] (withCatalog 0 []) =
      .error (.dispatchMismatch Extracted.method0Original.token) ∧
    checked [app, library] (withCatalog 1 []) =
      .error (.dispatchMismatch Extracted.method1Original.token) := by
  exact ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms erased

/-- The other selected assembly's catalog cannot substitute for this class token. -/
theorem wrongImageCatalog : checked [app, library] (withCatalog 0 Extracted.method1DispatchTypes) =
    .error (.dispatchMismatch Extracted.method0Original.token) := by cil_kernel_rfl
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
    raw.opcode == 0x75 && raw.operand == .type (.object Extracted.assembly1.identity name)
  let bytes := Extracted.method0Body.bytes
  let first ← bytes.head?
  let start := (if first % 4 == 2 then 1 else 12) + instruction.offset + 1
  let token := Tests.StrictBinding.readLittle bytes start 4
  guard (tableOf token == Table.typeRef)
  return token

/-- Change a physical metadata cell while preserving the caller's exact method-body bytes. -/
private def replaceCell (image : PreparedImage) (token column value : Nat) :
    Option PinnedImage := do
  let old ← (image.layout.cell image.view token column).toOption
  let (offset, width) ← (image.layout.cellAt token column).toOption
  guard (value < 256 ^ width)
  let changes := (List.range width).map fun i => (offset + i, ((old ^^^ value) / 256 ^ i) % 256)
  return {app with image := Tests.StrictBinding.flipBytes app.image changes}

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
  let altered ← if cycle then replaceCell original nested 0 ((nested % 2^24) * 4 + 3)
    else replaceCell original second typeNameColumn outerName
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
  let altered ← replaceCell caller nested typeNameColumn name
  let some family ← (enumDefinition? target 0 [CIL.Extraction.bytesOf "Far",
    CIL.Extraction.bytesOf "Family"]).toOption | none
  match checked [altered, library] Extracted.methodEvidence with
  | .error (.typeDefMismatch row .typeName) => return row == family
  | _ => return false

/-- A conflicting nested name fails at the enclosing TypeDef in the supplied destination. -/
theorem missingChildRejected : missingChild = some true := by decide +kernel
#print axioms missingChildRejected

end TwoCatalogCases
