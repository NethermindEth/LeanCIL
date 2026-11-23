import Extracted
import AppImage
import LibImage
import StrictBinding.DispatchCatalogs

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

/-- Both bodies test their own physically bound class in the same extraction. -/
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

end TwoCatalogCases
