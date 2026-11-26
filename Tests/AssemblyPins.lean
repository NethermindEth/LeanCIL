import Tests.Support.EnumIdentity
import CIL.Extraction.Translation

/-!
# Assembly attribution checks

Kernel-checked accept and reject cases for `AttributionValid`, the certificate conjunct that
names the pinned assembly of every extracted body, and for `AssemblyName.scopes`, which ties a
typed assembly to the scope of a type name. Rejections cover a body owned by another assembly, a
body attributed to its caller's assembly, an owner Lean did not read, assemblies that differ in
one identity field only and spellings that could prefix another scope.
-/

namespace Tests.AssemblyPins

open CIL CIL.Extraction

private def appAssembly : AssemblyName := unsignedAssembly name!"App"
private def libAssembly : AssemblyName := unsignedAssembly name!"Lib"
private def app : AssemblyPin := ⟨appAssembly⟩
private def lib : AssemblyPin := ⟨libAssembly⟩

/-- Bodies from two pinned assemblies, each owned by its own pin, are accepted. -/
theorem two_assemblies_accepted :
    AttributionValid [(app, some appAssembly), (lib, some libAssembly)] = true := by
  decide +kernel
#print axioms two_assemblies_accepted

/-- A body whose owner is defined in another assembly is rejected. -/
theorem wrong_assembly_rejected : AttributionValid [(app, some libAssembly)] = false := by
  decide +kernel
#print axioms wrong_assembly_rejected

/-- A referenced body attributed to the caller's assembly is rejected. -/
theorem caller_attribution_rejected :
    AttributionValid [(app, some appAssembly), (app, some libAssembly)] = false := by
  decide +kernel
#print axioms caller_attribution_rejected

/-- An owner whose assembly Lean did not read is rejected. -/
theorem unread_owner_rejected : AttributionValid [(app, none)] = false := by decide +kernel
#print axioms unread_owner_rejected

/-- An owner in an assembly that differs from the pin only in version, in a culture named
    `neutral`, which displays as the neutral culture, or in its key token is rejected. -/
theorem identity_fields_distinguish_owners :
    AttributionValid [(app, some (unsignedAssembly name!"App" 2))] = false ∧
    AttributionValid [(app, some { appAssembly with culture := name!"neutral" })] = false ∧
    AttributionValid [(app, some { appAssembly with publicKeyToken := some 0 })] = false := by
  decide +kernel
#print axioms identity_fields_distinguish_owners

/-- An owner is scoped by the spelling of its assembly followed by `::`; text that only extends
    the spelling, or the spelling of another assembly, does not scope it. -/
theorem owner_scopes :
    appAssembly.scopes "App, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::A.B" = true ∧
    appAssembly.scopes "App, Version=1.0.0.0, Culture=neutral, PublicKeyToken=nullX::A.B" =
      false ∧
    libAssembly.scopes "App, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::A.B" =
      false := by
  decide +kernel
#print axioms owner_scopes

/-- A spelling containing `:` could prefix another assembly's scope, so it scopes no owner. -/
theorem colon_spelling_scopes_nothing :
    (unsignedAssembly name!"App::Fixture").scopes
      "App::Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::A.B" = false ∧
    (unsignedAssembly name!"App::Fixture").spelledAs
      "App::Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" = false := by
  decide +kernel
#print axioms colon_spelling_scopes_nothing

/-- A generic argument's scope does not change the declaring aggregate's or enum's scope. -/
theorem flat_scopes :
    (TypeExpr.aggregate "Lib::Box<App::Value>" 0).headScope = some "Lib" ∧
    (TypeExpr.enum (Tests.enumIdentity "Flag" (unsignedAssembly name!"Λ")) .unsigned8).headScope =
      some "Λ, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" := by
  decide +kernel
#print axioms flat_scopes

/-- Flat owners without a scope, separator or type name supply no assembly identity. -/
theorem incomplete_flat_scopes :
    ["Value", "::Value", "Lib:Value", "Lib::"].all
      (fun owner => (TypeExpr.aggregate owner 0).headScope.isNone) := by decide +kernel
#print axioms incomplete_flat_scopes

end Tests.AssemblyPins
