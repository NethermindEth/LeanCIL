import CIL.Extraction.Translation

/-!
# Assembly attribution checks

Kernel-checked accept and reject cases for `AttributionValid`, the certificate conjunct that
names the pinned assembly of every extracted body, and for `AssemblyPinsValid`, which also
lists every pinned assembly once. Rejections cover a body owned by another assembly, an
unlisted or duplicated assembly and malformed identities.
-/

namespace Tests.AssemblyPins

open CIL.Extraction

private def app : AssemblyPin :=
  { identity := "App, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" }
private def lib : AssemblyPin :=
  { identity := "Lib, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" }

private def appOwner : String := app.identity ++ "::Fixture.Application"
private def libOwner : String := lib.identity ++ "::Fixture.Mix"

/-- Bodies from two pinned assemblies, each owned by its own pin, are accepted. -/
theorem two_assemblies_accepted :
    AssemblyPinsValid [app, lib] [(app, appOwner), (lib, libOwner)] := by decide +kernel
#print axioms two_assemblies_accepted

/-- The certificate conjunct accepts the same attribution. -/
theorem attribution_accepted : AttributionValid [(app, appOwner), (lib, libOwner)] = true := by
  decide +kernel
#print axioms attribution_accepted

/-- A body whose owner is scoped by another assembly is rejected. -/
theorem wrong_assembly_rejected : AttributionValid [(app, libOwner)] = false := by decide +kernel
#print axioms wrong_assembly_rejected

/-- A body attributed to an assembly outside the pin list is rejected. -/
theorem unlisted_pin_rejected : ¬ AssemblyPinsValid [app] [(lib, libOwner)] := by decide +kernel
#print axioms unlisted_pin_rejected

/-- One assembly listed twice is rejected, so each pin names one input. -/
theorem duplicate_identity_rejected : ¬ AssemblyPinsValid [app, app] [(app, appOwner)] := by
  decide +kernel
#print axioms duplicate_identity_rejected

/-- An identity containing `::` could prefix another scope, so it is rejected. -/
theorem scoped_identity_rejected :
    AttributionValid [({ identity := "App::Fixture" }, "App::Fixture::Fixture.Application")] =
      false := by decide +kernel
#print axioms scoped_identity_rejected

/-- An owner that only extends the identity's text, without `::`, is not owned by it. -/
theorem prefix_without_scope_rejected :
    AttributionValid [(app, app.identity ++ "Extra::Fixture.Application")] = false := by
  decide +kernel
#print axioms prefix_without_scope_rejected

/-- The default pin of hand-built evidence is not a valid attribution. -/
theorem default_pin_rejected : AttributionValid [({}, "::Fixture.Application")] = false := by
  decide +kernel
#print axioms default_pin_rejected

end Tests.AssemblyPins
