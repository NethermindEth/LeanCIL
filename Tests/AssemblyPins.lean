import CIL.Extraction.Translation

/-!
# Assembly attribution checks

Kernel-checked accept and reject cases for `AssemblyPinsValid`, the certificate conjunct that
names the pinned assembly of every extracted body. Rejections cover a duplicated identity, the
same bytes under two identities, a body owned by another assembly and malformed pins.
-/

namespace Tests.AssemblyPins

open CIL.Extraction

/-- A digest of the right length and alphabet; its value is arbitrary. -/
private def digest (fill : Char) : String := String.ofList (List.replicate sha256Digits fill)

private def app : AssemblyPin :=
  { identity := "App, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null",
    mvid := "00000000-0000-0000-0000-000000000001", sha256 := digest 'a' }

private def lib : AssemblyPin :=
  { identity := "Lib, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null",
    mvid := "00000000-0000-0000-0000-000000000002", sha256 := digest 'b' }

private def appOwner : String := app.identity ++ "::Fixture.Application"
private def libOwner : String := lib.identity ++ "::Fixture.Mix"

/-- Bodies from two pinned assemblies, each owned by its own pin, are accepted. -/
theorem two_assemblies_accepted :
    AssemblyPinsValid [app, lib] [(app, appOwner), (lib, libOwner)] := by decide +kernel
#print axioms two_assemblies_accepted

/-- A body whose owner is scoped by another assembly is rejected. -/
theorem wrong_assembly_rejected :
    ¬ AssemblyPinsValid [app, lib] [(app, libOwner)] := by decide +kernel
#print axioms wrong_assembly_rejected

/-- A body attributed to an assembly outside the pin list is rejected. -/
theorem unlisted_pin_rejected :
    ¬ AssemblyPinsValid [app] [(lib, libOwner)] := by decide +kernel
#print axioms unlisted_pin_rejected

/-- One identity with two different digests, a substituted assembly, is rejected. -/
theorem duplicate_identity_rejected :
    ¬ AssemblyPinsValid [app, { lib with identity := app.identity }] [(app, appOwner)] := by
  decide +kernel
#print axioms duplicate_identity_rejected

/-- The same bytes recorded under two identities are rejected. -/
theorem shared_digest_rejected :
    ¬ AssemblyPinsValid [app, { lib with sha256 := app.sha256 }] [(app, appOwner)] := by
  decide +kernel
#print axioms shared_digest_rejected

/-- A truncated digest is rejected. -/
theorem short_digest_rejected :
    ¬ AssemblyPinsValid [{ app with sha256 := "abc" }] [] := by decide +kernel
#print axioms short_digest_rejected

/-- An uppercase digest is rejected, so each hash has one spelling. -/
theorem uppercase_digest_rejected :
    ¬ AssemblyPinsValid [{ app with sha256 := digest 'A' }] [] := by decide +kernel
#print axioms uppercase_digest_rejected

/-- An identity containing `::` could prefix another scope, so it is rejected. -/
theorem scoped_identity_rejected :
    ¬ AssemblyPinsValid [{ app with identity := "App::Fixture" }] [] := by decide +kernel
#print axioms scoped_identity_rejected

/-- An owner that only extends the identity's text, without `::`, is not owned by it. -/
theorem prefix_without_scope_rejected :
    ¬ AssemblyPinsValid [app] [(app, app.identity ++ "Extra::Fixture.Application")] := by
  decide +kernel
#print axioms prefix_without_scope_rejected

/-- The default pin of hand-built evidence is not a valid attribution. -/
theorem default_pin_rejected :
    ¬ AssemblyPinsValid [{}] [({}, appOwner)] := by decide +kernel
#print axioms default_pin_rejected

end Tests.AssemblyPins
