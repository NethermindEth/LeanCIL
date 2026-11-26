import CIL.Extraction.MetadataBytes

/-! Assemblies that handwritten metadata and evidence pin, and the scope their type names carry. -/

namespace Tests
open CIL CIL.Extraction

/-- An unsigned assembly with neutral culture at version `major`.0.0.0, as handwritten
    `Assembly` rows state it. -/
def unsignedAssembly (name : MetadataName) (major : Nat := 1) : AssemblyName :=
  ⟨name, ⟨major, 0, 0, 0⟩, name!"", none⟩

/-- The assembly handwritten bodies and dispatch fixtures pin. -/
def fixtureAssembly : AssemblyName := unsignedAssembly name!"Fixture"

/-- The scope text of `fixtureAssembly` in scoped type names such as `fixtureScope ++ "::T"`. -/
def fixtureScope : String := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- Scoped type names spelled with `fixtureScope` name `fixtureAssembly`. -/
theorem fixtureAssembly_spelledAs : fixtureAssembly.spelledAs fixtureScope = true := by
  decide +kernel

#print axioms fixtureAssembly_spelledAs

end Tests
