import CIL.TypeExpr

/-! Physical enum declarations used in handwritten metadata and storage fixtures. -/

namespace Tests
open CIL CIL.Extraction

/-- An unsigned fixture assembly with a single version and neutral culture. -/
def enumAssembly (name : MetadataName) : AssemblyName :=
  ⟨name, ⟨1, 0, 0, 0⟩, name!"", none⟩

/-- A fixture enum in the namespace and enclosing types of its conventional spelling. -/
def enumIdentity (fullName : String) (assembly := enumAssembly name!"Fixture") : TypeIdentity :=
  let levels := (ClassName.ofText fullName).levels.reverse
  let row := levels.headD ⟨name!"", name!""⟩
  ⟨assembly, row.typeNamespace, levels.tail.reverse, row.name⟩

end Tests
