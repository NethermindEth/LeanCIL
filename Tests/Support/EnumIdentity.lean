import CIL.TypeExpr
import Tests.Support.FixtureAssembly

/-! Physical enum declarations used in handwritten metadata and storage fixtures. -/

namespace Tests
open CIL CIL.Extraction

/-- A fixture enum in the namespace and enclosing types of its conventional spelling. -/
def enumIdentity (fullName : String) (assembly := fixtureAssembly) : TypeIdentity :=
  let levels := (ClassName.ofText fullName).levels.reverse
  let row := levels.headD ⟨name!"", name!""⟩
  ⟨assembly, row.typeNamespace, levels.tail.reverse, row.name⟩

end Tests
