import StrictBinding.EnumEvidence
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

namespace Tests.StrictBinding.EnumEvidence

open CIL CIL.Extraction _root_.StrictBinding

private def small (code : Nat) : PlatformDefinition :=
  { assembly := StrictFixture.assembly
    parts := [asciiOf "StrictFixture", asciiOf "Small"]
    kind := .enumType code }

private def absent : PlatformDefinition :=
  { small 5 with assembly := { StrictFixture.assembly with name := name!"Absent" } }

private def check (claims : List PlatformDefinition) : Except AuditError Bool := do
  let image ← prepareOne ⟨StrictFixture.identity, StrictFixture.image⟩
  coveredEnumEntries [image] claims

/-- The compiled enum uses UInt8; both the missing assembly and a broken supplied definition
    retain their own outcomes, regardless of the order of the input list. -/
theorem compiled_storage_and_missing_images :
    (check [small 5]).toOption = some true ∧ (check [absent, small 5]).toOption = some false ∧
    failsWith (check [absent, small 9]) (.typeDefMismatch 2 .fields) = true ∧
    failsWith (check [small 9, absent]) (.typeDefMismatch 2 .fields) = true := by decide +kernel
#print axioms compiled_storage_and_missing_images

/-- A matching simple name in a different namespace, or at the wrong nesting level, cannot
    supply the row for an enum entry. -/
theorem rejects_wrong_scope_parts :
    failsWith (check [{ small 5 with parts := [[], asciiOf "Small"] }]) (.typeDefMismatch 0 .typeName) = true ∧
    failsWith (check [{ small 5 with parts := [asciiOf "StrictFixture", asciiOf "Small", [], asciiOf "Small"] }])
      (.typeDefMismatch 2 .typeName) = true := by decide +kernel
#print axioms rejects_wrong_scope_parts

/-- Select the definition using precisely the table lookup used for external signature types. -/
private def table : PlatformTable := platform_table% [small 5]

theorem compiled_table_storage :
    table.kindOf (small 5).assembly (small 5).parts = some (.enumType 5) ∧
    (check table.definitions).toOption = some true := by decide +kernel
#print axioms compiled_table_storage

end Tests.StrictBinding.EnumEvidence
