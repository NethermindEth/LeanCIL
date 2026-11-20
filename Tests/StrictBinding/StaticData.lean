import StrictBinding.StaticData
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

/-! The fixture's eight static bytes belong to Field row 6. -/
namespace Tests.StrictBinding.StaticData
open _root_.StrictBinding

private def field := tokenOf CIL.Extraction.Table.field 6
private def bytes : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]

private def check (raw : ImageBytes) (expected : List Nat := bytes) (token := field) :
    Except AuditError Unit := do
  let image ← prepareOne ⟨StrictFixture.identity, raw⟩
  let rows ← fieldRvaIndex image
  let some row := rows[token]? | throw (.invalidFieldData token)
  fieldDataAt image token row 1 expected

theorem static_bytes_match : ok (check StrictFixture.image) = true := by decide +kernel
#print axioms static_bytes_match

/-- The FieldRVA of the compiled Table property is 10064 in the section starting at RVA 8192
    and file offset 512. Changing its last byte preserves the PE and every metadata row. -/
theorem rejects_changed_image_data :
    failsWith (check (flipByte StrictFixture.image (512 + 10064 - 8192 + 7) 1))
      (.fieldDataMismatch field 10064 2384) = true := by decide +kernel
#print axioms rejects_changed_image_data

theorem rejects_changed_descriptor :
    failsWith (check StrictFixture.image [1, 2, 3, 4, 5, 6, 7, 0])
      (.fieldDataMismatch field 10064 2384) = true := by decide +kernel
#print axioms rejects_changed_descriptor

theorem rejects_another_field :
    failsWith (check StrictFixture.image bytes (tokenOf 4 5)) (.invalidFieldData (tokenOf 4 5)) = true := by
  decide +kernel
#print axioms rejects_another_field

/-- Moving the RVA back eight bytes keeps the entire range inside the same section. -/
theorem rejects_another_in_section_position :
    failsWith (check (flipByte StrictFixture.image 1410 24))
      (.fieldDataMismatch field 10056 2376) = true := by decide +kernel
#print axioms rejects_another_in_section_position

/-- Changing the row's Field index from 6 to the absent row 7 is rejected before reading data. -/
theorem rejects_out_of_range_field :
    failsWith (check (flipByte StrictFixture.image 1414 1))
      (.invalidDataTableKey fieldRvaTable 1 7) = true := by decide +kernel
#print axioms rejects_out_of_range_field

end Tests.StrictBinding.StaticData
