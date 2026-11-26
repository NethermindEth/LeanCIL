import CIL.Extraction.MetadataBinding
import Tests.MetadataWorld

/-!
# Field references

Pins `FieldRef`, the typed field operand: a literal elaborates and equality decides on it, a
reference that differs from another in any one of owner, index, type or name is unequal to it,
and `FieldRef.ofOperand?` reads the operand of the metadata world's `T.Program.count` into the
reference with the operand's owner, index, type and name.
-/

namespace Tests.FieldRef

open CIL CIL.Extraction Tests.MetadataWorld

/-- The owner of the metadata world's fields. -/
private def program : TypeExpr := .atom ownScope "Program" .classType

/-- `T.Program.count`, the first instance field of `Program`, holding an `int32`. -/
private def countField : FieldRef :=
  { owner := program, index := 0, type := int32, name := name!"count" }

-- A literal elaborates and compares equal to itself spelled again.
theorem decides_a_literal :
    countField =
      { owner := .atom ownScope "Program" .classType, index := 0,
        type := .primitive .int32, name := name!"count" } := by decide +kernel
#print axioms decides_a_literal

theorem another_owner_is_another_field :
    countField ≠ { countField with owner := .atom ownScope "Other" .classType } := by
  decide +kernel
#print axioms another_owner_is_another_field

theorem another_index_is_another_field :
    countField ≠ { countField with index := 1 } := by decide +kernel
#print axioms another_index_is_another_field

theorem another_type_is_another_field :
    countField ≠ { countField with type := uint32 } := by decide +kernel
#print axioms another_type_is_another_field

theorem another_name_is_another_field :
    countField ≠ { countField with name := name!"total" } := by decide +kernel
#print axioms another_name_is_another_field

/-- The count field's operand gives the count field. -/
theorem builds_the_count_field :
    FieldRef.ofOperand? countOperand = some countField := by decide +kernel
#print axioms builds_the_count_field

/-- An operand other than a field gives no reference. -/
theorem refuses_an_operand_that_is_not_a_field :
    FieldRef.ofOperand? (.type int32) = none := by decide +kernel
#print axioms refuses_an_operand_that_is_not_a_field

end Tests.FieldRef
