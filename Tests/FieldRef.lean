import CIL.Extraction.MetadataBinding
import Tests.MetadataWorld

/-!
# Field references

Pins `FieldRef`, the typed field operand: a literal elaborates and equality decides on it, a
reference that differs from another in any one of owner, index, type or name is unequal to it,
and `FieldRef.ofSite?` reads the count field of the metadata world's `T.Program` into the
reference its operand and its row name, refusing name bytes that are not a metadata name.
-/

namespace Tests.FieldRef

open CIL CIL.Extraction Tests.MetadataWorld

/-- The owner of the metadata world's fields. -/
private def program : TypeExpr := .atom ownIdentity "Program"

/-- `T.Program.count`, the first instance field of `Program`, holding an `int32`. -/
private def countField : FieldRef :=
  { owner := program, index := 0, type := int32, name := name!"count" }

-- A literal elaborates and compares equal to itself spelled again.
theorem decides_a_literal :
    countField = { owner := .atom ownIdentity "Program", index := 0,
      type := .atom runtimeScope "System.Int32", name := name!"count" } := by decide +kernel
#print axioms decides_a_literal

theorem another_owner_is_another_field :
    countField ≠ { countField with owner := .atom ownIdentity "Other" } := by decide +kernel
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

/-- The site the count field's token reads as in the metadata world. -/
private def countSite : Option FieldSite :=
  (do
    let env := MetadataEnv.ofSlices [← own.1.index, ← lib.index]
    env.fieldSite tokens.countField).toOption

/-- The count field's operand and site give the count field. -/
theorem builds_the_count_field :
    countSite.bind (FieldRef.ofSite? countOperand) = some countField := by decide +kernel
#print axioms builds_the_count_field

/-- A site whose name holds an entry above 255 names no field. -/
theorem refuses_a_name_that_is_not_bytes :
    countSite.bind (fun site => FieldRef.ofSite? countOperand { site with name := [99, 256] }) =
      none := by decide +kernel
#print axioms refuses_a_name_that_is_not_bytes

/-- An operand other than a field gives no reference, whatever the site. -/
theorem refuses_an_operand_that_is_not_a_field :
    countSite.bind (FieldRef.ofSite? (.type int32)) = none := by decide +kernel
#print axioms refuses_an_operand_that_is_not_a_field

end Tests.FieldRef
