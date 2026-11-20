import StrictBinding.TypeDefs
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

/-!
# Strict binding tests: type definitions

Every TypeDef row of the fixture, as System.Reflection.Metadata reads it, must be accepted at its
row: an enum, a struct, classes that extend `System.Object` through a TypeRef, classes that extend
another TypeDef, and a type whose fields run to the end of the Field table. Each rejection then
changes one part of a claim that passes, or one byte of the file, and asserts the exact error:
the name, the namespace, a nesting the row does not have, the kind, the Field rows and the base
type.
-/

namespace Tests.StrictBinding.TypeDefs

open _root_.StrictBinding

/-- The fixture image pinned under its own identity. -/
private def pinned : List PinnedImage :=
  [{ identity := StrictFixture.identity, image := StrictFixture.image }]

/-- The namespace of the fixture's own types. -/
private def fixtureNamespace : List Nat := asciiOf "StrictFixture"

/-- A TypeRef to `System` type `name`, as the fixture's TypeRef row `row` is. -/
private def systemBase (row : Nat) (name : String) : BaseType :=
  .named (tokenOf 0x01 row) systemNamespace (asciiOf name)

/-- A base type naming TypeDef row `row` of the fixture, in its namespace, with `name`. -/
private def fixtureBase (row : Nat) (name : String) : BaseType :=
  .named (tokenOf 0x02 row) fixtureNamespace (asciiOf name)

/-- A claim about TypeDef row `row` of the fixture. -/
private def claim (row : Nat) (typeNamespace : List Nat) (typeName : String) (kind : TypeKind)
    (fields : Nat × Nat) (base : BaseType) : TypeDefClaim :=
  { identity := StrictFixture.identity, row, typeNamespace, typeName := asciiOf typeName,
    nesting := .topLevel 1, kind, fields, base }

/-- The class `Shape`, which Triangle and Square extend. -/
private def shape : TypeDefClaim :=
  claim 5 fixtureNamespace "Shape" .classType (6, 0) (systemBase 9 "Object")

/-- The class `Triangle`, which extends the TypeDef row of `Shape`. -/
private def triangle : TypeDefClaim :=
  claim 6 fixtureNamespace "Triangle" .classType (6, 0) (fixtureBase 5 "Shape")

/-- The byte enum `Small`, which owns its `value__` field and two constants. -/
private def small : TypeDefClaim :=
  claim 2 fixtureNamespace "Small" .enum (1, 3) (systemBase 7 "Enum")

/-- The explicit-layout struct `Overlay`. -/
private def overlay : TypeDefClaim :=
  claim 3 fixtureNamespace "Overlay" .valueType (4, 2) (systemBase 8 "ValueType")

/-- Every TypeDef row of the fixture, in row order. -/
private def claims : List TypeDefClaim :=
  [claim 1 [] "<Module>" .classType (1, 0) .none, small, overlay,
   claim 4 fixtureNamespace "Arithmetic" .classType (6, 0) (systemBase 9 "Object"), shape,
   triangle, { triangle with row := 7, typeName := asciiOf "Square" },
   claim 8 [] "<PrivateImplementationDetails>" .classType (6, 1) (systemBase 9 "Object")]

theorem every_fixture_type_definition_is_found_at_its_row : TypeDefsBound pinned claims := by
  decide +kernel
#print axioms every_fixture_type_definition_is_found_at_its_row

/-- The file offset of TypeDef row `row`, from the reader's table position and row size. -/
private def typeDefRowStart (row : Nat) : Nat :=
  (StrictFixture.expectedFacts.filterMap fun fact =>
    match fact with
    | .table 0x02 _ size offset => some (offset + (row - 1) * size)
    | _ => none).headD 0

/-- The result of checking one claim against the fixture. -/
private def check (claim : TypeDefClaim) : Except AuditError Unit :=
  checkAll typeDefClaimBound pinned [claim]

theorem rejects_another_name :
    failsWith (check { shape with typeName := asciiOf "Shapes" })
      (.typeDefMismatch 5 .typeName) = true := by decide +kernel
#print axioms rejects_another_name

theorem rejects_another_namespace :
    failsWith (check { shape with typeNamespace := asciiOf "StrictFixtures" })
      (.typeDefMismatch 5 .typeNamespace) = true := by decide +kernel
#print axioms rejects_another_namespace

/-- A top-level row has a top-level visibility, so it is not nested in any row. -/
theorem rejects_a_nesting_the_row_does_not_have :
    failsWith (check { shape with nesting := .nested 1 4 })
      (.typeDefMismatch 5 .nesting) = true := by decide +kernel
#print axioms rejects_a_nesting_the_row_does_not_have

/-- The fixture has no NestedClass rows, so the only bracket is the empty table. -/
theorem rejects_a_bracket_past_the_table :
    failsWith (check { shape with nesting := .topLevel 2 })
      (.typeDefMismatch 5 .nesting) = true := by decide +kernel
#print axioms rejects_a_bracket_past_the_table

/-- An empty NestedClass table is sorted by any key. -/
theorem accepts_the_empty_nested_class_table :
    TablesSorted pinned
      [{ identity := StrictFixture.identity, table := 0x29, key := nestedClassKey }] := by
  decide +kernel
#print axioms accepts_the_empty_nested_class_table

theorem rejects_an_enum_claimed_as_a_struct :
    failsWith (check { small with kind := .valueType }) (.typeDefMismatch 2 .kind) = true := by
  decide +kernel
#print axioms rejects_an_enum_claimed_as_a_struct

theorem rejects_a_struct_claimed_as_a_class :
    failsWith (check { overlay with kind := .classType }) (.typeDefMismatch 3 .kind) = true := by
  decide +kernel
#print axioms rejects_a_struct_claimed_as_a_class

theorem rejects_a_class_claimed_as_a_struct :
    failsWith (check { shape with kind := .valueType }) (.typeDefMismatch 5 .kind) = true := by
  decide +kernel
#print axioms rejects_a_class_claimed_as_a_struct

/-- With the interface bit set in its flags, the row of `Shape` defines an interface. -/
theorem rejects_a_class_whose_row_is_an_interface :
    failsWith (checkAll typeDefClaimBound
        [{ identity := StrictFixture.identity,
           image := flipByte StrictFixture.image (typeDefRowStart 5) interfaceFlag }] [shape])
      (.typeDefMismatch 5 .kind) = true := by decide +kernel
#print axioms rejects_a_class_whose_row_is_an_interface

theorem rejects_one_field_fewer :
    failsWith (check { overlay with fields := (4, 1) }) (.typeDefMismatch 3 .fields) = true := by
  decide +kernel
#print axioms rejects_one_field_fewer

theorem rejects_a_shifted_field_list :
    failsWith (check { overlay with fields := (5, 2) }) (.typeDefMismatch 3 .fields) = true := by
  decide +kernel
#print axioms rejects_a_shifted_field_list

theorem rejects_the_last_row_owning_no_field :
    failsWith (check (claim 8 [] "<PrivateImplementationDetails>" .classType (6, 0)
        (systemBase 9 "Object"))) (.typeDefMismatch 8 .fields) = true := by decide +kernel
#print axioms rejects_the_last_row_owning_no_field

theorem rejects_another_base_row :
    failsWith (check { triangle with base := fixtureBase 4 "Shape" })
      (.typeDefMismatch 6 .base) = true := by decide +kernel
#print axioms rejects_another_base_row

theorem rejects_another_base_name :
    failsWith (check { triangle with base := fixtureBase 5 "Square" })
      (.typeDefMismatch 6 .base) = true := by decide +kernel
#print axioms rejects_another_base_name

theorem rejects_no_base_for_a_class :
    failsWith (check { shape with base := .none }) (.typeDefMismatch 5 .base) = true := by
  decide +kernel
#print axioms rejects_no_base_for_a_class

theorem rejects_a_generic_base_for_a_class :
    failsWith (check { shape with base := .spec (tokenOf 0x1B 1) })
      (.typeDefMismatch 5 .base) = true := by decide +kernel
#print axioms rejects_a_generic_base_for_a_class

theorem rejects_a_row_past_the_table :
    failsWith (check { shape with row := 9 }) (.tokenOutOfScope (tokenOf 0x02 9)) = true := by
  decide +kernel
#print axioms rejects_a_row_past_the_table

/-- An oversized claimed row fails before the auditor reads the TypeDef flags. -/
theorem rejects_a_row_above_24_bits :
    failsWith (check { shape with row := 0x1000001 }) (.rowOverflow 0x02 0x1000001) := by
  decide +kernel
#print axioms rejects_a_row_above_24_bits

/-- The fixture uses two-byte heap and table indexes. The base, field list and method list
    follow the four flag bytes and the two name indexes in each TypeDef row. -/
private def checkChanged (claim : TypeDefClaim) (row columnOffset before after : Nat) :=
  let image := flipByte StrictFixture.image (typeDefRowStart row + columnOffset) (before ^^^ after)
  checkAll typeDefClaimBound [{ identity := StrictFixture.identity, image }] [claim]

/-- A matching base specification can name the fixture's existing TypeSpec row. -/
theorem accepts_an_existing_base_specification :
    (checkChanged { shape with base := .spec (tokenOf 0x1B 1) } 5 8 37 6).isOk := by
  decide +kernel
#print axioms accepts_an_existing_base_specification

/-- A matching coded index still has to select an existing TypeSpec row. The fixture owns one. -/
theorem rejects_a_missing_base_specification :
    failsWith (checkChanged { shape with base := .spec (tokenOf 0x1B 2) } 5 8 37 10)
      (.tokenOutOfScope (tokenOf 0x1B 2)) := by decide +kernel
#print axioms rejects_a_missing_base_specification

/-- A nil TypeSpec token cannot designate a generic base. -/
theorem rejects_a_nil_base_specification :
    failsWith (checkChanged { shape with base := .spec (tokenOf 0x1B 0) } 5 8 37 2)
      (.tokenOutOfScope (tokenOf 0x1B 0)) := by decide +kernel
#print axioms rejects_a_nil_base_specification

/-- The range cannot start at row zero, even if the claim copies the malformed range. -/
theorem rejects_a_nil_field_list :
    failsWith (checkChanged { shape with fields := (0, 6) } 5 10 6 0)
      (.typeDefMismatch 5 .fields) := by decide +kernel
#print axioms rejects_a_nil_field_list

/-- The next type cannot extend its predecessor's range past the fixture's six Field rows. -/
theorem rejects_fields_past_the_table :
    failsWith (checkChanged { shape with fields := (6, 3) } 6 10 6 9)
      (.typeDefMismatch 5 .fields) := by decide +kernel
#print axioms rejects_fields_past_the_table

end Tests.StrictBinding.TypeDefs
