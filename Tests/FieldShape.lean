import CIL.Safety.ResolutionFacts

/-!
# Field and value shapes

Pins `CIL.LayoutEnvironment.fieldShape`, `valueShape` and the facts `cil_field_shape` and
`cil_value_shape` declare, over a hand-written environment of three structs. A struct field
resolves to the offset and width of its checked layout entry, sign-extended only when it is
declared as a narrow signed integer; a field whose index or held type does not match the
declaration is unsupported; a class field resolves to the model slot of its index, a struct array
element taking its size from the layout; and a method, defined or known by a hypothesis on its
environment, reads the shared facts through the `cil_code` simprocs.
-/

namespace Tests.FieldShape

open CIL CIL.Extraction

/-- The test assembly's scope. -/
private def scope : String := "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- `T::Inner`, one `int32`; `T::Pair`, an `int16`, a `uint32` and an `Inner`; `T::Ref`, a
    byref-like struct. -/
def rawLayouts : List RawLayout := [
  { identity := "T::Inner", explicit := false, packing := 0, declaredSize := 0,
    fields := [{ type := .signed32 }] },
  { identity := "T::Pair", explicit := false, packing := 0, declaredSize := 0,
    fields := [{ type := .signed16 }, { type := .unsigned32 }, { type := .aggregate 0 }] },
  { identity := "T::Ref", explicit := false, packing := 0, declaredSize := 0, byRefLike := true,
    fields := [{ type := .signed32 }] }]

/-- The layouts CoreCLR computes for `rawLayouts`. -/
def computedLayouts : Array ComputedLayout := #[
  ⟨{ size := 4, fields := [{ offset := 0, width := 4 }] }, 4⟩,
  ⟨{ size := 12, fields := [{ offset := 0, width := 2 }, { offset := 4, width := 4 },
    { offset := 8, width := 4, aggregate := true }] }, 4⟩,
  ⟨{ size := 4, fields := [{ offset := 0, width := 4 }] }, 4⟩]

theorem layouts_valid : LayoutsValid rawLayouts computedLayouts .x64 := by decide +kernel
#print axioms layouts_valid

/-- The environment every method of the test shares. -/
@[cil_code] def environment : LayoutEnvironment :=
  { rawLayouts := rawLayouts, layouts := computedLayouts }

private def int16 : TypeExpr := .atom runtimeScope "System.Int16"
private def uint32 : TypeExpr := .atom runtimeScope "System.UInt32"
private def inner : TypeExpr := .aggregate "T::Inner" 0
private def pair : TypeExpr := .aggregate "T::Pair" 1
private def node : TypeExpr := .object scope "Node"

/-- `Pair.low`, the `int16` at offset 0. -/
def lowField : FieldRef := { owner := pair, index := 0, type := int16, name := name!"low" }
/-- `Pair.high`, the `uint32` at offset 4. -/
def highField : FieldRef := { owner := pair, index := 1, type := uint32, name := name!"high" }
/-- `Pair.inner`, the nested struct at offset 8. -/
def innerField : FieldRef := { owner := pair, index := 2, type := inner, name := name!"inner" }

cil_field_shape environment lowField
cil_field_shape environment highField
cil_field_shape environment innerField

-- Each fact states the layout entry's offset and width; only the narrow signed field extends.
theorem low_at_its_layout (body : Method) (shared : body.environment = environment) :
    body.fieldShape lowField = .value 0 2 true := lowField_shape shared
#print axioms low_at_its_layout

theorem high_at_its_layout (body : Method) (shared : body.environment = environment) :
    body.fieldShape highField = .value 4 4 false := highField_shape shared
#print axioms high_at_its_layout

theorem inner_at_its_layout (body : Method) (shared : body.environment = environment) :
    body.fieldShape innerField = .aggregate 8 4 := innerField_shape shared
#print axioms inner_at_its_layout

/-- The test's one method, which shares the environment. -/
def body : Method := { code := [], locals := [], returnsValue := false, environment }

-- A method reads a shared fact through `cil_code`, which unfolds the method's environment.
theorem body_reads_high : body.fieldShape highField = .value 4 4 false := by
  simp only [cil_code]
#print axioms body_reads_high

-- A method known only by a hypothesis on its environment reads the fact through that hypothesis.
theorem hypothesis_reads_low (method : Method) (shared : method.environment = environment) :
    method.fieldShape lowField = .value 0 2 true := by
  simp only [cil_code]
#print axioms hypothesis_reads_low

-- An index whose declared type is not the held type, and an index past the fields, are refused.
theorem refuses_a_mismatched_index :
    environment.fieldShape { highField with index := 0 } =
      .unsupported "Field outside the checked layouts" := by decide +kernel
#print axioms refuses_a_mismatched_index

theorem refuses_an_index_past_the_fields :
    environment.fieldShape { highField with index := 3 } =
      .unsupported "Field outside the checked layouts" := by decide +kernel
#print axioms refuses_an_index_past_the_fields

theorem refuses_an_owner_that_is_not_a_value_type :
    environment.fieldShape { highField with owner := uint32 } =
      .unsupported "Field owner is not a value type" := by decide +kernel
#print axioms refuses_an_owner_that_is_not_a_value_type

-- A class field sits in the model slot of its index, whatever the struct layouts.
theorem class_word_slot :
    environment.fieldShape { owner := node, index := 2, type := int16, name := name!"count" } =
      .classSlot 16 (.word 2 true) := by decide +kernel
#print axioms class_word_slot

theorem class_reference_slot :
    environment.fieldShape { owner := node, index := 1, type := node, name := name!"next" } =
      .classSlot 8 .reference := by decide +kernel
#print axioms class_reference_slot

-- A struct array element is sized by its layout; a byref-like element has no slot.
theorem class_struct_array_slot :
    environment.fieldShape
        { owner := node, index := 0, type := .array inner, name := name!"items" } =
      .classSlot 0 (.array (.aggregate "T::Inner" 4)) := by decide +kernel
#print axioms class_struct_array_slot

/-- `Node.lanes`, an array of `Vector128<ulong>`, whose element name the resolver renders. -/
def lanesField : FieldRef :=
  { owner := node, index := 1, name := name!"lanes",
    type := .array (.apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1")
      (.atom runtimeScope "System.UInt64")) }

cil_field_shape environment lanesField

-- A vector array slot names its element as the evaluation stack records it.
theorem lanes_vector_slot (method : Method) (shared : method.environment = environment) :
    method.fieldShape lanesField =
      .classSlot 8 (.array (.vector "System.Runtime.Intrinsics.Vector128`1<System.UInt64>" 16)) :=
  lanesField_shape shared
#print axioms lanes_vector_slot

theorem refuses_a_byref_like_array_slot :
    environment.fieldShape
        { owner := node, index := 0, type := .array (.aggregate "T::Ref" 2),
          name := name!"items" } =
      .unsupported "Class instance field type" := by decide +kernel
#print axioms refuses_a_byref_like_array_slot

theorem refuses_a_double_slot :
    environment.fieldShape
        { owner := node, index := 3, type := .atom runtimeScope "System.Double",
          name := name!"ratio" } =
      .unsupported "Class instance field type" := by decide +kernel
#print axioms refuses_a_double_slot

-- A class slot's offset is the model offset of the field's index.
theorem class_offset_from_shape (field : FieldRef) (offset : Nat) (slot : ClassSlot)
    (shape : environment.fieldShape field = .classSlot offset slot) :
    offset = 8 * field.index := (LayoutEnvironment.fieldShape_class_offset shape).1
#print axioms class_offset_from_shape

/-- `T::Pair` as a type operand. -/
def pairType : TypeExpr := pair
/-- `System.Int16` as a type operand. -/
def shortType : TypeExpr := int16

cil_value_shape environment pairType
cil_value_shape environment shortType

theorem pair_value_size (body : Method) (shared : body.environment = environment) :
    body.valueShape pairType = .aggregate 12 := pairType_shape shared
#print axioms pair_value_size

theorem short_value_width (body : Method) (shared : body.environment = environment) :
    body.valueShape shortType = .primitive 2 true := shortType_shape shared
#print axioms short_value_width

-- Integer vectors and spans resolve before layouts; a double vector is no value type here.
theorem value_kinds :
    environment.valueShape (.apply (.constructor intrinsicsScope
        "System.Runtime.Intrinsics.Vector128`1") (.atom runtimeScope "System.Int32")) =
      .vector 16 ∧
    environment.valueShape (.apply (.constructor runtimeScope "System.Span`1") int16) = .span ∧
    environment.valueShape (.apply (.constructor intrinsicsScope
        "System.Runtime.Intrinsics.Vector128`1") (.atom runtimeScope "System.Double")) =
      .unsupported "Not a value type" := by decide +kernel
#print axioms value_kinds

end Tests.FieldShape
