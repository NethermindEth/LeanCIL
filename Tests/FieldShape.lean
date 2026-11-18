import CIL.Safety.ResolutionFacts
import CIL.Safety.ObjectSteps
import CIL.Safety.FuelLemmas

/-!
# Field and value shapes

Pins `CIL.LayoutEnvironment.fieldShape`, `valueShape` and the facts `cil_field_shape` and
`cil_value_shape` declare, over a hand-written environment of three structs. A struct field
resolves to the offset and width of its checked layout entry, sign-extended only when it is
declared as a narrow signed integer; a field whose index or held type does not match the
declaration is unsupported; a class field resolves to the model slot of its index, a struct array
element taking its size from the layout; and a method, defined or known by a hypothesis on its
environment, reads the shared facts through the `cil_code` simprocs. Stepping `ldflda` of a class
field faults; a struct field steps on each receiver kind as the lowered access of its shape, and
a field operand without a fact steps to the same literal shape a fact states.
-/

namespace Tests.FieldShape

open CIL CIL.Extraction

/-- The test assembly's scope. -/
private def scope : String := "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- `T::Inner`, one `int32`; `T::Pair`, an `int16`, a `uint32` and an `Inner`; `T::Ref`, a
    byref-like struct; `T::Lanes`, a 32-byte and a 16-byte vector and an `int32`. -/
def rawLayouts : List RawLayout := [
  { identity := "T::Inner", explicit := false, packing := 0, declaredSize := 0,
    fields := [{ type := .signed32 }] },
  { identity := "T::Pair", explicit := false, packing := 0, declaredSize := 0,
    fields := [{ type := .signed16 }, { type := .unsigned32 }, { type := .aggregate 0 }] },
  { identity := "T::Ref", explicit := false, packing := 0, declaredSize := 0, byRefLike := true,
    fields := [{ type := .signed32 }] },
  { identity := "T::Lanes", explicit := false, packing := 0, declaredSize := 0,
    fields := [{ type := .vector256 }, { type := .vector128 }, { type := .signed32 }] }]

/-- The layouts CoreCLR computes for `rawLayouts`. -/
def computedLayouts : Array ComputedLayout := #[
  ⟨{ size := 4, fields := [{ offset := 0, width := 4 }] }, 4⟩,
  ⟨{ size := 12, fields := [{ offset := 0, width := 2 }, { offset := 4, width := 4 },
    { offset := 8, width := 4, aggregate := true }] }, 4⟩,
  ⟨{ size := 4, fields := [{ offset := 0, width := 4 }] }, 4⟩,
  ⟨{ size := 64, fields := [{ offset := 0, width := 32 }, { offset := 32, width := 16 },
    { offset := 48, width := 4 }] }, 32⟩]

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

-- Integer vectors and spans resolve before layouts.
theorem value_kinds :
    environment.valueShape (.apply (.constructor intrinsicsScope
        "System.Runtime.Intrinsics.Vector128`1") (.atom runtimeScope "System.Int32")) =
      .vector 16 ∧
    environment.valueShape (.apply (.constructor runtimeScope "System.Span`1") int16) = .span :=
  by decide +kernel
#print axioms value_kinds

-- A floating-point vector has its size, so `sizeof` keeps admitting it; `ldobj` and `stobj`
-- refuse it in their own rule.
theorem double_vector_size :
    (environment.valueShape (.apply (.constructor intrinsicsScope
        "System.Runtime.Intrinsics.Vector128`1") (.atom runtimeScope "System.Double"))).size? =
      some 16 := by decide +kernel
#print axioms double_vector_size

-- The kernel checks each generated fact, which rests on no axiom beyond `propext`.
/-- info: 'Tests.FieldShape.lowField_shape' depends on axioms: [propext] -/
#guard_msgs in #print axioms lowField_shape

/-- info: 'Tests.FieldShape.pairType_shape' depends on axioms: [propext] -/
#guard_msgs in #print axioms pairType_shape

/-- `Pair.high` under another name, for a fact that misstates its shape. -/
def misstatedField : FieldRef :=
  { owner := pair, index := 1, type := uint32, name := name!"misstated" }

-- The kernel refuses a fact whose shape differs from the resolver's, so no fact rests on the
-- compiled evaluation that proposes its shape. The attempt leaves no declaration behind.
open Lean Meta Elab in
set_option Elab.async false in
run_cmd Command.liftTermElabM do
  let misstate : Expr → MetaM Expr := fun _ => pure (toExpr (FieldShape.value 4 2 true))
  let refused ← withoutModifyingEnv do
    try
      Safety.ResolutionFacts.declareShapeFact .field ``environment ``misstatedField misstate
      pure false
    catch error => pure (((← error.toMessageData.toString).splitOn "(kernel)").length > 1)
  unless refused do throwError "the kernel did not refuse a misstated shape fact"
  if (← getEnv).contains `Tests.FieldShape.misstatedField_shape then
    throwError "a refused shape fact stayed in the environment"

/-- `Node.count`, an `int32` class field at raw index 0. -/
def countField : FieldRef :=
  { owner := node, index := 0, type := .atom runtimeScope "System.Int32", name := name!"count" }

-- `ldflda` of a class field faults as unsupported, since the model forms no address into an
-- object; the fault is not definite, so no refutation lemma takes it as evidence about the method.
theorem class_field_address_faults (frame : Safety.Frame) (memory : Safety.Memory)
    (receiver : Safety.ManagedReference) :
    Safety.step body (.ldflda countField) 0 [] frame [.object receiver] memory =
      .error (.unsupported "Class field address") ∧
    (Safety.ExecutionFault.unsupported "Class field address").definite = false := by
  refine ⟨?_, rfl⟩
  simp only [cil_step]
#print axioms class_field_address_faults

-- A struct field of an object receiver is not a memory access, so the load faults.
theorem value_field_of_an_object_faults (frame : Safety.Frame) (memory : Safety.Memory)
    (receiver : Safety.ManagedReference) :
    Safety.step body (.ldfld highField) 0 [] frame [.object receiver] memory =
      .error (.unsupported "Not a memory instruction") := by
  simp only [cil_step, cil_code]
  rfl
#print axioms value_field_of_an_object_faults

-- A struct field steps as the lowered access its shape fact states, whatever the receiver.
theorem high_load_is_lowered (frame : Safety.Frame) (memory : Safety.Memory)
    (receiver : Safety.Value) :
    Safety.step body (.ldfld highField) 0 [] frame [receiver] memory =
      Safety.step body (.fieldAt 4 4) 0 [] frame [receiver] memory := by
  simp only [cil_step]
#print axioms high_load_is_lowered

theorem inner_store_is_lowered (frame : Safety.Frame) (memory : Safety.Memory)
    (stack : List Safety.Value) :
    Safety.step body (.stfld innerField) 0 [] frame stack memory =
      Safety.step body (.setAggregateFieldAt 8 4) 0 [] frame stack memory := by
  simp only [cil_step]
#print axioms inner_store_is_lowered

theorem inner_load_is_lowered (frame : Safety.Frame) (memory : Safety.Memory)
    (stack : List Safety.Value) :
    Safety.step body (.ldfld innerField) 0 [] frame stack memory =
      Safety.step body (.aggregateFieldAt 8 4) 0 [] frame stack memory := by
  simp only [cil_step]
#print axioms inner_load_is_lowered

theorem inner_address_is_lowered (frame : Safety.Frame) (memory : Safety.Memory)
    (stack : List Safety.Value) :
    Safety.step body (.ldflda innerField) 0 [] frame stack memory =
      Safety.step body (.fieldAddress 8) 0 [] frame stack memory := by
  simp only [cil_step]
#print axioms inner_address_is_lowered

theorem high_address_is_lowered (frame : Safety.Frame) (memory : Safety.Memory)
    (stack : List Safety.Value) :
    Safety.step body (.ldflda highField) 0 [] frame stack memory =
      Safety.step body (.fieldAddress 4) 0 [] frame stack memory := by
  simp only [cil_step]
#print axioms high_address_is_lowered

private def lanes : TypeExpr := .aggregate "T::Lanes" 3
/-- A `Vector*<ulong>` of the given generic definition. -/
private def ulongVector (definition : String) : TypeExpr :=
  .apply (.constructor intrinsicsScope definition) (.atom runtimeScope "System.UInt64")

/-- `Lanes.wide`, the 32-byte vector at offset 0. -/
def wideField : FieldRef :=
  { owner := lanes, index := 0, type := ulongVector "System.Runtime.Intrinsics.Vector256`1",
    name := name!"wide" }
/-- `Lanes.narrow`, the 16-byte vector at offset 32. -/
def narrowField : FieldRef :=
  { owner := lanes, index := 1, type := ulongVector "System.Runtime.Intrinsics.Vector128`1",
    name := name!"narrow" }
/-- `Lanes.tag`, the `int32` at offset 48. -/
def tagField : FieldRef :=
  { owner := lanes, index := 2, type := .atom runtimeScope "System.Int32", name := name!"tag" }

cil_field_shape environment wideField
cil_field_shape environment narrowField
cil_field_shape environment tagField

/-- A `T::Lanes` value held as a byte snapshot, as a vector bitcast leaves it. -/
def lanesSnapshot : Safety.Value :=
  .scalar (.snapshot (.aggregate 64) (List.replicate 64 (0, true)))

-- A snapshot receiver yields its 32- and 16-byte vector fields, and faults on any other width.
theorem snapshot_vector_fields_load (frame : Safety.Frame) (memory : Safety.Memory) :
    (∃ value, Safety.step body (.ldfld wideField) 0 [] frame [lanesSnapshot] memory =
      .ok (.next (0 + 1) [.scalar value] frame memory)) ∧
    (∃ value, Safety.step body (.ldfld narrowField) 0 [] frame [lanesSnapshot] memory =
      .ok (.next (0 + 1) [.scalar value] frame memory)) := by
  simp only [cil_step]
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
#print axioms snapshot_vector_fields_load

theorem snapshot_word_field_faults (frame : Safety.Frame) (memory : Safety.Memory) :
    Safety.step body (.ldfld tagField) 0 [] frame [lanesSnapshot] memory =
      .error (.unsupported "Snapshot field width") := by
  simp only [cil_step]
  rfl
#print axioms snapshot_word_field_faults

-- A store through a readonly reference faults before any address is formed.
theorem readonly_store_unwritable (frame : Safety.Frame) (memory : Safety.Memory)
    (receiver : Safety.ManagedReference) :
    Safety.step body (.stfld highField) 0 [] frame
        [.scalar (.i32 7), .readOnlyReference receiver] memory =
      .error (.memory .unwritable receiver 4) := by
  simp only [cil_step]
  rfl
#print axioms readonly_store_unwritable

-- A struct value on the stack has no address, so `ldflda` of it faults.
theorem value_address_faults (frame : Safety.Frame) (memory : Safety.Memory)
    (bytes : List (BitVec 8)) :
    Safety.step body (.ldflda highField) 0 [] frame [.scalar (.aggregate bytes)] memory =
      .error (.unsupported "Not a memory instruction") := by
  simp only [cil_step]
  rfl
#print axioms value_address_faults

/-- `Node.lanes` written inline under another name, which no shape fact states. -/
def inlineLanes : FieldRef :=
  { owner := node, index := 1, name := name!"inline",
    type := .array (.apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1")
      (.atom runtimeScope "System.UInt64")) }

-- A closed body steps a field without a fact by evaluating its shape to the literal a fact would
-- state, so the stepped goal spells the vector element as a string literal.
theorem inline_lanes_load (frame : Safety.Frame) (memory : Safety.Memory)
    (receiver : Safety.ManagedReference) :
    ∃ outcome, Safety.step body (.ldfld inlineLanes) 0 [] frame [.object receiver] memory =
      outcome := by
  simp only [cil_step]
  guard_target =ₛ ∃ outcome, (do
      let address ← Safety.objectFieldAddress memory receiver node 8
      let value ← Safety.loadArraySlot memory address
        (.vector "System.Runtime.Intrinsics.Vector128`1<System.UInt64>" 16)
      pure (Safety.FrameAction.next (0 + 1) [value] frame memory)) = outcome
  exact ⟨_, rfl⟩
#print axioms inline_lanes_load

-- With shape facts required, the operand that has none is refused instead of evaluated.
/-- error: field inlineLanes of a closed body has no shape fact -/
#guard_msgs in
set_option cil.requireFieldShapeFacts true in
example (frame : Safety.Frame) (memory : Safety.Memory) (receiver : Safety.ManagedReference) :
    ∃ outcome, Safety.step body (.ldfld inlineLanes) 0 [] frame [.object receiver] memory =
      outcome := by
  simp only [cil_step]
  exact ⟨_, rfl⟩

-- The operand with a fact still steps by it.
set_option cil.requireFieldShapeFacts true in
theorem fact_lanes_load (frame : Safety.Frame) (memory : Safety.Memory)
    (receiver : Safety.ManagedReference) :
    ∃ outcome, Safety.step body (.ldfld lanesField) 0 [] frame [.object receiver] memory =
      outcome := by
  simp only [cil_step]
  exact ⟨_, rfl⟩
#print axioms fact_lanes_load

end Tests.FieldShape
