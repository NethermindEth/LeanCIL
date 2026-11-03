import CIL.Safety.AggregateFields

/-!
# Struct locals by field value

A struct whose fields hold the values `values` is `layout.encode values`: the zeroed struct
after each field stores its value, as `initobj` followed by one `stfld` per field leaves it. A
proof that tracks a struct local this way names its field values, such as `[.i32 count,
.i32 sum]`, instead of its bytes, offsets and widths. On a valid, disjoint layout a field store
replaces exactly that value (`AggregateLayout.setIn_encode`), and a field holding an int, word or
vector of exactly its width reads back as that value, by value (`step_fieldAt_encode`) or through
the struct's address (`fieldAt_encode_home`). A narrow field stores a truncated value, which
reads back zero or sign extended, so it has no exact read here and stays at the byte level of
`CIL.Safety.AggregateFields`.
-/

namespace CIL.Safety

/-- The number a field of `width` bytes holds after a store of `value`, or zero when no store
    of `value` into such a field succeeds. -/
def fieldNumber (width : Nat) (value : CIL.Value) : Nat :=
  (fieldStoreNumber width value).getD 0

/-- `bytes` after each of `fields` stores the value at its position in `values`, in order. -/
def encodeFields : List FieldLayout → List CIL.Value → List (BitVec 8) → List (BitVec 8)
  | field :: fields, value :: values, bytes =>
    encodeFields fields values (field.setIn bytes (fieldNumber field.width value))
  | _, _, bytes => bytes

/-- The bytes of a struct of `layout` whose fields hold `values` in field order, every other
    byte zero. -/
def _root_.CIL.AggregateLayout.encode (layout : AggregateLayout) (values : List CIL.Value) :
    List (BitVec 8) :=
  encodeFields layout.fields values (List.replicate layout.size 0)

/-- A value a field of `width` bytes stores and reads back unchanged: an int in 4 bytes, a word
    in 8 and a vector of exactly the field's width. -/
def FieldExact : Nat → CIL.Value → Prop
  | 4, .i32 _ | 8, .i64 _ | 16, .v128 _ | 32, .v256 _ => True
  | _, _ => False

/-- A stored field number fits its field, whatever the value. -/
theorem fieldNumber_lt (width : Nat) (value : CIL.Value) :
    fieldNumber width value < 256 ^ width := by
  unfold fieldNumber
  cases encoded : fieldStoreNumber width value with
  | none => exact Nat.pow_pos (by decide)
  | some number => exact fieldStoreNumber_lt encoded

/-- An exact field value is the value its stored number decodes to, signed or not. -/
theorem FieldExact.decoded {width : Nat} {value : CIL.Value} (exact : FieldExact width value)
    (signed : Bool) :
    (if signed then signedOfWidth width (fieldNumber width value)
      else numericOfWidth width (fieldNumber width value)) = value := by
  unfold FieldExact at exact
  split at exact <;> (try cases exact) <;>
    cases signed <;> simp [fieldNumber, fieldStoreNumber, signedOfWidth, numericOfWidth]

#print axioms fieldNumber_lt
#print axioms FieldExact.decoded

end CIL.Safety

namespace CIL
open Safety

/-- Two field stores to fields sharing no byte commute. -/
theorem FieldLayout.setIn_comm {field other : FieldLayout} {bytes : List (BitVec 8)}
    (apart : field.Apart other) (fieldWithin : field.offset + field.width ≤ bytes.length)
    (otherWithin : other.offset + other.width ≤ bytes.length) (number otherNumber : Nat) :
    field.setIn (other.setIn bytes otherNumber) number =
      other.setIn (field.setIn bytes number) otherNumber := by
  have fieldAfter := (FieldLayout.length_setIn otherWithin otherNumber).symm ▸ fieldWithin
  have otherAfter := (FieldLayout.length_setIn fieldWithin number).symm ▸ otherWithin
  apply List.ext_getElem?
  intro position
  rw [getElem?_setIn fieldAfter, getElem?_setIn otherWithin, getElem?_setIn otherAfter,
    getElem?_setIn fieldWithin]
  unfold Apart at apart
  by_cases inField : field.offset ≤ position ∧ position < field.offset + field.width
  · have outside : ¬ (other.offset ≤ position ∧ position < other.offset + other.width) := by
      omega
    simp only [inField, outside, and_self, ite_true, ite_false]
  · simp only [inField, ite_false]

/-- A second store to a field replaces the first. -/
theorem FieldLayout.setIn_setIn {field : FieldLayout} {bytes : List (BitVec 8)}
    (within : field.offset + field.width ≤ bytes.length) (first second : Nat) :
    field.setIn (field.setIn bytes first) second = field.setIn bytes second := by
  have after := (FieldLayout.length_setIn within first).symm ▸ within
  apply List.ext_getElem?
  intro position
  rw [getElem?_setIn after, getElem?_setIn within, getElem?_setIn within]
  split <;> rfl

#print axioms FieldLayout.setIn_comm
#print axioms FieldLayout.setIn_setIn

end CIL

namespace CIL.Safety

/-- Storing fields that lie inside the bytes keeps their length. -/
theorem length_encodeFields {fields : List FieldLayout} {values : List CIL.Value}
    {bytes : List (BitVec 8)}
    (within : ∀ field ∈ fields, field.offset + field.width ≤ bytes.length) :
    (encodeFields fields values bytes).length = bytes.length := by
  induction fields generalizing values bytes with
  | nil => rfl
  | cons field fields ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      have length := FieldLayout.length_setIn (within field (by simp))
        (fieldNumber field.width value)
      simp only [encodeFields]
      rw [ih fun other member => length ▸ within other (by simp [member]), length]

/-- Storing fields apart from `field` keeps the number `field` holds. -/
theorem numberIn_encodeFields_apart {field : FieldLayout} {fields : List FieldLayout}
    {values : List CIL.Value} {bytes : List (BitVec 8)}
    (within : ∀ other ∈ fields, other.offset + other.width ≤ bytes.length)
    (apart : ∀ other ∈ fields, other.Apart field) :
    field.numberIn (encodeFields fields values bytes) = field.numberIn bytes := by
  induction fields generalizing values bytes with
  | nil => rfl
  | cons other fields ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      have otherWithin := within other (by simp)
      have length := FieldLayout.length_setIn otherWithin (fieldNumber other.width value)
      simp only [encodeFields]
      rw [ih (fun next member => length ▸ within next (by simp [member]))
        fun next member => apart next (by simp [member])]
      exact FieldLayout.numberIn_setIn_apart otherWithin (apart other (by simp)) _

/-- Storing `field` over the stored fields, all apart from it, is storing it first. -/
theorem setIn_encodeFields_apart {field : FieldLayout} {fields : List FieldLayout}
    {values : List CIL.Value} {bytes : List (BitVec 8)}
    (fieldWithin : field.offset + field.width ≤ bytes.length)
    (within : ∀ other ∈ fields, other.offset + other.width ≤ bytes.length)
    (apart : ∀ other ∈ fields, field.Apart other) (number : Nat) :
    field.setIn (encodeFields fields values bytes) number =
      encodeFields fields values (field.setIn bytes number) := by
  induction fields generalizing values bytes with
  | nil => rfl
  | cons other fields ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      have otherWithin := within other (by simp)
      have length := FieldLayout.length_setIn otherWithin (fieldNumber other.width value)
      simp only [encodeFields]
      rw [ih (length ▸ fieldWithin)
        (fun next member => length ▸ within next (by simp [member]))
        fun next member => apart next (by simp [member]),
        FieldLayout.setIn_comm (apart other (by simp)) fieldWithin otherWithin]

/-- On fields sharing no byte, field `index` of the stored bytes holds the number of the value
    at `index`. -/
theorem numberIn_encodeFields {fields : List FieldLayout} {values : List CIL.Value}
    {bytes : List (BitVec 8)} (disjoint : fields.Pairwise FieldLayout.Apart)
    (within : ∀ field ∈ fields, field.offset + field.width ≤ bytes.length) {index : Nat}
    {field : FieldLayout} (found : fields[index]? = some field) {value : CIL.Value}
    (listed : values[index]? = some value) :
    field.numberIn (encodeFields fields values bytes) = fieldNumber field.width value := by
  induction fields generalizing values bytes index with
  | nil => simp at found
  | cons head fields ih =>
    cases values with
    | nil => simp at listed
    | cons first values =>
      have headWithin := within head (by simp)
      have length := FieldLayout.length_setIn headWithin (fieldNumber head.width first)
      have later : ∀ other ∈ fields, other.offset + other.width ≤
          (head.setIn bytes (fieldNumber head.width first)).length :=
        fun other member => length ▸ within other (by simp [member])
      simp only [encodeFields]
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found listed
        subst found listed
        rw [numberIn_encodeFields_apart later fun other member =>
          (List.pairwise_cons.1 disjoint).1 other member |>.symm,
          FieldLayout.numberIn_setIn headWithin, Nat.mod_eq_of_lt (fieldNumber_lt _ _)]
      | succ index =>
        exact ih (List.pairwise_cons.1 disjoint).2 later (by simpa using found)
          (by simpa using listed)

/-- On fields sharing no byte, storing field `index` over the stored bytes is storing the
    fields with that value replaced. -/
theorem setIn_encodeFields {fields : List FieldLayout} {values : List CIL.Value}
    {bytes : List (BitVec 8)} (disjoint : fields.Pairwise FieldLayout.Apart)
    (within : ∀ field ∈ fields, field.offset + field.width ≤ bytes.length) {index : Nat}
    {field : FieldLayout} (found : fields[index]? = some field) (listed : index < values.length)
    (value : CIL.Value) :
    field.setIn (encodeFields fields values bytes) (fieldNumber field.width value) =
      encodeFields fields (values.set index value) bytes := by
  induction fields generalizing values bytes index with
  | nil => simp at found
  | cons head fields ih =>
    cases values with
    | nil => simp at listed
    | cons first values =>
      have headWithin := within head (by simp)
      have length := FieldLayout.length_setIn headWithin (fieldNumber head.width first)
      have later : ∀ other ∈ fields, other.offset + other.width ≤
          (head.setIn bytes (fieldNumber head.width first)).length :=
        fun other member => length ▸ within other (by simp [member])
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        simp only [encodeFields, List.set_cons_zero]
        rw [setIn_encodeFields_apart (length ▸ headWithin) later
          fun other member => (List.pairwise_cons.1 disjoint).1 other member,
          FieldLayout.setIn_setIn headWithin]
      | succ index =>
        simp only [encodeFields, List.set_cons_succ]
        exact ih (List.pairwise_cons.1 disjoint).2 later (by simpa using found)
          (by simpa using listed)

#print axioms length_encodeFields
#print axioms numberIn_encodeFields_apart
#print axioms setIn_encodeFields_apart
#print axioms numberIn_encodeFields
#print axioms setIn_encodeFields

end CIL.Safety

namespace CIL
open Safety

/-- The bytes of a struct of a valid layout fill it. -/
theorem AggregateLayout.length_encode {layout : AggregateLayout} (valid : layout.Valid)
    (values : List CIL.Value) : (layout.encode values).length = layout.size := by
  unfold encode
  rw [length_encodeFields fun field member => by
    simpa using field_within_layout layout valid field member, List.length_replicate]

/-- Every field of a struct of a valid layout lies inside its bytes. -/
theorem AggregateLayout.within_encode {layout : AggregateLayout} (valid : layout.Valid)
    (values : List CIL.Value) :
    ∀ field ∈ layout.fields, field.offset + field.width ≤ (layout.encode values).length :=
  fun field member =>
    (length_encode valid values).symm ▸ field_within_layout layout valid field member

/-- Field `index` of a struct of a valid, disjoint layout holds the number of the value at
    `index`. -/
theorem AggregateLayout.numberIn_encode {layout : AggregateLayout} (valid : layout.Valid)
    (disjoint : layout.Disjoint) {values : List CIL.Value} {index : Nat} {field : FieldLayout}
    (found : layout.fields[index]? = some field) {value : CIL.Value}
    (listed : values[index]? = some value) :
    field.numberIn (layout.encode values) = fieldNumber field.width value :=
  numberIn_encodeFields disjoint (fun field member => by
    simpa using field_within_layout layout valid field member) found listed

/-- On a valid, disjoint layout, storing field `index` of a struct replaces the value at
    `index`. -/
theorem AggregateLayout.setIn_encode {layout : AggregateLayout} (valid : layout.Valid)
    (disjoint : layout.Disjoint) {values : List CIL.Value} {index : Nat} {field : FieldLayout}
    (found : layout.fields[index]? = some field) (listed : index < values.length)
    (value : CIL.Value) :
    field.setIn (layout.encode values) (fieldNumber field.width value) =
      layout.encode (values.set index value) :=
  setIn_encodeFields disjoint (fun field member => by
    simpa using field_within_layout layout valid field member) found listed value

#print axioms AggregateLayout.length_encode
#print axioms AggregateLayout.within_encode
#print axioms AggregateLayout.numberIn_encode
#print axioms AggregateLayout.setIn_encode

end CIL

namespace CIL.Safety

/-- A by-value `ldfld` of a field holding `number` in struct bytes that contain it pushes the
    value an exact field `value` with that number decodes to, signed or not. The step holds in
    any method and frame. -/
theorem step_fieldAt_value {bytes : List (BitVec 8)} {offset width : Nat} {value : CIL.Value}
    (within : offset + width ≤ bytes.length) (exact : FieldExact width value)
    (decoded : byteNumber ((bytes.drop offset).take width) = fieldNumber width value) :
    ∀ body pc args frame memory rest signed,
      step body (.fieldAt offset width signed) pc args frame (.scalar (.aggregate bytes) :: rest)
        memory = .ok (.next (pc + 1) (.scalar value :: rest) frame memory) := by
  intro body pc args frame memory rest signed
  have pushed := exact.decoded false
  unfold FieldExact at exact
  rw [step_fieldAt_eq]
  split at exact <;> (try cases exact) <;>
    simp_all [instructionStep, instruction, cil_guard, unspecifiedOperands, List.take, List.any,
      Value.hasUnspecified, numericOfWidth, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Nat.not_lt.2 within]

/-- A by-value `ldfld` of field `index` of a struct of a valid, disjoint layout whose fields hold
    `values` pushes the exact value at `index`. -/
theorem step_fieldAt_encode {layout : AggregateLayout} (valid : layout.Valid) (index : Nat)
    (values : List CIL.Value) {offset width : Nat} {aggregate : Bool}
    (found : layout.fields[index]? = some ⟨offset, width, aggregate⟩ := by rfl)
    {value : CIL.Value} (listed : values[index]? = some value := by rfl)
    (exact : FieldExact width value := by trivial) (disjoint : layout.Disjoint := by decide) :
    ∀ body pc args frame memory rest signed,
      step body (.fieldAt offset width signed) pc args frame
        (.scalar (.aggregate (layout.encode values)) :: rest) memory =
        .ok (.next (pc + 1) (.scalar value :: rest) frame memory) :=
  step_fieldAt_value (layout.within_encode valid values _ (List.mem_of_getElem? found)) exact
    (layout.numberIn_encode valid disjoint found listed)

#print axioms step_fieldAt_value
#print axioms step_fieldAt_encode

/-- `ldfld` of field `index` through the address of a struct home holding a struct of a valid,
    disjoint layout whose fields hold `values` pushes the exact value at `index`. The step holds
    in any method and frame. -/
theorem fieldAt_encode_home {memory : Memory} {home : Reference} {layout : AggregateLayout}
    (formed : memory.WellFormed) (valid : layout.Valid) (disjoint : layout.Disjoint)
    {values : List CIL.Value}
    (loaded : read memory home (layout.encode values).length 1 = .ok (layout.encode values))
    {index offset width : Nat} {aggregate : Bool}
    (found : layout.fields[index]? = some ⟨offset, width, aggregate⟩) {value : CIL.Value}
    (listed : values[index]? = some value) (exact : FieldExact width value) :
    ∀ body pc args frame rest signed,
      step body (.fieldAt offset width signed) pc args frame
        (.reference (.address home) :: rest) memory =
        .ok (.next (pc + 1) (.scalar value :: rest) frame memory) := by
  intro body pc args frame rest signed
  have within := layout.within_encode valid values _ (List.mem_of_getElem? found)
  have number := layout.numberIn_encode valid disjoint found listed
  have scalar : ScalarWidth width := by
    unfold FieldExact at exact
    split at exact <;> (try cases exact) <;> simp [ScalarWidth]
  rw [← exact.decoded signed]
  cases signed with
  | false =>
    simpa [number] using step_fieldAt_home (field := ⟨offset, width, aggregate⟩) formed loaded
      within scalar body pc args frame rest
  | true =>
    simpa [number] using step_fieldAt_signed_home (field := ⟨offset, width, aggregate⟩) formed
      loaded within scalar body pc args frame rest

#print axioms fieldAt_encode_home

end CIL.Safety
