import CIL.Layout
import CIL.Safety.ByteRoundTrip
import CIL.Safety.InstructionSteps
import CIL.Safety.WordMemory
import CIL.Safety.LocalSnapshots

/-!
# Struct field views

The bytes of a struct read as one number per field of its `AggregateLayout`, decoded little
endian as the checked field loads do, and `FieldLayout.setIn` replaces one field's bytes with
the encoding of a number, as a field store does. The field laws: a store reads back its own
field modulo the field's width and leaves every field apart from it unchanged, so on a layout
passing the decidable `AggregateLayout.Disjoint` check a store changes exactly one field value.
Overlapping explicit layouts fail that check and stay at the byte level.

The checked `initobj`, `stfld` and `ldfld` steps through a struct home's address are proved
against these laws, for int, word and 16- or 32-byte vector fields, for signed loads of 1- and
2-byte fields, and for nested struct fields, whose number is that of their bytes.
`LocalSnapshots.zero_aggregate`, `store_field`, `store_aggregate_field`, `load_field`,
`load_signed_field` and `load_aggregate_field` take them through a remembered aggregate local,
tracking its decoded field values and keeping every other local's snapshot, so struct and
numeric locals share one snapshot set. Every store reaches its snapshots through
`LocalSnapshots.write_field`.
-/

namespace CIL.Safety

/-- Bytes that are all zero decode to zero. -/
theorem byteNumber_replicate_zero (count : Nat) : byteNumber (List.replicate count 0) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ, byteNumber, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

#print axioms byteNumber_replicate_zero
end CIL.Safety

namespace CIL
open Safety

/-- The two fields share no byte. -/
def FieldLayout.Apart (field other : FieldLayout) : Prop :=
  field.offset + field.width ≤ other.offset ∨ other.offset + other.width ≤ field.offset

instance (field other : FieldLayout) : Decidable (field.Apart other) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- No two fields of the layout share a byte. Explicit layouts may overlap and then fail it. -/
def AggregateLayout.Disjoint (layout : AggregateLayout) : Prop :=
  layout.fields.Pairwise FieldLayout.Apart

instance (layout : AggregateLayout) : Decidable layout.Disjoint :=
  inferInstanceAs (Decidable (List.Pairwise _ _))

/-- Distinct fields of a disjoint layout share no byte. -/
theorem AggregateLayout.Disjoint.apart {layout : AggregateLayout} (disjoint : layout.Disjoint)
    {index other : Nat} {field neighbour : FieldLayout}
    (found : layout.fields[index]? = some field) (beside : layout.fields[other]? = some neighbour)
    (distinct : index ≠ other) : field.Apart neighbour := by
  obtain ⟨indexBound, rfl⟩ := List.getElem?_eq_some_iff.mp found
  obtain ⟨otherBound, rfl⟩ := List.getElem?_eq_some_iff.mp beside
  have pairs := List.pairwise_iff_getElem.mp disjoint
  rcases Nat.lt_or_gt_of_ne distinct with before | after
  · exact pairs _ _ indexBound otherBound before
  · exact (pairs _ _ otherBound indexBound after).symm

/-- The widths a valid layout gives a scalar field are scalar load widths. -/
theorem AggregateLayout.Valid.scalar {layout : AggregateLayout} (valid : layout.Valid)
    {offset width : Nat} (member : (⟨offset, width, false⟩ : FieldLayout) ∈ layout.fields) :
    ScalarWidth width := by
  have shape := (valid.2.2 _ member).1
  simp at shape
  unfold ScalarWidth
  omega

/-- Every field of a valid layout is at least one byte wide. -/
theorem AggregateLayout.Valid.positive {layout : AggregateLayout} (valid : layout.Valid)
    {field : FieldLayout} (member : field ∈ layout.fields) : 0 < field.width := by
  have shape := (valid.2.2 _ member).1
  split at shape
  · exact shape
  · simp at shape; omega

#print axioms AggregateLayout.Valid.scalar
#print axioms AggregateLayout.Valid.positive

/-- The bytes `field` occupies in `bytes`. -/
def FieldLayout.bytesIn (field : FieldLayout) (bytes : List (BitVec 8)) : List (BitVec 8) :=
  (bytes.drop field.offset).take field.width

/-- The number `field` holds in `bytes`, decoded little endian. -/
def FieldLayout.numberIn (field : FieldLayout) (bytes : List (BitVec 8)) : Nat :=
  byteNumber (field.bytesIn bytes)

/-- `bytes` with `field` holding the `field.width`-byte encoding of `number`. -/
def FieldLayout.setIn (field : FieldLayout) (bytes : List (BitVec 8)) (number : Nat) :
    List (BitVec 8) :=
  bytes.take field.offset ++ numberBytes number field.width ++
    bytes.drop (field.offset + field.width)

/-- The number each field of the layout holds in `bytes`, in field order. -/
def AggregateLayout.values (layout : AggregateLayout) (bytes : List (BitVec 8)) : List Nat :=
  layout.fields.map (·.numberIn bytes)

/-- A field store keeps the length of bytes that contain the field. -/
theorem FieldLayout.length_setIn {field : FieldLayout} {bytes : List (BitVec 8)}
    (within : field.offset + field.width ≤ bytes.length) (number : Nat) :
    (field.setIn bytes number).length = bytes.length := by
  simp only [setIn, List.length_append, List.length_take, List.length_drop, numberBytes_length]
  omega

/-- Each byte of a field store: the encoding inside the field, the old byte outside it. -/
theorem FieldLayout.getElem?_setIn {field : FieldLayout} {bytes : List (BitVec 8)}
    (within : field.offset + field.width ≤ bytes.length) (number position : Nat) :
    (field.setIn bytes number)[position]? =
      if field.offset ≤ position ∧ position < field.offset + field.width then
        (numberBytes number field.width)[position - field.offset]?
      else bytes[position]? := by
  have prefixLength : (bytes.take field.offset).length = field.offset := by
    simp only [List.length_take]; omega
  unfold setIn
  rw [List.append_assoc, List.getElem?_append, prefixLength, List.getElem?_append,
    numberBytes_length, List.getElem?_drop]
  by_cases before : position < field.offset
  · simp only [before, ite_true, List.getElem?_take_of_lt before]
    rw [ite_eq_right_iff.mpr (fun inside => absurd inside.1 (by omega))]
  · simp only [before, ite_false]
    by_cases inside : position - field.offset < field.width
    · simp only [inside, ite_true]
      rw [ite_eq_left_iff.mpr (fun outside => absurd ⟨by omega, by omega⟩ outside)]
    · simp only [inside, ite_false]
      rw [ite_eq_right_iff.mpr (fun within => absurd within.2 (by omega))]
      congr 1
      omega

/-- A field store reads back as the encoding it wrote. -/
theorem FieldLayout.bytesIn_setIn {field : FieldLayout} {bytes : List (BitVec 8)}
    (within : field.offset + field.width ≤ bytes.length) (number : Nat) :
    field.bytesIn (field.setIn bytes number) = numberBytes number field.width := by
  apply List.ext_getElem?
  intro position
  simp only [bytesIn, List.getElem?_take, List.getElem?_drop, getElem?_setIn within]
  simp only [Nat.add_sub_cancel_left]
  by_cases inside : position < field.width
  · simp only [inside, ite_true, show field.offset ≤ field.offset + position by omega,
      show field.offset + position < field.offset + field.width by omega, and_self]
  · simp only [inside, ite_false]
    rw [eq_comm, List.getElem?_eq_none_iff, numberBytes_length]
    omega

/-- A field store reads back its own number modulo the field's width. -/
theorem FieldLayout.numberIn_setIn {field : FieldLayout} {bytes : List (BitVec 8)}
    (within : field.offset + field.width ≤ bytes.length) (number : Nat) :
    field.numberIn (field.setIn bytes number) = number % 256 ^ field.width := by
  rw [numberIn, bytesIn_setIn within, byteNumber_numberBytes]

/-- A field store leaves every field apart from it unchanged, wherever that field lies. -/
theorem FieldLayout.bytesIn_setIn_apart {field other : FieldLayout} {bytes : List (BitVec 8)}
    (within : field.offset + field.width ≤ bytes.length) (apart : field.Apart other)
    (number : Nat) : other.bytesIn (field.setIn bytes number) = other.bytesIn bytes := by
  apply List.ext_getElem?
  intro position
  simp only [bytesIn, List.getElem?_take, List.getElem?_drop, getElem?_setIn within]
  by_cases inside : position < other.width
  · have outside : ¬ (field.offset ≤ other.offset + position ∧
        other.offset + position < field.offset + field.width) := by
      unfold Apart at apart; omega
    simp only [inside, ite_true, outside, ite_false]
  · simp only [inside, ite_false]

/-- A field store changes only the stored field's number. -/
theorem FieldLayout.numberIn_setIn_apart {field other : FieldLayout} {bytes : List (BitVec 8)}
    (within : field.offset + field.width ≤ bytes.length) (apart : field.Apart other)
    (number : Nat) : other.numberIn (field.setIn bytes number) = other.numberIn bytes := by
  rw [numberIn, bytesIn_setIn_apart within apart]
  rfl

/-- On a disjoint layout, storing a field of struct bytes replaces exactly that field's value,
    by the stored number modulo the field's width. -/
theorem AggregateLayout.values_setIn {layout : AggregateLayout} (valid : layout.Valid)
    (disjoint : layout.Disjoint) {bytes : List (BitVec 8)} (sized : bytes.length = layout.size)
    {index : Nat} {field : FieldLayout} (found : layout.fields[index]? = some field)
    (number : Nat) :
    layout.values (field.setIn bytes number) =
      (layout.values bytes).set index (number % 256 ^ field.width) := by
  have member := List.mem_of_getElem? found
  have within : field.offset + field.width ≤ bytes.length :=
    sized ▸ field_within_layout layout valid field member
  apply List.ext_getElem?
  intro other
  simp only [values, List.getElem?_set, List.getElem?_map, List.length_map]
  by_cases same : index = other
  · subst other
    obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp found
    simp [bound, FieldLayout.numberIn_setIn within]
  · simp only [same, ite_false]
    cases beside : layout.fields[other]? with
    | none => rfl
    | some neighbour =>
      simp [FieldLayout.numberIn_setIn_apart within (disjoint.apart found beside same)]

/-- Every field of zeroed bytes holds zero. -/
theorem AggregateLayout.values_zero (layout : AggregateLayout) (size : Nat) :
    layout.values (List.replicate size 0) = layout.fields.map fun _ => 0 := by
  simp only [values, FieldLayout.numberIn, FieldLayout.bytesIn, List.drop_replicate,
    List.take_replicate, byteNumber_replicate_zero]

#print axioms AggregateLayout.Disjoint.apart
#print axioms FieldLayout.length_setIn
#print axioms FieldLayout.getElem?_setIn
#print axioms FieldLayout.bytesIn_setIn
#print axioms FieldLayout.numberIn_setIn
#print axioms FieldLayout.bytesIn_setIn_apart
#print axioms FieldLayout.numberIn_setIn_apart
#print axioms AggregateLayout.values_setIn
#print axioms AggregateLayout.values_zero

end CIL

namespace CIL.Safety

/-- Reducing a number modulo `256^width` keeps its `width`-byte encoding. -/
theorem numberBytes_mod (number width : Nat) :
    numberBytes (number % 256 ^ width) width = numberBytes number width := by
  conv => rhs; rw [← numberBytes_byteNumber (numberBytes number width), numberBytes_length]
  rw [byteNumber_numberBytes]

/-- The number a checked `stfld` of `value` writes in `width` bytes, reduced to that width:
    an int or word at 1, 2, 4 or 8 bytes, or a 16- or 32-byte vector. `none` where the store
    faults or the value is a snapshot. -/
def fieldStoreNumber : Nat → CIL.Value → Option Nat
  | 1, .i32 bits => some (bits.toNat % 256)
  | 2, .i32 bits => some (bits.toNat % 256 ^ 2)
  | 4, .i32 bits => some bits.toNat
  | 8, .i64 bits => some bits.toNat
  | 16, .v128 bits => some bits.toNat
  | 32, .v256 bits => some bits.toNat
  | _, _ => none

/-- A stored field number fits its field. -/
theorem fieldStoreNumber_lt {width number : Nat} {value : CIL.Value}
    (encoded : fieldStoreNumber width value = some number) : number < 256 ^ width := by
  unfold fieldStoreNumber at encoded
  split at encoded <;> cases encoded
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · rename_i bits; exact bits.isLt
  · rename_i bits; exact bits.isLt
  · rename_i bits; exact bits.isLt
  · rename_i bits; exact bits.isLt

/-- A snapshot store of known bytes is the plain write of those bytes. -/
theorem writeSnapshot_initialized (memory : Memory) (reference : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat) :
    writeSnapshot memory reference (bytes.map fun byte => (byte, true)) alignment =
      write memory reference bytes alignment := by
  have bits : (bytes.map fun byte => (byte, true)).map Prod.fst = bytes := by
    simp [List.map_map, Function.comp_def]
  unfold writeSnapshot
  rw [bits]
  unfold write
  cases access memory reference bytes.length alignment true with
  | error => rfl
  | ok =>
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, List.getElem?_map]
    congr 2
    funext allocation position
    split <;> try rfl
    cases bytes[position - reference.offset]? <;> rfl

/-- What a signed `loadValue` of `width` bytes returns for the decoded `number`: a 1- or 2-byte
    load sign extends to i32, and a wider one loads as unsigned. -/
def signedOfWidth (width number : Nat) : CIL.Value :=
  match width with
  | 1 => .i32 ((BitVec.ofNat 8 number).signExtend 32)
  | 2 => .i32 ((BitVec.ofNat 16 number).signExtend 32)
  | _ => numericOfWidth width number

/-- An initialized signed read at any scalar width decodes its bytes, sign extending at 1 and 2
    bytes. -/
theorem loadValue_signed_of_read {memory : Memory} {reference : Reference} {width : Nat}
    {bytes : List (BitVec 8)}
    (scalar : ScalarWidth width) (loaded : read memory reference width 1 = .ok bytes) :
    loadValue memory (.address reference) width true =
      .ok (signedOfWidth width (byteNumber bytes)) := by
  rcases scalar with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [loadValue, dereference, loaded, checkedAt, Except.mapError, signedOfWidth,
      numericOfWidth, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Closes a step equation through its generic `instructionStep` equation, as the stepping
    equations in `InstructionSteps` are closed. -/
local macro "field_step_proof " generic:ident : tactic => `(tactic| (
  rw [$generic:ident]
  simp -bitVecOfNat only [instructionStep, instruction, cil_guard, unspecifiedOperands, List.take, List.any,
    Value.hasUnspecified, Bool.or_false, Bool.false_eq_true, ite_false, bind_assoc, pure_bind,
    referenceAt, valueSnapshot, ite_true, writeSnapshot_initialized]
  all_goals first | rfl | (split <;> (try simp -bitVecOfNat only [bind_assoc, pure_bind]) <;> rfl)))

/-- A 16-byte vector field store writes the vector's bytes at the field address. -/
theorem step_setFieldAt_v128_eq (body : CIL.Method) (pc : Nat) (args : List Value)
    (frame : Frame) (memory : Memory) (offset : Nat) (bits : BitVec 128) (reference : Reference)
    (rest : List Value) :
    step body (.setFieldAt offset 16) pc args frame
      (.scalar (.v128 bits) :: .reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let stored ← checkedAt (.address address) 16
        (write memory address (numberBytes bits.toNat 16) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored := by
  field_step_proof step_setFieldAt_eq

/-- A 32-byte vector field store writes the vector's bytes at the field address. -/
theorem step_setFieldAt_v256_eq (body : CIL.Method) (pc : Nat) (args : List Value)
    (frame : Frame) (memory : Memory) (offset : Nat) (bits : BitVec 256) (reference : Reference)
    (rest : List Value) :
    step body (.setFieldAt offset 32) pc args frame
      (.scalar (.v256 bits) :: .reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let stored ← checkedAt (.address address) 32
        (write memory address (numberBytes bits.toNat 32) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored := by
  field_step_proof step_setFieldAt_eq

/-- A nested struct field store writes the struct's bytes at the field address once their
    count matches the field's. -/
theorem step_setAggregateFieldAt_reference_eq (body : CIL.Method) (pc : Nat)
    (args : List Value) (frame : Frame) (memory : Memory) (offset size : Nat)
    (bytes : List (BitVec 8)) (reference : Reference) (rest : List Value) :
    step body (.setAggregateFieldAt offset size) pc args frame
      (.scalar (.aggregate bytes) :: .reference (.address reference) :: rest) memory =
      if bytes.length != size then .error .invalidState else do
        let address ← checkedAt (.address reference) 0
          (add memory reference 1 (BitVec.ofNat 64 offset))
        let stored ← checkedAt (.address address) size
          (write memory address bytes ordinaryAccessAlignment)
        return .next (pc + 1) rest frame stored := by
  field_step_proof step_setAggregateFieldAt_eq

/-- A nested struct field load reads the field's bytes at the field address. -/
theorem step_aggregateFieldAt_reference_eq (body : CIL.Method) (pc : Nat) (args : List Value)
    (frame : Frame) (memory : Memory) (offset size : Nat) (reference : Reference)
    (rest : List Value) :
    step body (.aggregateFieldAt offset size) pc args frame
      (.reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let bytes ← checkedAt (.address address) size
        (read memory address size ordinaryAccessAlignment)
      return .next (pc + 1) (.scalar (.aggregate bytes) :: rest) frame memory := by
  field_step_proof step_aggregateFieldAt_eq

/-- A field store into readable struct bytes leaves them reading as the stored field bytes. -/
theorem read_after_field_write {memory after : Memory} {home : Reference}
    {bytes : List (BitVec 8)} {field : FieldLayout} {number : Nat}
    (loaded : read memory home bytes.length 1 = .ok bytes)
    (within : field.offset + field.width ≤ bytes.length)
    (written : write memory { home with offset := home.offset + field.offset }
      (numberBytes number field.width) 1 = .ok after) :
    read after home bytes.length 1 = .ok (field.setIn bytes number) := by
  obtain ⟨allocation, ready⟩ := access_requirements (read_access loaded)
  rw [read_snapshot (ready.after_write written) fun position bound =>
    write_preserves_initialization _ _ _ _ _ _ _ written
      (read_requires_initialization _ _ _ _ _ loaded position (List.mem_range.mpr bound))]
  have snapshot := read_result_snapshot loaded
  congr 1
  apply List.ext_getElem?
  intro position
  rw [FieldLayout.getElem?_setIn within, List.getElem?_map]
  by_cases bound : position < bytes.length
  · rw [List.getElem?_range bound, Option.map_some]
    by_cases inside : field.offset ≤ position ∧ position < field.offset + field.width
    · have offset : home.offset + position =
          home.offset + field.offset + (position - field.offset) := by omega
      have cell := write_initializes _ _ _ _ _ (position - field.offset) written
        (by rw [numberBytes_length]; omega)
      rw [ite_eq_left inside, offset, cell, List.getElem?_eq_getElem]
    · have cell := write_outside _ _ _ _ _ home.allocation (home.offset + position) written
        (by simp only [numberBytes_length]; omega)
      rw [ite_eq_right inside, cell, snapshot]
      simp [bound]
  · rw [ite_eq_right (by omega), List.getElem?_eq_none_iff.mpr (by simpa using bound),
      List.getElem?_eq_none_iff.mpr (by omega)]
    rfl

/-- A field address inside readable struct bytes forms exactly at the field's offset. -/
theorem field_address {memory : Memory} {home : Reference} {length offset width : Nat}
    {writing : Bool} (formed : memory.WellFormed)
    (ready : access memory home length 1 writing = .ok ()) (positive : 0 < width)
    (within : offset + width ≤ length) :
    add memory home 1 (BitVec.ofNat 64 offset) =
      .ok { home with offset := home.offset + offset } := by
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  simpa using requirements.add_slice formed 1 offset width positive (by simpa using within)

/-- `stfld` into a struct home readable as `bytes` writes only the field's bytes, after which the
    home reads as `bytes` with that field stored. The step holds in any method and frame. -/
theorem step_setFieldAt_home {memory : Memory} {home : Reference} {bytes : List (BitVec 8)}
    {field : FieldLayout} (formed : memory.WellFormed)
    (loaded : read memory home bytes.length 1 = .ok bytes)
    (writable : access memory home bytes.length 1 true = .ok ())
    (within : field.offset + field.width ≤ bytes.length) {value : CIL.Value} {number : Nat}
    (encoded : fieldStoreNumber field.width value = some number) :
    ∃ after,
      (∀ body pc args frame rest,
        step body (.setFieldAt field.offset field.width) pc args frame
          (.scalar value :: .reference (.address home) :: rest) memory =
          .ok (.next (pc + 1) rest frame after)) ∧
      write memory { home with offset := home.offset + field.offset }
        (numberBytes number field.width) 1 = .ok after ∧
      read after home bytes.length 1 = .ok (field.setIn bytes number) := by
  have positive : 0 < field.width := by
    unfold fieldStoreNumber at encoded
    split at encoded <;> (cases encoded <;> omega)
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have slice := ready.slice formed field.offset field.width positive within
  obtain ⟨after, written⟩ := write_succeeds (bytes := numberBytes number field.width)
    (alignment := 1) (by simpa only [numberBytes_length] using slice.access)
  have address := field_address formed writable positive within
  refine ⟨after, ?_, written, read_after_field_write loaded within written⟩
  intro body pc args frame rest
  unfold fieldStoreNumber at encoded
  split at encoded <;> cases encoded <;> rename_i sized <;>
    simp only [sized] at written address ⊢
  all_goals first
    | rw [step_setFieldAt_i32_1_eq, ← numberBytes_mod _ 1]
    | rw [step_setFieldAt_i32_2_eq, ← numberBytes_mod _ 2]
    | rw [step_setFieldAt_i32_4_eq]
    | rw [step_setFieldAt_i64_eq]
    | rw [step_setFieldAt_v128_eq]
    | rw [step_setFieldAt_v256_eq]
  all_goals simp [address, written, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- A nested struct store of `fieldBytes` into a struct home readable as `bytes` writes only
    the field's bytes, after which the home reads as `bytes` with that field stored. The step
    holds in any method and frame. -/
theorem step_setAggregateFieldAt_home {memory : Memory} {home : Reference}
    {bytes : List (BitVec 8)} {field : FieldLayout} (formed : memory.WellFormed)
    (loaded : read memory home bytes.length 1 = .ok bytes)
    (writable : access memory home bytes.length 1 true = .ok ())
    (within : field.offset + field.width ≤ bytes.length) (positive : 0 < field.width)
    {fieldBytes : List (BitVec 8)} (fieldSized : fieldBytes.length = field.width) :
    ∃ after,
      (∀ body pc args frame rest,
        step body (.setAggregateFieldAt field.offset field.width) pc args frame
          (.scalar (.aggregate fieldBytes) :: .reference (.address home) :: rest) memory =
          .ok (.next (pc + 1) rest frame after)) ∧
      write memory { home with offset := home.offset + field.offset } fieldBytes 1 =
        .ok after ∧
      read after home bytes.length 1 = .ok (field.setIn bytes (byteNumber fieldBytes)) := by
  have encoding : numberBytes (byteNumber fieldBytes) field.width = fieldBytes := by
    rw [← fieldSized, numberBytes_byteNumber]
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have slice := ready.slice formed field.offset field.width positive within
  obtain ⟨after, written⟩ := write_succeeds (bytes := fieldBytes) (alignment := 1)
    (by simpa only [fieldSized] using slice.access)
  have address := field_address formed writable positive within
  refine ⟨after, ?_, written,
    read_after_field_write loaded within (by rw [encoding]; exact written)⟩
  intro body pc args frame rest
  rw [step_setAggregateFieldAt_reference_eq]
  simp [fieldSized, address, written, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

#print axioms writeSnapshot_initialized
#print axioms loadValue_signed_of_read
#print axioms step_setFieldAt_v128_eq
#print axioms step_setFieldAt_v256_eq
#print axioms step_setAggregateFieldAt_reference_eq
#print axioms step_aggregateFieldAt_reference_eq
#print axioms field_address
#print axioms step_setFieldAt_home
#print axioms step_setAggregateFieldAt_home
/-- `ldfld` through the address of a struct home readable as `bytes` pushes the field's number
    at the field's width and changes nothing. The step holds in any method and frame. -/
theorem step_fieldAt_home {memory : Memory} {home : Reference} {bytes : List (BitVec 8)}
    {field : FieldLayout} (formed : memory.WellFormed)
    (loaded : read memory home bytes.length 1 = .ok bytes)
    (within : field.offset + field.width ≤ bytes.length) (scalar : ScalarWidth field.width) :
    ∀ body pc args frame rest,
      step body (.fieldAt field.offset field.width false) pc args frame
        (.reference (.address home) :: rest) memory =
        .ok (.next (pc + 1) (.scalar (numericOfWidth field.width (field.numberIn bytes)) :: rest)
          frame memory) := by
  intro body pc args frame rest
  have positive : 0 < field.width := by rcases scalar with h | h | h | h | h | h | h <;> omega
  have address := field_address formed (read_access loaded) positive within
  have slice := read_slice_bytes formed loaded field.offset field.width positive within
  rw [step_fieldAt_reference_eq]
  simp [address, loadValue_of_read scalar slice, FieldLayout.numberIn, FieldLayout.bytesIn,
    checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A signed `ldfld` through the address of a struct home readable as `bytes` pushes the
    field's number sign extended from a 1- or 2-byte field, and changes nothing. The step holds
    in any method and frame. -/
theorem step_fieldAt_signed_home {memory : Memory} {home : Reference}
    {bytes : List (BitVec 8)} {field : FieldLayout} (formed : memory.WellFormed)
    (loaded : read memory home bytes.length 1 = .ok bytes)
    (within : field.offset + field.width ≤ bytes.length) (scalar : ScalarWidth field.width) :
    ∀ body pc args frame rest,
      step body (.fieldAt field.offset field.width true) pc args frame
        (.reference (.address home) :: rest) memory =
        .ok (.next (pc + 1) (.scalar (signedOfWidth field.width (field.numberIn bytes)) :: rest)
          frame memory) := by
  intro body pc args frame rest
  have positive : 0 < field.width := by rcases scalar with h | h | h | h | h | h | h <;> omega
  have address := field_address formed (read_access loaded) positive within
  have slice := read_slice_bytes formed loaded field.offset field.width positive within
  rw [step_fieldAt_reference_eq]
  simp [address, loadValue_signed_of_read scalar slice, FieldLayout.numberIn,
    FieldLayout.bytesIn, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
    Except.pure]

/-- A nested struct load through the address of a struct home readable as `bytes` pushes the
    field's bytes and changes nothing. The step holds in any method and frame. -/
theorem step_aggregateFieldAt_home {memory : Memory} {home : Reference}
    {bytes : List (BitVec 8)} {field : FieldLayout} (formed : memory.WellFormed)
    (loaded : read memory home bytes.length 1 = .ok bytes)
    (within : field.offset + field.width ≤ bytes.length) (positive : 0 < field.width) :
    ∀ body pc args frame rest,
      step body (.aggregateFieldAt field.offset field.width) pc args frame
        (.reference (.address home) :: rest) memory =
        .ok (.next (pc + 1) (.scalar (.aggregate (field.bytesIn bytes)) :: rest) frame
          memory) := by
  intro body pc args frame rest
  have address := field_address formed (read_access loaded) positive within
  have slice := read_slice_bytes formed loaded field.offset field.width positive within
  rw [step_aggregateFieldAt_reference_eq]
  simp [address, slice, FieldLayout.bytesIn, checkedAt, Except.mapError, Bind.bind,
    Except.bind, Pure.pure, Except.pure]

/-- `initobj` on a writable home zeroes its `size` bytes, which then read back. The step holds
    in any method and frame. -/
theorem step_initAggregate_home {memory : Memory} {home : Reference} {size : Nat}
    (writable : access memory home size 1 true = .ok ()) :
    ∃ after,
      (∀ body pc args frame rest,
        step body (.initAggregate size) pc args frame (.reference (.address home) :: rest)
          memory = .ok (.next (pc + 1) rest frame after)) ∧
      write memory home (List.replicate size 0) 1 = .ok after ∧
      read after home size 1 = .ok (List.replicate size 0) := by
  obtain ⟨after, written⟩ := write_succeeds (bytes := List.replicate size 0) (alignment := 1)
    (by simpa using writable)
  refine ⟨after, ?_, written, by simpa using write_readback _ _ _ _ _ written⟩
  intro body pc args frame rest
  rw [step_initAggregate_reference_eq]
  simp only [referenceAt, ordinaryAccessAlignment, written, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_fieldAt_home
#print axioms step_fieldAt_signed_home
#print axioms step_aggregateFieldAt_home
#print axioms step_initAggregate_home

/-- A remembered aggregate local reads as exactly its remembered bytes, which fill its home. -/
theorem LocalSnapshots.aggregate {memory : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    {index : Nat} {size : Fin (2^64)} {home : Reference} {bytes : List (BitVec 8)}
    (slot : slots[index]? = some (.bytes (.aggregate size) home))
    (specified : known index = some (.aggregate bytes)) :
    bytes.length = size ∧ read memory home bytes.length 1 = .ok bytes := by
  obtain ⟨kind, stored, stored', number, found, fits, result, loaded⟩ :=
    snapshots index _ specified
  rw [slot] at found
  cases found
  have same : stored' = .aggregate bytes := by
    cases stored' <;> simp_all [localResult]
  subst same
  have length : bytes.length = size := by
    by_cases sized : bytes.length = size
    · exact sized
    · simp [localNumber, CIL.Value.hasUnspecified, sized] at fits
  have decoded : number = byteNumber bytes := by
    simp [localNumber, CIL.Value.hasUnspecified, length] at fits
    exact fits.symm
  refine ⟨length, ?_⟩
  rw [length]
  simpa [localWidth, decoded, ← length, numberBytes_byteNumber] using loaded

/-- `initobj` through the address of an aggregate local's writable home remembers it as zeros
    and keeps every other snapshot; no earlier value of the local is needed. The home stays
    writable, its address forms, and the write equation states the exact footprint. -/
theorem LocalSnapshots.zero_aggregate {entered memory : Memory} {boundary : Nat} {kinds slots}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    (homes : WritableHomes entered boundary kinds slots) (formed : memory.WellFormed)
    {index width : Nat} {bounded : width < 2^64} {home : Reference}
    (slot : slots[index]? = some (.bytes (.aggregate ⟨width, bounded⟩) home))
    (writable : access memory home width 1 true = .ok ()) :
    ∃ after,
      (∀ body pc args frame rest,
        step body (.initAggregate width) pc args frame (.reference (.address home) :: rest)
          memory = .ok (.next (pc + 1) rest frame after)) ∧
      LocalSnapshots after slots
        (rememberLocal known index (.aggregate (List.replicate width 0))) ∧
      after.WellFormed ∧ MemoryBelow boundary memory after ∧
      access after home width 1 true = .ok () ∧ form after home = .ok home ∧
      write memory home (List.replicate width 0) 1 = .ok after := by
  let size : Fin (2^64) := ⟨width, bounded⟩
  obtain ⟨after, stepped, written, _⟩ := step_initAggregate_home writable
  obtain ⟨_, ready⟩ := access_requirements writable
  have encoded : localNumber (.aggregate size) (.aggregate (List.replicate size 0)) =
      .ok (byteNumber (List.replicate size 0)) := by
    simp [localNumber, CIL.Value.hasUnspecified]
  have zeros : write memory home (numberBytes (byteNumber (List.replicate size 0))
      (localWidth (.aggregate size))) 1 = .ok after := by
    have encoding := numberBytes_byteNumber (List.replicate size.val 0)
    rw [List.length_replicate] at encoding
    rwa [localWidth, encoding]
  have kept := (ready.after_write written).access
  exact ⟨after, stepped,
    snapshots.after_write homes index (.aggregate size) home _ _ encoded slot zeros,
    write_preserves_wellFormed _ _ _ _ _ formed written,
    write_preserves_memory_below _ _ _ _ _ _ (homes.home_bound index _ home slot) written,
    kept, access_reference_valid _ _ _ _ _ kept, written⟩

/-- A write of a `width`-byte number into field `fieldIndex` of a remembered aggregate local of a
    valid, disjoint `layout` whose bytes decode to `values`: the local is remembered with that
    field stored, its fields then decode to `values` with the number at `fieldIndex`, and every
    other snapshot is kept. The home stays writable and its address forms. Each field store
    instruction reaches its snapshots through this write. -/
theorem LocalSnapshots.write_field {entered memory after : Memory} {boundary : Nat} {kinds slots}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    (homes : WritableHomes entered boundary kinds slots) (formed : memory.WellFormed)
    {index : Nat} {size : Fin (2^64)} {home : Reference} {bytes : List (BitVec 8)}
    (slot : slots[index]? = some (.bytes (.aggregate size) home))
    (specified : known index = some (.aggregate bytes))
    (writable : access memory home (localWidth (.aggregate size)) 1 true = .ok ())
    {layout : AggregateLayout} (valid : layout.Valid) (disjoint : layout.Disjoint)
    (sized : layout.size = size) {values : List Nat} (decoded : layout.values bytes = values)
    {fieldIndex offset width : Nat} {aggregate : Bool}
    (found : layout.fields[fieldIndex]? = some ⟨offset, width, aggregate⟩) {number : Nat}
    (fits : number < 256 ^ width)
    (written : write memory { home with offset := home.offset + offset }
      (numberBytes number width) 1 = .ok after) :
    LocalSnapshots after slots (rememberLocal known index
      (.aggregate ((⟨offset, width, aggregate⟩ : FieldLayout).setIn bytes number))) ∧
    after.WellFormed ∧ MemoryBelow boundary memory after ∧
    access after home (localWidth (.aggregate size)) 1 true = .ok () ∧
    form after home = .ok home ∧
    layout.values ((⟨offset, width, aggregate⟩ : FieldLayout).setIn bytes number) =
      values.set fieldIndex number := by
  obtain ⟨length, loaded⟩ := snapshots.aggregate slot specified
  have within : offset + width ≤ bytes.length :=
    (length.trans sized.symm) ▸ field_within_layout layout valid _ (List.mem_of_getElem? found)
  have stored := read_after_field_write (field := ⟨offset, width, aggregate⟩) loaded within written
  obtain ⟨_, ready⟩ := access_requirements writable
  have kept := (ready.after_write written).access
  have changed : layout.values ((⟨offset, width, aggregate⟩ : FieldLayout).setIn bytes number) =
      values.set fieldIndex number := by
    rw [layout.values_setIn valid disjoint (length.trans sized.symm) found, decoded,
      Nat.mod_eq_of_lt fits]
  refine ⟨?_, write_preserves_wellFormed _ _ _ _ _ formed written,
    write_preserves_memory_below _ _ _ _ _ _ (by exact homes.home_bound index _ home slot)
      written, kept, access_reference_valid _ _ _ _ _ kept, changed⟩
  have storedLength := FieldLayout.length_setIn (field := ⟨offset, width, aggregate⟩) within number
  intro other remembered specifiedOther
  by_cases same : other = index
  · subst other
    have result : CIL.Value.aggregate
        ((⟨offset, width, aggregate⟩ : FieldLayout).setIn bytes number) = remembered := by
      simpa [rememberLocal] using specifiedOther
    refine ⟨.aggregate size, home, _,
      byteNumber ((⟨offset, width, aggregate⟩ : FieldLayout).setIn bytes number), slot,
      by simp [localNumber, CIL.Value.hasUnspecified, storedLength, length], result, ?_⟩
    have fill : localWidth (.aggregate size) =
        ((⟨offset, width, aggregate⟩ : FieldLayout).setIn bytes number).length := by
      rw [storedLength, length]; rfl
    rw [fill, numberBytes_byteNumber, storedLength]
    exact stored
  · have previous : known other = some remembered := by
      simpa [rememberLocal, same] using specifiedOther
    obtain ⟨otherKind, otherHome, otherStored, otherNumber, otherSlot, otherFits, result,
      otherLoaded⟩ := snapshots other remembered previous
    exact ⟨otherKind, otherHome, otherStored, otherNumber, otherSlot, otherFits, result,
      write_preserves_disjoint_read written otherLoaded
        (Or.inl (homes.distinct other index otherKind _ otherHome home same otherSlot slot))⟩

/-- `stfld` of `value` into field `fieldIndex` of a remembered aggregate local of a valid,
    disjoint `layout` whose bytes decode to `values`: the local is remembered with that field
    stored, its fields then decode to `values` with the stored number at `fieldIndex`, and every
    other snapshot is kept. The value is an int, a word or a 16- or 32-byte vector. The home
    stays writable, its address forms, and the write covers only the field. -/
theorem LocalSnapshots.store_field {entered memory : Memory} {boundary : Nat} {kinds slots}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    (homes : WritableHomes entered boundary kinds slots) (formed : memory.WellFormed)
    {index : Nat} {size : Fin (2^64)} {home : Reference} {bytes : List (BitVec 8)}
    (slot : slots[index]? = some (.bytes (.aggregate size) home))
    (specified : known index = some (.aggregate bytes))
    (writable : access memory home (localWidth (.aggregate size)) 1 true = .ok ())
    {layout : AggregateLayout} (valid : layout.Valid) (disjoint : layout.Disjoint)
    (sized : layout.size = size) {values : List Nat} (decoded : layout.values bytes = values)
    {fieldIndex offset width : Nat} {aggregate : Bool}
    (found : layout.fields[fieldIndex]? = some ⟨offset, width, aggregate⟩)
    (value : CIL.Value) {number : Nat} (encoded : fieldStoreNumber width value = some number) :
    ∃ after,
      (∀ body pc args frame rest,
        step body (.setFieldAt offset width) pc args frame
          (.scalar value :: .reference (.address home) :: rest) memory =
          .ok (.next (pc + 1) rest frame after)) ∧
      LocalSnapshots after slots (rememberLocal known index
        (.aggregate ((⟨offset, width, aggregate⟩ : FieldLayout).setIn bytes number))) ∧
      after.WellFormed ∧ MemoryBelow boundary memory after ∧
      access after home (localWidth (.aggregate size)) 1 true = .ok () ∧
      form after home = .ok home ∧
      layout.values ((⟨offset, width, aggregate⟩ : FieldLayout).setIn bytes number) =
        values.set fieldIndex number ∧
      write memory { home with offset := home.offset + offset } (numberBytes number width) 1 =
        .ok after := by
  obtain ⟨length, loaded⟩ := snapshots.aggregate slot specified
  have within : offset + width ≤ bytes.length :=
    (length.trans sized.symm) ▸ field_within_layout layout valid _ (List.mem_of_getElem? found)
  obtain ⟨after, stepped, written, -⟩ := step_setFieldAt_home
    (field := ⟨offset, width, aggregate⟩) formed loaded (length ▸ writable) within encoded
  obtain ⟨remembered, formedAfter, below, kept, formsAfter, changed⟩ :=
    snapshots.write_field homes formed slot specified writable valid disjoint sized decoded found
      (fieldStoreNumber_lt encoded) written
  exact ⟨after, stepped, remembered, formedAfter, below, kept, formsAfter, changed, written⟩

/-- A nested struct store of `fieldBytes` into field `fieldIndex` of a remembered aggregate local
    of a valid, disjoint `layout` whose bytes decode to `values`: the local is remembered with that
    field holding `fieldBytes`, whose number then sits at `fieldIndex` of the decoded values, and
    every other snapshot is kept. The home stays writable, its address forms, and the write covers
    only the field. -/
theorem LocalSnapshots.store_aggregate_field {entered memory : Memory} {boundary : Nat}
    {kinds slots} {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    (homes : WritableHomes entered boundary kinds slots) (formed : memory.WellFormed)
    {index : Nat} {size : Fin (2^64)} {home : Reference} {bytes : List (BitVec 8)}
    (slot : slots[index]? = some (.bytes (.aggregate size) home))
    (specified : known index = some (.aggregate bytes))
    (writable : access memory home (localWidth (.aggregate size)) 1 true = .ok ())
    {layout : AggregateLayout} (valid : layout.Valid) (disjoint : layout.Disjoint)
    (sized : layout.size = size) {values : List Nat} (decoded : layout.values bytes = values)
    {fieldIndex offset width : Nat} {aggregate : Bool}
    (found : layout.fields[fieldIndex]? = some ⟨offset, width, aggregate⟩)
    (fieldBytes : List (BitVec 8)) (fieldSized : fieldBytes.length = width) :
    ∃ after,
      (∀ body pc args frame rest,
        step body (.setAggregateFieldAt offset width) pc args frame
          (.scalar (.aggregate fieldBytes) :: .reference (.address home) :: rest) memory =
          .ok (.next (pc + 1) rest frame after)) ∧
      LocalSnapshots after slots (rememberLocal known index (.aggregate
        ((⟨offset, width, aggregate⟩ : FieldLayout).setIn bytes (byteNumber fieldBytes)))) ∧
      after.WellFormed ∧ MemoryBelow boundary memory after ∧
      access after home (localWidth (.aggregate size)) 1 true = .ok () ∧
      form after home = .ok home ∧
      layout.values ((⟨offset, width, aggregate⟩ : FieldLayout).setIn bytes
        (byteNumber fieldBytes)) = values.set fieldIndex (byteNumber fieldBytes) ∧
      write memory { home with offset := home.offset + offset } fieldBytes 1 = .ok after := by
  obtain ⟨length, loaded⟩ := snapshots.aggregate slot specified
  have member := List.mem_of_getElem? found
  have within : offset + width ≤ bytes.length :=
    (length.trans sized.symm) ▸ field_within_layout layout valid _ member
  have positive := valid.positive member
  obtain ⟨after, stepped, written, -⟩ := step_setAggregateFieldAt_home
    (field := ⟨offset, width, aggregate⟩) formed loaded (length ▸ writable) within positive
    fieldSized
  have fits : byteNumber fieldBytes < 256 ^ width := fieldSized ▸ byteNumber_lt fieldBytes
  have encoding : numberBytes (byteNumber fieldBytes) width = fieldBytes := by
    rw [← fieldSized, numberBytes_byteNumber]
  obtain ⟨remembered, formedAfter, below, kept, formsAfter, changed⟩ :=
    snapshots.write_field homes formed slot specified writable valid disjoint sized decoded found
      fits (encoding ▸ written)
  exact ⟨after, stepped, remembered, formedAfter, below, kept, formsAfter, changed, written⟩

/-- Field `fieldIndex` of a remembered aggregate local of a valid `layout` whose bytes decode to
    `values` lies inside the local's readable bytes and decodes to the value at `fieldIndex`. -/
theorem LocalSnapshots.field_value {memory : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    {index : Nat} {size : Fin (2^64)} {home : Reference}
    {bytes : List (BitVec 8)} (slot : slots[index]? = some (.bytes (.aggregate size) home))
    (specified : known index = some (.aggregate bytes)) {layout : AggregateLayout}
    (valid : layout.Valid) (sized : layout.size = size) {values : List Nat}
    (decoded : layout.values bytes = values) {fieldIndex : Nat} {field : FieldLayout}
    (found : layout.fields[fieldIndex]? = some field) {value : Nat}
    (present : values[fieldIndex]? = some value) :
    read memory home bytes.length 1 = .ok bytes ∧
      field.offset + field.width ≤ bytes.length ∧ field.numberIn bytes = value := by
  obtain ⟨length, loaded⟩ := snapshots.aggregate slot specified
  refine ⟨loaded, (length.trans sized.symm) ▸
    field_within_layout layout valid _ (List.mem_of_getElem? found), ?_⟩
  rw [← decoded] at present
  simpa [AggregateLayout.values, found] using present

/-- `ldfld` of field `fieldIndex` through the address of a remembered aggregate local of a valid
    `layout` whose bytes decode to `values` pushes that field's value and changes nothing. The
    field is an int, a word or a 16- or 32-byte vector. -/
theorem LocalSnapshots.load_field {memory : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    (formed : memory.WellFormed) {index : Nat} {size : Fin (2^64)} {home : Reference}
    {bytes : List (BitVec 8)} (slot : slots[index]? = some (.bytes (.aggregate size) home))
    (specified : known index = some (.aggregate bytes)) {layout : AggregateLayout}
    (valid : layout.Valid) (sized : layout.size = size) {values : List Nat}
    (decoded : layout.values bytes = values) {fieldIndex offset width : Nat}
    (found : layout.fields[fieldIndex]? = some ⟨offset, width, false⟩) {value : Nat}
    (present : values[fieldIndex]? = some value) :
    ∀ body pc args frame rest,
      step body (.fieldAt offset width false) pc args frame (.reference (.address home) :: rest)
        memory = .ok (.next (pc + 1) (.scalar (numericOfWidth width value) :: rest) frame
          memory) := by
  obtain ⟨loaded, within, number⟩ :=
    snapshots.field_value slot specified valid sized decoded found present
  rw [← number]
  exact step_fieldAt_home (field := ⟨offset, width, false⟩) formed loaded within
    (valid.scalar (List.mem_of_getElem? found))

/-- A signed `ldfld` of field `fieldIndex` through the address of a remembered aggregate local
    of a valid `layout` whose bytes decode to `values` pushes that field's value, sign extended
    from a 1- or 2-byte field, and changes nothing. -/
theorem LocalSnapshots.load_signed_field {memory : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    (formed : memory.WellFormed) {index : Nat} {size : Fin (2^64)} {home : Reference}
    {bytes : List (BitVec 8)} (slot : slots[index]? = some (.bytes (.aggregate size) home))
    (specified : known index = some (.aggregate bytes)) {layout : AggregateLayout}
    (valid : layout.Valid) (sized : layout.size = size) {values : List Nat}
    (decoded : layout.values bytes = values) {fieldIndex offset width : Nat}
    (found : layout.fields[fieldIndex]? = some ⟨offset, width, false⟩) {value : Nat}
    (present : values[fieldIndex]? = some value) :
    ∀ body pc args frame rest,
      step body (.fieldAt offset width true) pc args frame (.reference (.address home) :: rest)
        memory = .ok (.next (pc + 1) (.scalar (signedOfWidth width value) :: rest) frame
          memory) := by
  obtain ⟨loaded, within, number⟩ :=
    snapshots.field_value slot specified valid sized decoded found present
  rw [← number]
  exact step_fieldAt_signed_home (field := ⟨offset, width, false⟩) formed loaded within
    (valid.scalar (List.mem_of_getElem? found))

/-- A nested struct load of field `fieldIndex` through the address of a remembered aggregate
    local of a valid `layout` whose bytes decode to `values` pushes the field's bytes, the
    `width`-byte encoding of its value, and changes nothing. -/
theorem LocalSnapshots.load_aggregate_field {memory : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    (formed : memory.WellFormed) {index : Nat} {size : Fin (2^64)} {home : Reference}
    {bytes : List (BitVec 8)} (slot : slots[index]? = some (.bytes (.aggregate size) home))
    (specified : known index = some (.aggregate bytes)) {layout : AggregateLayout}
    (valid : layout.Valid) (sized : layout.size = size) {values : List Nat}
    (decoded : layout.values bytes = values) {fieldIndex offset width : Nat} {aggregate : Bool}
    (found : layout.fields[fieldIndex]? = some ⟨offset, width, aggregate⟩) {value : Nat}
    (present : values[fieldIndex]? = some value) :
    ∀ body pc args frame rest,
      step body (.aggregateFieldAt offset width) pc args frame
        (.reference (.address home) :: rest) memory =
        .ok (.next (pc + 1) (.scalar (.aggregate (numberBytes value width)) :: rest) frame
          memory) := by
  obtain ⟨loaded, within, number⟩ :=
    snapshots.field_value slot specified valid sized decoded found present
  have member := List.mem_of_getElem? found
  have positive := valid.positive member
  let field : FieldLayout := ⟨offset, width, aggregate⟩
  have fieldLength : (field.bytesIn bytes).length = width := by
    simp only [field, FieldLayout.bytesIn, List.length_take, List.length_drop]
    simp at within
    omega
  have encoding : numberBytes value width = field.bytesIn bytes := by
    have roundTrip := numberBytes_byteNumber (field.bytesIn bytes)
    rw [fieldLength] at roundTrip
    rw [← number]
    exact roundTrip
  rw [encoding]
  exact step_aggregateFieldAt_home (field := ⟨offset, width, aggregate⟩) formed loaded within
    positive

#print axioms LocalSnapshots.aggregate
#print axioms LocalSnapshots.zero_aggregate
#print axioms LocalSnapshots.write_field
#print axioms LocalSnapshots.store_field
#print axioms LocalSnapshots.store_aggregate_field
#print axioms LocalSnapshots.field_value
#print axioms LocalSnapshots.load_field
#print axioms LocalSnapshots.load_signed_field
#print axioms LocalSnapshots.load_aggregate_field

#print axioms numberBytes_mod
#print axioms fieldStoreNumber_lt
#print axioms read_after_field_write

end CIL.Safety
