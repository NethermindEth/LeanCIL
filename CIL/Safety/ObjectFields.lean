import CIL.Safety.ObjectFraming
import CIL.Safety.ByteRoundTrip
import CIL.Safety.MemoryBelow
import CIL.Safety.RenamedMemoryBelow
import CIL.Safety.AggregateFields

/-!
# Named fields of class instances

Proofs about class instances name a field by its class and field name instead of a byte offset.
An extraction generates one `WordField` or `ReferenceField` per instance field of each admitted
class it uses, carrying the class and the model offset the extractor validated; a wrong one
cannot make a proof succeed, since every field instruction carries its own checked operands.

`field.of memory object` is what the field holds, read from memory without checking authority.
`field.Readable` packages what a load needs: a live object of the field's class, the field
located inside it, and readable, initialized storage. `field.Owned` adds write authority, which
a store needs; `field.Holds memory object value` is `Owned` with the field holding `value`.
Each gives the facts the stepping tactics take (`live`, `located`, `load`, `store`), and keeps
across a confined call when the call's footprint is apart from the field (`frame`), so a
contract reads as the C# does: `Account.Balance.Holds final account (balance + amount)`.
`across` decides aliasing: after a call confined to a field of `written`, the same field of
`object` holds the written value when the two are the same object and its old value otherwise.
-/

namespace CIL.Safety

/-- `object` is a live class instance in `memory`: its reference forms as an object reference,
    and names an allocation that existed before any later one. -/
structure LiveObject (memory : Memory) (object : Reference) : Prop where
  formed : formObject memory (.address object) = .ok (.object (.address object))
  old : object.allocation < memory.nextIdentity

/-- A formed object reference in well-formed memory is live. -/
theorem LiveObject.of_formed {memory : Memory} {object : Reference}
    (wellFormed : memory.WellFormed)
    (formed : formObject memory (.address object) = .ok (.object (.address object))) :
    LiveObject memory object :=
  ⟨formed, wellFormed.object_below formed⟩
#print axioms LiveObject.of_formed

/-- A live object's reference is the origin of its allocation. -/
theorem LiveObject.origin {memory : Memory} {object : Reference}
    (live : LiveObject memory object) : object.offset = 0 := by
  have formed := live.formed
  simp only [formObject, checkedAt, Except.mapError, Bind.bind, Except.bind] at formed
  cases found : liveAllocation memory object.allocation with
  | error => simp only [found] at formed; cases formed
  | ok allocation =>
    simp only [found] at formed
    cases kind : allocation.kind <;> simp only [kind] at formed <;> try cases formed
    by_cases origin : object.offset = 0
    · exact origin
    · simp only [origin, ite_false] at formed; cases formed
#print axioms LiveObject.origin

/-- Two different live objects lie in different allocations. -/
theorem LiveObject.allocation_ne {memory : Memory} {left right : Reference}
    (leftLive : LiveObject memory left) (rightLive : LiveObject memory right)
    (distinct : left ≠ right) : left.allocation ≠ right.allocation := by
  intro same
  apply distinct
  have leftOrigin := leftLive.origin
  have rightOrigin := rightLive.origin
  cases left; cases right
  simp only at same leftOrigin rightOrigin
  rw [same, leftOrigin, rightOrigin]
#print axioms LiveObject.allocation_ne

/-- A live object stays live across a confined call. -/
theorem LiveObject.after_confined {footprint : List (Reference × Nat)} {before after : Memory}
    {object : Reference} (live : LiveObject before object)
    (framed : Confined footprint before after) : LiveObject after object :=
  ⟨by rw [formObject_of_allocation (framed.allocations _ live.old)]; exact live.formed,
    Nat.lt_of_lt_of_le live.old framed.grows⟩
#print axioms LiveObject.after_confined

/-- A live object stays live in memory that keeps every allocation below a watermark above it
    and has allocated up to the watermark. -/
theorem LiveObject.after_below {watermark : Nat} {before after : Memory} {object : Reference}
    (live : LiveObject before object) (preserved : MemoryBelow watermark before after)
    (old : object.allocation < watermark) (grows : watermark ≤ after.nextIdentity) :
    LiveObject after object :=
  ⟨by rw [formObject_of_allocation (preserved.allocations _ old)]; exact live.formed,
    Nat.lt_of_lt_of_le old grows⟩
#print axioms LiveObject.after_below

/-- A live object stays live in memory that keeps its allocation and does not lower the next
    identity. -/
theorem LiveObject.after_kept {before after : Memory} {object : Reference}
    (live : LiveObject before object) (preserved : MemoryAt object.allocation before after)
    (grows : before.nextIdentity ≤ after.nextIdentity) : LiveObject after object :=
  ⟨by rw [formObject_of_allocation preserved.allocations]; exact live.formed,
    Nat.lt_of_lt_of_le live.old grows⟩
#print axioms LiveObject.after_kept

/-- A scalar field of a class: `width` bytes at model offset `offset` of every instance of
    `owner` and of the classes derived from it. -/
structure WordField (width : Nat) where
  owner : CIL.Extraction.TypeExpr
  offset : Nat
  deriving DecidableEq, Repr

/-- A class-typed field: the slot at model offset `offset` of every instance of `owner` and of
    the classes derived from it, holding an object reference. -/
structure ReferenceField where
  owner : CIL.Extraction.TypeExpr
  offset : Nat
  deriving DecidableEq, Repr

/-- Read authority over bytes wholly outside a call's footprint is what it was. -/
theorem Confined.access_read {footprint : List (Reference × Nat)} {before after : Memory}
    (framed : Confined footprint before after) (reference : Reference)
    (old : reference.allocation < before.nextIdentity) (width alignment : Nat)
    (outside : ∀ i < width, Outside footprint reference.allocation (reference.offset + i)) :
    access after reference width alignment false =
      access before reference width alignment false := by
  have authority : (List.range width).all
        (fun i => permitted after false { reference with offset := reference.offset + i }) =
      (List.range width).all
        (fun i => permitted before false { reference with offset := reference.offset + i }) := by
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_range]
    constructor
    · intro allowed i bound
      rw [← framed.readable _ old _ (outside i bound)]
      exact allowed i bound
    · intro allowed i bound
      rw [framed.readable _ old _ (outside i bound)]
      exact allowed i bound
  simp only [CIL.Safety.access, form, liveAllocation, framed.allocations _ old, authority]
#print axioms Confined.access_read

/-- What an unsigned load of a `width`-byte field pushes for the value it holds: a 64-bit field
    its word, a narrower one its value zero-extended to 32 bits. -/
class FieldWidth (width : Nat) where
  /-- The pushed value. -/
  loaded : BitVec (8 * width) → CIL.Value
  /-- What a signed load pushes: a narrow value sign-extended to 32 bits. -/
  signedLoaded : BitVec (8 * width) → CIL.Value
  scalar : ScalarWidth width
  numeric : ∀ value, numericOfWidth width value.toNat = loaded value
  signed : ∀ value, signedOfWidth width value.toNat = signedLoaded value

instance : FieldWidth 8 where
  loaded value := .i64 value
  signedLoaded value := .i64 value
  scalar := by decide
  numeric value := by simp [numericOfWidth]
  signed value := by simp [signedOfWidth, numericOfWidth]

instance : FieldWidth 4 where
  loaded value := .i32 value
  signedLoaded value := .i32 value
  scalar := by decide
  numeric value := by simp [numericOfWidth]
  signed value := by simp [signedOfWidth, numericOfWidth]

instance : FieldWidth 2 where
  loaded value := .i32 (value.setWidth 32)
  signedLoaded value := .i32 (value.signExtend 32)
  scalar := by decide
  numeric value := by
    simp only [numericOfWidth]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  signed value := by simp [signedOfWidth]

instance : FieldWidth 1 where
  loaded value := .i32 (value.setWidth 32)
  signedLoaded value := .i32 (value.signExtend 32)
  scalar := by decide
  numeric value := by
    simp only [numericOfWidth]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  signed value := by simp [signedOfWidth]

/-- A 64-bit field loads as its word. -/
@[simp] theorem FieldWidth.loaded_word64 (value : BitVec 64) :
    FieldWidth.loaded (width := 8) value = .i64 value := rfl

/-- A 32-bit field loads as its word. -/
@[simp] theorem FieldWidth.loaded_word32 (value : BitVec 32) :
    FieldWidth.loaded (width := 4) value = .i32 value := rfl

/-- A 16-bit field loads zero-extended to 32 bits. -/
@[simp] theorem FieldWidth.loaded_word16 (value : BitVec 16) :
    FieldWidth.loaded (width := 2) value = .i32 (value.setWidth 32) := rfl

/-- An 8-bit field loads zero-extended to 32 bits. -/
@[simp] theorem FieldWidth.loaded_byte (value : BitVec 8) :
    FieldWidth.loaded (width := 1) value = .i32 (value.setWidth 32) := rfl

namespace WordField

variable {width : Nat}

/-- Where the field lies in `object`. -/
def address (field : WordField width) (object : Reference) : Reference :=
  ⟨object.allocation, field.offset⟩

/-- The footprint entry a call that may change the field names. -/
def entry (field : WordField width) (object : Reference) : Reference × Nat :=
  (field.address object, width)

/-- `op` loads or stores this field: a scalar field operation of its class, offset and width.
    An extraction checks each field it names against an operation of its own code with this. -/
def accessedBy (field : WordField width) : CIL.Op → Bool
  | .memory (.objectField owner offset size _) | .memory (.setObjectField owner offset size) =>
    owner == field.owner && offset == field.offset && size == width
  | _ => false

@[simp] theorem address_allocation (field : WordField width) (object : Reference) :
    (field.address object).allocation = object.allocation := rfl

@[simp] theorem address_offset (field : WordField width) (object : Reference) :
    (field.address object).offset = field.offset := rfl

/-- The bytes of the field in `memory`, whether or not they are readable or initialized. -/
def bytes (field : WordField width) (memory : Memory) (object : Reference) : List (BitVec 8) :=
  (List.range width).map fun index => (memory.cells object.allocation (field.offset + index)).bits

/-- The value the field holds: its bytes decoded little-endian, as a load of it returns. -/
def of (field : WordField width) (memory : Memory) (object : Reference) : BitVec (8 * width) :=
  BitVec.ofNat (8 * width) (byteNumber (field.bytes memory object))

/-- A load of the field succeeds: `object` is a live instance of the field's class, the
    field is located inside it, and its bytes are readable and initialized. -/
structure Readable (field : WordField width) (memory : Memory) (object : Reference) : Prop where
  located : objectFieldAddress memory (.address object) field.owner field.offset =
    .ok (field.address object)
  old : object.allocation < memory.nextIdentity
  readable : ∃ bytes, read memory (field.address object) width 1 = .ok bytes

/-- A load and a store of the field succeed: it is `Readable` and writable. -/
structure Owned (field : WordField width) (memory : Memory) (object : Reference) : Prop
    extends Readable field memory object where
  writable : access memory (field.address object) width 1 true = .ok ()

/-- The field is `Owned` and holds `value`. -/
def Holds (field : WordField width) (memory : Memory) (object : Reference)
    (value : BitVec (8 * width)) : Prop :=
  field.Owned memory object ∧ field.of memory object = value

/-- The field's object is live. -/
theorem Readable.live {field : WordField width} {memory : Memory} {object : Reference}
    (readable : field.Readable memory object) : LiveObject memory object :=
  ⟨formObject_of_objectFieldAddress readable.located, readable.old⟩
#print axioms Readable.live

/-- An owned field holds what it holds. -/
theorem Owned.holds {field : WordField width} {memory : Memory} {object : Reference}
    (owned : field.Owned memory object) : field.Holds memory object (field.of memory object) :=
  ⟨owned, rfl⟩
#print axioms Owned.holds

/-- A readable field reads back as the encoding of the value it holds. -/
theorem Readable.read {field : WordField width} {memory : Memory} {object : Reference}
    (readable : field.Readable memory object) :
    CIL.Safety.read memory (field.address object) width 1 =
      .ok (numberBytes (field.of memory object).toNat width) := by
  obtain ⟨bytes, loaded⟩ := readable.readable
  have shape : bytes = field.bytes memory object := by
    simp only [CIL.Safety.read, Bind.bind, Except.bind] at loaded
    cases accessed : access memory (field.address object) width 1 false with
    | error => simp only [accessed] at loaded; cases loaded
    | ok =>
      simp only [accessed] at loaded
      split at loaded
      · cases loaded
        simp [WordField.bytes, WordField.address, List.map_map, Function.comp_def]
      · cases loaded
  subst shape
  have length : (field.bytes memory object).length = width := by simp [WordField.bytes]
  have bound := byteNumber_lt (field.bytes memory object)
  rw [length] at bound
  have small : byteNumber (field.bytes memory object) < 2 ^ (8 * width) := by
    rwa [Nat.pow_mul]
  rw [loaded]
  simp only [WordField.of, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have roundTrip := numberBytes_byteNumber (field.bytes memory object)
  rw [length] at roundTrip
  rw [roundTrip]
#print axioms Readable.read

/-- A readable scalar field loads as the value it holds. -/
theorem Readable.load {field : WordField width} {memory : Memory} {object : Reference}
    (readable : field.Readable memory object) (scalar : ScalarWidth width) :
    loadValue memory (.address (field.address object)) width =
      .ok (numericOfWidth width (field.of memory object).toNat) :=
  load_scalar_of_read scalar readable.read
#print axioms Readable.load

/-- What an unsigned load of a readable field steps with, as one fact: the object forms, the
    field is located in it, and the load pushes the value the field holds. -/
theorem Readable.facts [shape : FieldWidth width] {field : WordField width} {memory : Memory}
    {object : Reference} (readable : field.Readable memory object) :
    formObject memory (.address object) = .ok (.object (.address object)) ∧
      objectFieldAddress memory (.address object) field.owner field.offset =
        .ok (field.address object) ∧
      loadValue memory (.address (field.address object)) width =
        .ok (FieldWidth.loaded (field.of memory object)) :=
  ⟨readable.live.formed, readable.located, by rw [readable.load shape.scalar, shape.numeric]⟩
#print axioms Readable.facts

/-- What a signed load of a readable field steps with: as `facts`, with the value the field
    holds sign-extended to 32 bits when the field is narrower. -/
theorem Readable.signedFacts [shape : FieldWidth width] {field : WordField width}
    {memory : Memory} {object : Reference} (readable : field.Readable memory object) :
    formObject memory (.address object) = .ok (.object (.address object)) ∧
      objectFieldAddress memory (.address object) field.owner field.offset =
        .ok (field.address object) ∧
      loadValue memory (.address (field.address object)) width true =
        .ok (FieldWidth.signedLoaded (field.of memory object)) := by
  refine ⟨readable.live.formed, readable.located, ?_⟩
  rw [loadValue_signed_of_read shape.scalar readable.read, byteNumber_numberBytes,
    Nat.mod_eq_of_lt (by
      show _ < (2 ^ 8) ^ width; rw [← Nat.pow_mul]; exact (field.of memory object).isLt),
    shape.signed]
#print axioms Readable.signedFacts

/-- A readable 64-bit field loads as the word it holds. -/
theorem Readable.load_i64 {field : WordField 8} {memory : Memory} {object : Reference}
    (readable : field.Readable memory object) :
    loadValue memory (.address (field.address object)) 8 = .ok (.i64 (field.of memory object)) :=
  load_word64_of_read readable.read
#print axioms Readable.load_i64

/-- A readable 32-bit field loads as the word it holds. -/
theorem Readable.load_i32 {field : WordField 4} {memory : Memory} {object : Reference}
    (readable : field.Readable memory object) :
    loadValue memory (.address (field.address object)) 4 =
      .ok (.i32 (field.of memory object)) := by
  rw [readable.load (Or.inr (Or.inr (Or.inl rfl)))]
  simp [numericOfWidth]
#print axioms Readable.load_i32

/-- Storing `value` into an owned field succeeds, confined to the field, and leaves it owned
    and holding `value`. -/
theorem Owned.store {field : WordField width} {memory : Memory} {object : Reference}
    (owned : field.Owned memory object) (value : BitVec (8 * width)) :
    ∃ after, write memory (field.address object) (numberBytes value.toNat width) 1 = .ok after ∧
      Confined [field.entry object] memory after ∧ field.Holds after object value := by
  have length : (numberBytes value.toNat width).length = width := numberBytes_length _ _
  obtain ⟨after, written⟩ := write_succeeds (bytes := numberBytes value.toNat width)
    (by rw [length]; exact owned.writable)
  have framed : Confined [field.entry object] memory after :=
    Confined.write written (by simp [WordField.entry, length])
  have readback := write_readback _ _ _ _ _ written
  rw [length] at readback
  have readable : field.Readable after object :=
    ⟨by rw [objectFieldAddress_of_allocations (write_allocations _ _ _ _ _ written)]
        exact owned.located,
      Nat.lt_of_lt_of_le owned.old framed.grows, _, readback⟩
  refine ⟨after, written, framed,
    ⟨{ readable with
      writable := (framed.access_write (field.address object) owned.old _ _).trans
        owned.writable }, ?_⟩⟩
  have decoded := readable.read
  rw [readback] at decoded
  have bound : value.toNat < 256 ^ width := by have := value.isLt; rwa [Nat.pow_mul] at this
  have equal := congrArg byteNumber (Except.ok.inj decoded)
  rw [byteNumber_numberBytes, byteNumber_numberBytes, Nat.mod_eq_of_lt bound,
    Nat.mod_eq_of_lt (by have := (field.of after object).isLt; rwa [Nat.pow_mul] at this)]
    at equal
  exact (BitVec.eq_of_toNat_eq equal).symm
#print axioms Owned.store

/-- A readable field keeps its storage and value across a call confined to a footprint apart
    from it. -/
theorem Readable.frame {footprint : List (Reference × Nat)} {field : WordField width}
    {before after : Memory} {object : Reference} (readable : field.Readable before object)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (field.address object) width entry) :
    field.Readable after object ∧ field.of after object = field.of before object := by
  have outside := Outside.of_apart apart
  refine ⟨⟨?_, Nat.lt_of_lt_of_le readable.old framed.grows, ?_⟩, ?_⟩
  · rw [objectFieldAddress_of_allocation (reference := object)
      (framed.allocations _ readable.old)]
    exact readable.located
  · obtain ⟨bytes, loaded⟩ := readable.readable
    exact ⟨bytes,
      (framed.read_eq (field.address object) readable.old width 1 outside).trans loaded⟩
  · simp only [WordField.of, WordField.bytes]
    congr 2
    apply List.map_congr_left
    intro index member
    have kept := framed.cells _ readable.old _ (outside index (List.mem_range.mp member))
    simp only [WordField.address_offset] at kept
    rw [kept]
#print axioms Readable.frame

/-- An owned field stays owned, holding its value, across a call confined to a footprint
    apart from it. -/
theorem Owned.frame {footprint : List (Reference × Nat)} {field : WordField width}
    {before after : Memory} {object : Reference} (owned : field.Owned before object)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (field.address object) width entry) :
    field.Holds after object (field.of before object) :=
  have kept := owned.toReadable.frame framed apart
  ⟨{ kept.1 with
      writable := (framed.access_write (field.address object) owned.old _ _).trans
        owned.writable }, kept.2⟩
#print axioms Owned.frame

/-- A readable field stays readable across a call confined to a footprint apart from it. -/
theorem Readable.after_confined {footprint : List (Reference × Nat)} {field : WordField width}
    {before after : Memory} {object : Reference} (readable : field.Readable before object)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (field.address object) width entry) :
    field.Readable after object :=
  (readable.frame framed apart).1
#print axioms Readable.after_confined

/-- An owned field stays owned across a call confined to a footprint apart from it. -/
theorem Owned.after_confined {footprint : List (Reference × Nat)} {field : WordField width}
    {before after : Memory} {object : Reference} (owned : field.Owned before object)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (field.address object) width entry) :
    field.Owned after object :=
  (owned.frame framed apart).1
#print axioms Owned.after_confined

/-- A field holding `value` holds it across a call confined to a footprint apart from it. -/
theorem Holds.after_confined {footprint : List (Reference × Nat)} {field : WordField width}
    {before after : Memory} {object : Reference} {value : BitVec (8 * width)}
    (held : field.Holds before object value) (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (field.address object) width entry) :
    field.Holds after object value :=
  held.2 ▸ held.1.frame framed apart
#print axioms Holds.after_confined

/-- After a call confined to this field of `written` that leaves it holding `value`, the same
    field of `object` holds `value` when the two are the same object, and what it held before
    the call when they are different objects. -/
theorem Owned.across {field : WordField width} {before after : Memory}
    {object written : Reference} {value : BitVec (8 * width)}
    (owned : field.Owned before object) (writtenLive : LiveObject before written)
    (framed : Confined [field.entry written] before after)
    (held : field.Holds after written value) :
    field.Holds after object (if written = object then value else field.of before object) := by
  by_cases same : written = object
  · subst same
    simpa using held
  · simp only [same, ite_false]
    refine owned.frame framed fun entry member => ?_
    simp only [List.mem_singleton] at member
    subst member
    exact Or.inl fun equal =>
      writtenLive.allocation_ne owned.toReadable.live same equal.symm
#print axioms Owned.across

/-- After a call confined to this field of `written` that leaves it holding `value`, the same
    field of a readable `object` is readable and holds `value` when the two are the same object,
    and what it held before the call when they are different objects. -/
theorem Readable.across {field : WordField width} {before after : Memory}
    {object written : Reference} {value : BitVec (8 * width)}
    (readable : field.Readable before object) (writtenLive : LiveObject before written)
    (framed : Confined [field.entry written] before after)
    (held : field.Holds after written value) :
    field.Readable after object ∧
      field.of after object = if written = object then value else field.of before object := by
  by_cases same : written = object
  · subst same
    simpa using ⟨held.1.toReadable, held.2⟩
  · simp only [same, ite_false]
    refine readable.frame framed fun entry member => ?_
    simp only [List.mem_singleton] at member
    subst member
    exact Or.inl fun equal => writtenLive.allocation_ne readable.live same equal.symm
#print axioms Readable.across

/-- A readable field keeps its storage and value in memory that keeps every allocation below a
    watermark above it and has allocated up to the watermark. -/
theorem Readable.below {watermark : Nat} {field : WordField width} {before after : Memory}
    {object : Reference} (readable : field.Readable before object)
    (preserved : MemoryBelow watermark before after) (old : object.allocation < watermark)
    (grows : watermark ≤ after.nextIdentity) :
    field.Readable after object ∧ field.of after object = field.of before object := by
  refine ⟨⟨?_, Nat.lt_of_lt_of_le old grows, ?_⟩, ?_⟩
  · rw [objectFieldAddress_of_allocation (reference := object) (preserved.allocations _ old)]
    exact readable.located
  · obtain ⟨bytes, loaded⟩ := readable.readable
    exact ⟨bytes, (preserved.read (field.address object) old width 1).trans loaded⟩
  · simp only [WordField.of, WordField.bytes, preserved.cells _ old]
#print axioms Readable.below

/-- A readable field stays readable in memory that keeps every allocation below a watermark
    above it and has allocated up to the watermark. -/
theorem Readable.after_below {watermark : Nat} {field : WordField width} {before after : Memory}
    {object : Reference} (readable : field.Readable before object)
    (preserved : MemoryBelow watermark before after) (old : object.allocation < watermark)
    (grows : watermark ≤ after.nextIdentity) : field.Readable after object :=
  (readable.below preserved old grows).1
#print axioms Readable.after_below

/-- An owned field stays owned in memory that keeps every allocation below a watermark above it
    and has allocated up to the watermark. -/
theorem Owned.after_below {watermark : Nat} {field : WordField width} {before after : Memory}
    {object : Reference} (owned : field.Owned before object)
    (preserved : MemoryBelow watermark before after) (old : object.allocation < watermark)
    (grows : watermark ≤ after.nextIdentity) : field.Owned after object :=
  { owned.toReadable.after_below preserved old grows with
    writable := (preserved.access (field.address object) old width 1 true).trans owned.writable }
#print axioms Owned.after_below

/-- A field holding `value` holds it in memory that keeps every allocation below a watermark
    above it and has allocated up to the watermark. -/
theorem Holds.after_below {watermark : Nat} {field : WordField width} {before after : Memory}
    {object : Reference} {value : BitVec (8 * width)} (held : field.Holds before object value)
    (preserved : MemoryBelow watermark before after) (old : object.allocation < watermark)
    (grows : watermark ≤ after.nextIdentity) : field.Holds after object value :=
  ⟨held.1.after_below preserved old grows,
    (held.1.toReadable.below preserved old grows).2.trans held.2⟩
#print axioms Holds.after_below

/-- A readable field keeps its storage and value in memory that keeps its object's allocation
    and does not lower the next identity. -/
theorem Readable.kept {field : WordField width} {before after : Memory} {object : Reference}
    (readable : field.Readable before object) (preserved : MemoryAt object.allocation before after)
    (grows : before.nextIdentity ≤ after.nextIdentity) :
    field.Readable after object ∧ field.of after object = field.of before object := by
  refine ⟨⟨?_, Nat.lt_of_lt_of_le readable.old grows, ?_⟩, ?_⟩
  · rw [objectFieldAddress_of_allocation (reference := object) preserved.allocations]
    exact readable.located
  · obtain ⟨bytes, loaded⟩ := readable.readable
    exact ⟨bytes, (MemoryAt.read (r := field.address object) preserved width 1).trans loaded⟩
  · simp only [WordField.of, WordField.bytes, preserved.cells]
#print axioms Readable.kept

/-- An owned field stays owned in memory that keeps its object's allocation. -/
theorem Owned.after_kept {field : WordField width} {before after : Memory} {object : Reference}
    (owned : field.Owned before object) (preserved : MemoryAt object.allocation before after)
    (grows : before.nextIdentity ≤ after.nextIdentity) : field.Owned after object :=
  { (owned.toReadable.kept preserved grows).1 with
    writable := (MemoryAt.access (r := field.address object) preserved width 1 true).trans
      owned.writable }
#print axioms Owned.after_kept

/-- A field holding `value` holds it in memory that keeps its object's allocation. -/
theorem Holds.after_kept {field : WordField width} {before after : Memory} {object : Reference}
    {value : BitVec (8 * width)} (held : field.Holds before object value)
    (preserved : MemoryAt object.allocation before after)
    (grows : before.nextIdentity ≤ after.nextIdentity) : field.Holds after object value :=
  ⟨held.1.after_kept preserved grows, (held.1.toReadable.kept preserved grows).2.trans held.2⟩
#print axioms Holds.after_kept

/-- A field of a fresh instance, declared by its class or one of its bases and inside its size,
    is owned: `newobj` grants the instance's storage to the code that created it. -/
theorem fresh_owned {field : WordField width} (memory : Memory) (type : RuntimeType)
    {size : Nat} (declared : field.owner ∈ type.lineage) (bounded : size < nativeLimit)
    (fits : field.offset + width ≤ size) (nonempty : 0 < width) :
    field.Owned (objectMemory memory type size) ⟨memory.nextIdentity, 0⟩ where
  located := objectMemory_field memory type declared bounded (by omega)
  old := by simp [objectMemory]
  readable := by
    refine ⟨(List.range width).map fun _ => 0, ?_⟩
    have accessed := objectMemory_access memory type bounded fits nonempty false
    simp only [CIL.Safety.read, WordField.address, Bind.bind, Except.bind]
    rw [accessed]
    simp [objectMemory, Pure.pure, Except.pure]
  writable := objectMemory_access memory type bounded fits nonempty true
#print axioms fresh_owned

end WordField

namespace ReferenceField

/-- Where the field's slot lies in `object`. -/
def address (field : ReferenceField) (object : Reference) : Reference :=
  ⟨object.allocation, field.offset⟩

/-- The footprint entry a call that may change the field names. -/
def entry (field : ReferenceField) (object : Reference) : Reference × Nat :=
  (field.address object, objectFieldSlot)

/-- `op` loads or stores this field: a reference field operation of its class and offset. An
    extraction checks each field it names against an operation of its own code with this. -/
def accessedBy (field : ReferenceField) : CIL.Op → Bool
  | .memory (.objectReferenceField owner offset)
  | .memory (.setObjectReferenceField owner offset) =>
    owner == field.owner && offset == field.offset
  | _ => false

@[simp] theorem address_allocation (field : ReferenceField) (object : Reference) :
    (field.address object).allocation = object.allocation := rfl

@[simp] theorem address_offset (field : ReferenceField) (object : Reference) :
    (field.address object).offset = field.offset := rfl

/-- The reference the field holds in `memory`, whether or not its slot is readable. -/
def of (field : ReferenceField) (memory : Memory) (object : Reference) : ManagedReference :=
  memory.slots object.allocation field.offset

/-- A load of the field reaches its slot: `object` is a live instance of the field's class, the
    field is located inside it, and its slot is readable. -/
structure Readable (field : ReferenceField) (memory : Memory) (object : Reference) : Prop where
  located : objectFieldAddress memory (.address object) field.owner field.offset =
    .ok (field.address object)
  old : object.allocation < memory.nextIdentity
  readable : access memory (field.address object) objectFieldSlot 1 false = .ok ()

/-- A load and a store of the field reach its slot: it is `Readable` and writable. -/
structure Owned (field : ReferenceField) (memory : Memory) (object : Reference) : Prop
    extends Readable field memory object where
  writable : access memory (field.address object) objectFieldSlot 1 true = .ok ()

/-- The field is `Owned` and holds `value`. -/
def Holds (field : ReferenceField) (memory : Memory) (object : Reference)
    (value : ManagedReference) : Prop :=
  field.Owned memory object ∧ field.of memory object = value

/-- The field's object is live. -/
theorem Readable.live {field : ReferenceField} {memory : Memory} {object : Reference}
    (readable : field.Readable memory object) : LiveObject memory object :=
  ⟨formObject_of_objectFieldAddress readable.located, readable.old⟩
#print axioms Readable.live

/-- An owned field holds what it holds. -/
theorem Owned.holds {field : ReferenceField} {memory : Memory} {object : Reference}
    (owned : field.Owned memory object) : field.Holds memory object (field.of memory object) :=
  ⟨owned, rfl⟩
#print axioms Owned.holds

/-- A readable field loads the reference it holds, which must still form. -/
theorem Readable.load {field : ReferenceField} {memory : Memory} {object : Reference}
    (readable : field.Readable memory object) :
    loadSlot memory (field.address object) = formObject memory (field.of memory object) :=
  loadSlot_of_access readable.readable
#print axioms Readable.load

/-- A readable field holding a live object loads it. -/
theorem Readable.load_live {field : ReferenceField} {memory : Memory}
    {object target : Reference} (readable : field.Readable memory object)
    (held : field.of memory object = .address target) (live : LiveObject memory target) :
    loadSlot memory (field.address object) = .ok (.object (.address target)) := by
  rw [readable.load, held]
  exact live.formed
#print axioms Readable.load_live

/-- What a load of a readable field holding a live object steps with, as one fact: the
    field's object forms, the field is located in it, and the load pushes the held object. -/
theorem Readable.facts {field : ReferenceField} {memory : Memory} {object target : Reference}
    (readable : field.Readable memory object) (held : field.of memory object = .address target)
    (live : LiveObject memory target) :
    formObject memory (.address object) = .ok (.object (.address object)) ∧
      objectFieldAddress memory (.address object) field.owner field.offset =
        .ok (field.address object) ∧
      loadSlot memory (field.address object) = .ok (.object (.address target)) :=
  ⟨readable.live.formed, readable.located, readable.load_live held live⟩
#print axioms Readable.facts

/-- A readable field holding null loads null. -/
theorem Readable.load_null {field : ReferenceField} {memory : Memory} {object : Reference}
    (readable : field.Readable memory object) (held : field.of memory object = .null) :
    loadSlot memory (field.address object) = .ok (.object .null) := by
  rw [readable.load, held]
  rfl
#print axioms Readable.load_null

/-- Storing a live object into an owned field succeeds, confined to the field, and leaves it
    owned and holding the object. -/
theorem Owned.store {field : ReferenceField} {memory : Memory} {object target : Reference}
    (owned : field.Owned memory object) (live : LiveObject memory target) :
    storeSlot memory (field.address object) (.address target) =
        .ok (setSlot memory (field.address object) (.address target)) ∧
      Confined [field.entry object] memory
        (setSlot memory (field.address object) (.address target)) ∧
      field.Holds (setSlot memory (field.address object) (.address target)) object
          (.address target) :=
  ⟨storeSlot_of_access owned.writable live.formed,
    Confined.setSlot _ (List.mem_singleton_self _) (by decide),
    ⟨{ located := by rw [objectFieldAddress_setSlot]; exact owned.located
       old := owned.old
       readable := owned.readable
       writable := owned.writable }, setSlot_slots_same _ _ _⟩⟩
#print axioms Owned.store

/-- A readable field keeps its slot, its authority and what it holds across a call confined to a
    footprint apart from it. -/
theorem Readable.frame {footprint : List (Reference × Nat)} {field : ReferenceField}
    {before after : Memory} {object : Reference} (readable : field.Readable before object)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (field.address object) objectFieldSlot entry) :
    field.Readable after object ∧ field.of after object = field.of before object := by
  have outside := Outside.of_apart apart
  refine ⟨⟨?_, Nat.lt_of_lt_of_le readable.old framed.grows, ?_⟩, ?_⟩
  · rw [objectFieldAddress_of_allocation (reference := object)
      (framed.allocations _ readable.old)]
    exact readable.located
  · rw [← readable.readable]
    exact framed.access_read (field.address object) readable.old _ _ outside
  · exact framed.slots _ readable.old _ (by simpa using outside 0 (by decide))
#print axioms Readable.frame

/-- An owned field stays owned, holding what it held, across a call confined to a footprint
    apart from it. -/
theorem Owned.frame {footprint : List (Reference × Nat)} {field : ReferenceField}
    {before after : Memory} {object : Reference} (owned : field.Owned before object)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (field.address object) objectFieldSlot entry) :
    field.Holds after object (field.of before object) :=
  have kept := owned.toReadable.frame framed apart
  ⟨{ kept.1 with
      writable := (framed.access_write (field.address object) owned.old _ _).trans
        owned.writable }, kept.2⟩
#print axioms Owned.frame

/-- A readable field stays readable across a call confined to a footprint apart from it. -/
theorem Readable.after_confined {footprint : List (Reference × Nat)} {field : ReferenceField}
    {before after : Memory} {object : Reference} (readable : field.Readable before object)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (field.address object) objectFieldSlot entry) :
    field.Readable after object :=
  (readable.frame framed apart).1
#print axioms Readable.after_confined

/-- An owned field stays owned across a call confined to a footprint apart from it. -/
theorem Owned.after_confined {footprint : List (Reference × Nat)} {field : ReferenceField}
    {before after : Memory} {object : Reference} (owned : field.Owned before object)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (field.address object) objectFieldSlot entry) :
    field.Owned after object :=
  (owned.frame framed apart).1
#print axioms Owned.after_confined

/-- A field holding `value` holds it across a call confined to a footprint apart from it. -/
theorem Holds.after_confined {footprint : List (Reference × Nat)} {field : ReferenceField}
    {before after : Memory} {object : Reference} {value : ManagedReference}
    (held : field.Holds before object value) (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (field.address object) objectFieldSlot entry) :
    field.Holds after object value :=
  held.2 ▸ held.1.frame framed apart
#print axioms Holds.after_confined

/-- After a call confined to this field of `written` that leaves it holding `value`, the same
    field of `object` holds `value` when the two are the same object, and what it held before
    the call when they are different objects. -/
theorem Owned.across {field : ReferenceField} {before after : Memory}
    {object written : Reference} {value : ManagedReference}
    (owned : field.Owned before object) (writtenLive : LiveObject before written)
    (framed : Confined [field.entry written] before after)
    (held : field.Holds after written value) :
    field.Holds after object (if written = object then value else field.of before object) := by
  by_cases same : written = object
  · subst same
    simpa using held
  · simp only [same, ite_false]
    refine owned.frame framed fun entry member => ?_
    simp only [List.mem_singleton] at member
    subst member
    exact Or.inl fun equal =>
      writtenLive.allocation_ne owned.toReadable.live same equal.symm
#print axioms Owned.across

/-- After a call confined to this field of `written` that leaves it holding `value`, the same
    field of a readable `object` is readable and holds `value` when the two are the same object,
    and what it held before the call when they are different objects. -/
theorem Readable.across {field : ReferenceField} {before after : Memory}
    {object written : Reference} {value : ManagedReference}
    (readable : field.Readable before object) (writtenLive : LiveObject before written)
    (framed : Confined [field.entry written] before after)
    (held : field.Holds after written value) :
    field.Readable after object ∧
      field.of after object = if written = object then value else field.of before object := by
  by_cases same : written = object
  · subst same
    simpa using ⟨held.1.toReadable, held.2⟩
  · simp only [same, ite_false]
    refine readable.frame framed fun entry member => ?_
    simp only [List.mem_singleton] at member
    subst member
    exact Or.inl fun equal => writtenLive.allocation_ne readable.live same equal.symm
#print axioms Readable.across

/-- A readable field keeps its slot and what it holds in memory that keeps every allocation
    below a watermark above it and has allocated up to the watermark. -/
theorem Readable.below {watermark : Nat} {field : ReferenceField} {before after : Memory}
    {object : Reference} (readable : field.Readable before object)
    (preserved : MemoryBelow watermark before after) (old : object.allocation < watermark)
    (grows : watermark ≤ after.nextIdentity) :
    field.Readable after object ∧ field.of after object = field.of before object := by
  refine ⟨⟨?_, Nat.lt_of_lt_of_le old grows,
    (preserved.access (field.address object) old _ 1 false).trans readable.readable⟩,
    preserved.slots _ old _⟩
  rw [objectFieldAddress_of_allocation (reference := object) (preserved.allocations _ old)]
  exact readable.located
#print axioms Readable.below

/-- A readable field stays readable in memory that keeps every allocation below a watermark
    above it and has allocated up to the watermark. -/
theorem Readable.after_below {watermark : Nat} {field : ReferenceField} {before after : Memory}
    {object : Reference} (readable : field.Readable before object)
    (preserved : MemoryBelow watermark before after) (old : object.allocation < watermark)
    (grows : watermark ≤ after.nextIdentity) : field.Readable after object :=
  (readable.below preserved old grows).1
#print axioms Readable.after_below

/-- An owned field stays owned in memory that keeps every allocation below a watermark above it
    and has allocated up to the watermark. -/
theorem Owned.after_below {watermark : Nat} {field : ReferenceField} {before after : Memory}
    {object : Reference} (owned : field.Owned before object)
    (preserved : MemoryBelow watermark before after) (old : object.allocation < watermark)
    (grows : watermark ≤ after.nextIdentity) : field.Owned after object :=
  { owned.toReadable.after_below preserved old grows with
    writable := (preserved.access (field.address object) old _ 1 true).trans owned.writable }
#print axioms Owned.after_below

/-- A field holding `value` holds it in memory that keeps every allocation below a watermark
    above it and has allocated up to the watermark. -/
theorem Holds.after_below {watermark : Nat} {field : ReferenceField} {before after : Memory}
    {object : Reference} {value : ManagedReference} (held : field.Holds before object value)
    (preserved : MemoryBelow watermark before after) (old : object.allocation < watermark)
    (grows : watermark ≤ after.nextIdentity) : field.Holds after object value :=
  ⟨held.1.after_below preserved old grows,
    (held.1.toReadable.below preserved old grows).2.trans held.2⟩
#print axioms Holds.after_below

/-- A readable field keeps its slot and what it holds in memory that keeps its object's
    allocation and does not lower the next identity. -/
theorem Readable.kept {field : ReferenceField} {before after : Memory} {object : Reference}
    (readable : field.Readable before object) (preserved : MemoryAt object.allocation before after)
    (grows : before.nextIdentity ≤ after.nextIdentity) :
    field.Readable after object ∧ field.of after object = field.of before object := by
  refine ⟨⟨?_, Nat.lt_of_lt_of_le readable.old grows,
    (MemoryAt.access (r := field.address object) preserved _ 1 false).trans readable.readable⟩,
    preserved.slots _⟩
  rw [objectFieldAddress_of_allocation (reference := object) preserved.allocations]
  exact readable.located
#print axioms Readable.kept

/-- An owned field stays owned in memory that keeps its object's allocation. -/
theorem Owned.after_kept {field : ReferenceField} {before after : Memory} {object : Reference}
    (owned : field.Owned before object) (preserved : MemoryAt object.allocation before after)
    (grows : before.nextIdentity ≤ after.nextIdentity) : field.Owned after object :=
  { (owned.toReadable.kept preserved grows).1 with
    writable := (MemoryAt.access (r := field.address object) preserved _ 1 true).trans
      owned.writable }
#print axioms Owned.after_kept

/-- A field holding `value` holds it in memory that keeps its object's allocation. -/
theorem Holds.after_kept {field : ReferenceField} {before after : Memory} {object : Reference}
    {value : ManagedReference} (held : field.Holds before object value)
    (preserved : MemoryAt object.allocation before after)
    (grows : before.nextIdentity ≤ after.nextIdentity) : field.Holds after object value :=
  ⟨held.1.after_kept preserved grows, (held.1.toReadable.kept preserved grows).2.trans held.2⟩
#print axioms Holds.after_kept

/-- A field holding a caller object holds it in memory whose bytes, authority and caller
    references agree below a watermark above both objects, and that has allocated up to it: the
    memory an execution allocating different private storage leaves. -/
theorem Holds.of_agree {watermark : Nat} {field : ReferenceField} {source target : Memory}
    {object held : Reference} (holds : field.Holds source object (.address held))
    (bytes : BytesBelow watermark source target) (agree : SlotsAgreeBelow watermark source target)
    (old : object.allocation < watermark) (heldOld : held.allocation < watermark)
    (grows : watermark ≤ target.nextIdentity) : field.Holds target object (.address held) := by
  refine ⟨⟨⟨?_, Nat.lt_of_lt_of_le old grows,
      (bytes.access (field.address object) old _ _ _).trans holds.1.readable⟩,
      (bytes.access (field.address object) old _ _ _).trans holds.1.writable⟩,
    agree.held old holds.2 heldOld⟩
  rw [objectFieldAddress_of_allocation (reference := object) (bytes.allocations _ old)]
  exact holds.1.located
#print axioms Holds.of_agree

/-- A reference field of a fresh instance, declared by its class or one of its bases and inside
    its size, is owned and holds null, as `newobj` zeroes every field. -/
theorem fresh_holds_null {field : ReferenceField} (memory : Memory) (type : RuntimeType)
    {size : Nat} (declared : field.owner ∈ type.lineage) (bounded : size < nativeLimit)
    (fits : field.offset + objectFieldSlot ≤ size) :
    field.Holds (objectMemory memory type size) ⟨memory.nextIdentity, 0⟩ .null :=
  ⟨{ located := objectMemory_field memory type declared bounded
        (by simp only [objectFieldSlot] at fits; omega)
     old := by simp [objectMemory]
     readable := objectMemory_access memory type bounded fits (by decide) false
     writable := objectMemory_access memory type bounded fits (by decide) true },
    by simp [ReferenceField.of, objectMemory]⟩
#print axioms fresh_holds_null

end ReferenceField

/-- Fields at disjoint byte ranges are apart, whichever objects hold them. -/
theorem apart_of_offsets {address : Reference} {width : Nat} {entry : Reference × Nat}
    (disjoint : address.offset + width ≤ entry.1.offset ∨
      entry.1.offset + entry.2 ≤ address.offset) :
    Apart address width entry :=
  Or.inr disjoint
#print axioms apart_of_offsets

/-- A field is apart from every entry of a footprint whose offset range misses its own, whichever
    objects the entries belong to; `decide` checks it for the views an extraction names. -/
theorem apart_of_entries {address : Reference} {width : Nat} {footprint : List (Reference × Nat)}
    (disjoint : footprint.all (fun entry => decide (address.offset + width ≤ entry.1.offset) ||
      decide (entry.1.offset + entry.2 ≤ address.offset)) = true) :
    ∀ entry ∈ footprint, Apart address width entry := by
  intro entry member
  have missed := List.all_eq_true.mp disjoint entry member
  simp only [Bool.or_eq_true, decide_eq_true_eq] at missed
  exact apart_of_offsets missed
#print axioms apart_of_entries

/-- Storage of two different live objects is apart, whatever fields of them it holds. -/
theorem apart_of_objects {memory : Memory} {object other : Reference} {offset width : Nat}
    {entry : Reference × Nat} (live : LiveObject memory object)
    (otherLive : LiveObject memory other) (distinct : other ≠ object)
    (owned : entry.1.allocation = other.allocation) :
    Apart ⟨object.allocation, offset⟩ width entry :=
  Or.inl fun same => otherLive.allocation_ne live distinct (owned.symm.trans same.symm)
#print axioms apart_of_objects

end CIL.Safety
