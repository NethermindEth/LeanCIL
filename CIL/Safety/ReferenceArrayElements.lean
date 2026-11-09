import CIL.Safety.ObjectFields
import CIL.Safety.ObjectAllocationLemmas

/-!
# Elements of arrays of class references

An array of class references is an object whose runtime type is `E[]`, with element `i` held in
the slot at `objectFieldSlot * i` (see [SOUNDNESS-RUNTIME](../../docs/SOUNDNESS-RUNTIME.md)).
Proofs name an element by its array and index, as they name a class field by its object.

`ReferenceArray.Live memory array element length` is a live array of `element` with `length`
elements. `ReferenceArray.of memory array index` is what an element holds, whether or not it is
readable. `Readable` packages what `ldelem.ref` needs and `Owned` adds what `stelem.ref` needs;
`Holds` is `Owned` with the element holding a value, and `Reads` is `Readable` with it. Each gives
the facts the stepping tactics take (`facts`, `store`, `store_null`), keeps across a confined call
whose footprint is apart from the element (`frame`), and `across` decides aliasing between two
elements. `Live.field_ne` separates an array from every object with a field, so element and field
facts carry across each other's stores. A fresh array is live with every element owned and null
(`fresh`).
-/

namespace CIL.Safety
namespace ReferenceArray

/-- The slot of element `index` of `array`. -/
def slot (array : Reference) (index : Nat) : Reference :=
  ⟨array.allocation, objectFieldSlot * index⟩

/-- The footprint entry a call that may change element `index` names. -/
def entry (array : Reference) (index : Nat) : Reference × Nat :=
  (slot array index, objectFieldSlot)

/-- The reference element `index` of `array` holds in `memory`, whether or not it is readable. -/
def of (memory : Memory) (array : Reference) (index : Nat) : ManagedReference :=
  memory.slots array.allocation (objectFieldSlot * index)

@[simp] theorem slot_allocation (array : Reference) (index : Nat) :
    (slot array index).allocation = array.allocation := rfl

/-- `array` is a live array of class `element` with `length` elements, located from its
    reference, and it was allocated before any later allocation. -/
structure Live (memory : Memory) (array : Reference) (element : CIL.Extraction.TypeExpr)
    (length : Nat) : Prop where
  located : referenceArrayOf memory (.address array) = .ok (array, element, length)
  old : array.allocation < memory.nextIdentity

/-- A load of element `index` reaches its slot: the array is live, the index is inside it, and
    the slot is readable. -/
structure Readable (memory : Memory) (array : Reference) (element : CIL.Extraction.TypeExpr)
    (length index : Nat) : Prop extends Live memory array element length where
  inside : index < length
  readable : access memory (slot array index) objectFieldSlot 1 false = .ok ()

/-- A load and a store of element `index` reach its slot: it is `Readable` and writable. -/
structure Owned (memory : Memory) (array : Reference) (element : CIL.Extraction.TypeExpr)
    (length index : Nat) : Prop extends Readable memory array element length index where
  writable : access memory (slot array index) objectFieldSlot 1 true = .ok ()

/-- Element `index` is `Owned` and holds `value`. -/
def Holds (memory : Memory) (array : Reference) (element : CIL.Extraction.TypeExpr)
    (length index : Nat) (value : ManagedReference) : Prop :=
  Owned memory array element length index ∧ of memory array index = value

/-- A live array locates element `index` at its slot when the index is inside it. -/
theorem Live.slot_located {memory : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index : Nat}
    (live : Live memory array element length) (inside : index < length) :
    referenceArraySlot memory (.address array) index = .ok (slot array index, element) := by
  simp only [referenceArraySlot, live.located, inside, Bind.bind, Except.bind, ite_true,
    Pure.pure, Except.pure, slot]
#print axioms Live.slot_located

/-- An index at or past the length of a live array throws `IndexOutOfRangeException`. -/
theorem Live.slot_outside {memory : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index : Nat}
    (live : Live memory array element length) (outside : length ≤ index) :
    referenceArraySlot memory (.address array) index =
      .error (.thrown "System.IndexOutOfRangeException") := by
  simp only [referenceArraySlot, live.located, Nat.not_lt.mpr outside, Bind.bind, Except.bind,
    ite_false]
#print axioms Live.slot_outside

/-- A live array forms as an object reference, as every argument and local must. -/
theorem Live.formed {memory : Memory} {array : Reference} {element : CIL.Extraction.TypeExpr}
    {length : Nat} (live : Live memory array element length) :
    formObject memory (.address array) = .ok (.object (.address array)) := by
  have located := live.located
  simp only [referenceArrayOf, checkedAt, Except.mapError, Bind.bind, Except.bind] at located
  simp only [formObject, checkedAt, Except.mapError, Bind.bind, Except.bind]
  repeat' first
    | contradiction
    | rfl
    | split at located
    | split
  all_goals simp_all
#print axioms Live.formed

/-- A live array is a live object. -/
theorem Live.object {memory : Memory} {array : Reference} {element : CIL.Extraction.TypeExpr}
    {length : Nat} (live : Live memory array element length) : LiveObject memory array :=
  ⟨live.formed, live.old⟩
#print axioms Live.object

/-- A live array keeps its location in memory that keeps its allocation. -/
theorem Live.of_allocation {before after : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length : Nat} (live : Live before array element length)
    (same : after.allocations array.allocation = before.allocations array.allocation)
    (grows : before.nextIdentity ≤ after.nextIdentity) : Live after array element length :=
  ⟨by simp only [referenceArrayOf, liveAllocation, same] at live ⊢; exact live.located,
    Nat.lt_of_lt_of_le live.old grows⟩
#print axioms Live.of_allocation

/-- A readable element loads the reference it holds, which must still form. -/
theorem Readable.load {memory : Memory} {array : Reference} {element : CIL.Extraction.TypeExpr}
    {length index : Nat} (readable : Readable memory array element length index) :
    loadSlot memory (slot array index) = formObject memory (of memory array index) :=
  loadSlot_of_access readable.readable
#print axioms Readable.load

/-- What a load of a readable element steps with, as one fact: the element's slot is located,
    and the load pushes the live object it holds. -/
theorem Readable.facts {memory : Memory} {array target : Reference}
    {element : CIL.Extraction.TypeExpr} {length index : Nat}
    (readable : Readable memory array element length index)
    (held : of memory array index = .address target) (live : LiveObject memory target) :
    referenceArraySlot memory (.address array) index = .ok (slot array index, element) ∧
      loadSlot memory (slot array index) = .ok (.object (.address target)) := by
  refine ⟨readable.slot_located readable.inside, ?_⟩
  rw [readable.load, held]
  exact live.formed
#print axioms Readable.facts

/-- What a load of a readable element holding null steps with. -/
theorem Readable.facts_null {memory : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index : Nat}
    (readable : Readable memory array element length index)
    (held : of memory array index = .null) :
    referenceArraySlot memory (.address array) index = .ok (slot array index, element) ∧
      loadSlot memory (slot array index) = .ok (.object .null) := by
  refine ⟨readable.slot_located readable.inside, ?_⟩
  rw [readable.load, held]
  rfl
#print axioms Readable.facts_null

/-- The reference element `index` holds forms in `memory`: null, or a live object of any class,
    which a load pushes as it is. -/
def Forms (memory : Memory) (array : Reference) (index : Nat) : Prop :=
  formObject memory (of memory array index) = .ok (.object (of memory array index))

/-- `Forms` as the equation the stepping tactics rewrite with. -/
theorem Forms.formed {memory : Memory} {array : Reference} {index : Nat}
    (forms : Forms memory array index) :
    formObject memory (of memory array index) = .ok (.object (of memory array index)) :=
  forms
#print axioms Forms.formed

/-- What a load of a readable element whose reference forms steps with, null or not: the slot is
    located, and the load pushes the reference it holds. -/
theorem Readable.facts_forms {memory : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index : Nat}
    (readable : Readable memory array element length index) (forms : Forms memory array index) :
    referenceArraySlot memory (.address array) index = .ok (slot array index, element) ∧
      loadSlot memory (slot array index) = .ok (.object (of memory array index)) :=
  ⟨readable.slot_located readable.inside, readable.load.trans forms⟩
#print axioms Readable.facts_forms

/-- An array keeps its location, and its elements their authority, when one slot changes. -/
private theorem Owned.after_setSlot {memory : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index : Nat} (field : Reference)
    (value : ManagedReference) (owned : Owned memory array element length index) :
    Owned (setSlot memory field value) array element length index :=
  { located := owned.located
    old := owned.old
    inside := owned.inside
    readable := owned.readable
    writable := owned.writable }

/-- Storing a live object that passes the covariance check into an owned element succeeds,
    confined to the element, and leaves it owned and holding the object. -/
theorem Owned.store {memory : Memory} {array target : Reference}
    {element : CIL.Extraction.TypeExpr} {length index : Nat}
    (owned : Owned memory array element length index) (live : LiveObject memory target)
    (storable : storableIn memory element (.address target) = .ok ()) :
    referenceArraySlot memory (.address array) index = .ok (slot array index, element) ∧
      storableIn memory element (.address target) = .ok () ∧
      storeSlot memory (slot array index) (.address target) =
        .ok (setSlot memory (slot array index) (.address target)) ∧
      Confined [entry array index] memory
        (setSlot memory (slot array index) (.address target)) ∧
      Holds (setSlot memory (slot array index) (.address target)) array element length index
        (.address target) :=
  ⟨owned.slot_located owned.inside, storable,
    storeSlot_of_access owned.writable live.formed,
    Confined.setSlot _ (List.mem_singleton_self _) (by decide),
    ⟨owned.after_setSlot _ _, setSlot_slots_same _ _ _⟩⟩
#print axioms Owned.store

/-- Storing null into an owned element succeeds whatever the element class, confined to the
    element, and leaves it owned and holding null. -/
theorem Owned.store_null {memory : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index : Nat}
    (owned : Owned memory array element length index) :
    referenceArraySlot memory (.address array) index = .ok (slot array index, element) ∧
      storableIn memory element .null = .ok () ∧
      storeSlot memory (slot array index) .null =
        .ok (setSlot memory (slot array index) .null) ∧
      Confined [entry array index] memory (setSlot memory (slot array index) .null) ∧
      Holds (setSlot memory (slot array index) .null) array element length index .null :=
  ⟨owned.slot_located owned.inside, rfl, storeSlot_of_access owned.writable rfl,
    Confined.setSlot _ (List.mem_singleton_self _) (by decide),
    ⟨owned.after_setSlot _ _, setSlot_slots_same _ _ _⟩⟩
#print axioms Owned.store_null

/-- Storing any reference that forms and passes the covariance check, such as one to a class
    outside the model, into an owned element succeeds, confined to the element, and leaves it
    owned and holding that reference. -/
theorem Owned.store_formed {memory : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index : Nat} {value : ManagedReference}
    (owned : Owned memory array element length index)
    (formed : formObject memory value = .ok (.object value))
    (storable : storableIn memory element value = .ok ()) :
    referenceArraySlot memory (.address array) index = .ok (slot array index, element) ∧
      storableIn memory element value = .ok () ∧
      storeSlot memory (slot array index) value =
        .ok (setSlot memory (slot array index) value) ∧
      Confined [entry array index] memory (setSlot memory (slot array index) value) ∧
      Holds (setSlot memory (slot array index) value) array element length index value :=
  ⟨owned.slot_located owned.inside, storable, storeSlot_of_access owned.writable formed,
    Confined.setSlot _ (List.mem_singleton_self _) (by decide),
    ⟨owned.after_setSlot _ _, setSlot_slots_same _ _ _⟩⟩
#print axioms Owned.store_formed

/-- A live instance whose runtime type has `element` in its lineage is storable into an array of
    `element`, when both are admitted classes. -/
theorem storableIn_of_lineage {memory : Memory} {target : Reference}
    {allocation : Allocation} {type : RuntimeType} {element : CIL.Extraction.TypeExpr}
    {scope name elementScope elementName : String}
    (found : liveAllocation memory target.allocation = .ok allocation)
    (kind : allocation.kind = .object type) (identity : type.identity = .object scope name)
    (elementClass : element = .object elementScope elementName)
    (member : element ∈ type.lineage) :
    storableIn memory element (.address target) = .ok () := by
  subst elementClass
  simp only [storableIn, found, kind, identity, member, checkedAt, Except.mapError, Bind.bind,
    Except.bind, ite_true]
#print axioms storableIn_of_lineage

/-- A live instance of an admitted class whose lineage lacks `element` is not storable into an
    array of `element`: the store throws `ArrayTypeMismatchException`. -/
theorem storableIn_mismatch {memory : Memory} {target : Reference}
    {allocation : Allocation} {type : RuntimeType} {element : CIL.Extraction.TypeExpr}
    {scope name elementScope elementName : String}
    (found : liveAllocation memory target.allocation = .ok allocation)
    (kind : allocation.kind = .object type) (identity : type.identity = .object scope name)
    (elementClass : element = .object elementScope elementName)
    (outside : element ∉ type.lineage) :
    storableIn memory element (.address target) =
      .error (.thrown "System.ArrayTypeMismatchException") := by
  subst elementClass
  simp only [storableIn, found, kind, identity, outside, checkedAt, Except.mapError, Bind.bind,
    Except.bind, ite_false]
#print axioms storableIn_mismatch

/-- A readable element keeps its slot, its authority and what it holds across a call confined to
    a footprint apart from it. -/
theorem Readable.frame {footprint : List (Reference × Nat)} {before after : Memory}
    {array : Reference} {element : CIL.Extraction.TypeExpr} {length index : Nat}
    (readable : Readable before array element length index)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (slot array index) objectFieldSlot entry) :
    Readable after array element length index ∧
      of after array index = of before array index := by
  have outside := Outside.of_apart apart
  refine ⟨{ toLive := readable.toLive.of_allocation (framed.allocations _ readable.old)
              framed.grows
            inside := readable.inside
            readable := ?_ }, ?_⟩
  · rw [← readable.readable]
    exact framed.access_read (slot array index) readable.old _ _ outside
  · exact framed.slots _ readable.old _ (by simpa [slot] using outside 0 (by decide))
#print axioms Readable.frame

/-- An owned element stays owned, holding what it held, across a call confined to a footprint
    apart from it. -/
theorem Owned.frame {footprint : List (Reference × Nat)} {before after : Memory}
    {array : Reference} {element : CIL.Extraction.TypeExpr} {length index : Nat}
    (owned : Owned before array element length index) (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (slot array index) objectFieldSlot entry) :
    Holds after array element length index (of before array index) :=
  have kept := owned.toReadable.frame framed apart
  ⟨{ kept.1 with
      writable := (framed.access_write (slot array index) owned.old _ _).trans owned.writable },
    kept.2⟩
#print axioms Owned.frame

/-- An element holding `value` holds it across a call confined to a footprint apart from it. -/
theorem Holds.after_confined {footprint : List (Reference × Nat)} {before after : Memory}
    {array : Reference} {element : CIL.Extraction.TypeExpr} {length index : Nat}
    {value : ManagedReference} (held : Holds before array element length index value)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (slot array index) objectFieldSlot entry) :
    Holds after array element length index value :=
  held.2 ▸ held.1.frame framed apart
#print axioms Holds.after_confined

/-- After a call confined to element `written` of `array` that leaves it holding `value`,
    element `index` of the same array holds `value` when the indices agree and what it held
    before the call otherwise. -/
theorem Owned.across {before after : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index written : Nat} {value : ManagedReference}
    (owned : Owned before array element length index)
    (framed : Confined [entry array written] before after)
    (held : Holds after array element length written value) :
    Holds after array element length index
      (if written = index then value else of before array index) := by
  by_cases same : written = index
  · subst same
    simpa using held
  · simp only [same, ite_false]
    refine owned.frame framed fun entry member => ?_
    simp only [List.mem_singleton] at member
    subst member
    refine Or.inr ?_
    simp only [ReferenceArray.entry, ReferenceArray.slot, objectFieldSlot]
    omega
#print axioms Owned.across

/-- After a call confined to element `written` of `array`, an owned element at another index
    holds what it held before. -/
theorem Owned.across_ne {before after : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index written : Nat}
    (owned : Owned before array element length index)
    (framed : Confined [entry array written] before after) (other : written ≠ index) :
    Holds after array element length index (of before array index) := by
  refine owned.frame framed fun entry member => ?_
  simp only [List.mem_singleton] at member
  subst member
  refine Or.inr ?_
  simp only [ReferenceArray.entry, ReferenceArray.slot, objectFieldSlot]
  omega
#print axioms Owned.across_ne

/-- An element holding `value` holds it after a call confined to another element of its array. -/
theorem Holds.across_ne {before after : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index written : Nat} {value : ManagedReference}
    (held : Holds before array element length index value)
    (framed : Confined [entry array written] before after) (other : written ≠ index) :
    Holds after array element length index value :=
  held.2 ▸ held.1.across_ne framed other
#print axioms Holds.across_ne

/-- A live object that passes an array's covariance check passes it after a call confined to any
    footprint, which keeps every older allocation and so the object's class. -/
theorem storableIn_after_confined {footprint : List (Reference × Nat)} {before after : Memory}
    {element : CIL.Extraction.TypeExpr} {target : Reference}
    (storable : storableIn before element (.address target) = .ok ())
    (framed : Confined footprint before after) (old : target.allocation < before.nextIdentity) :
    storableIn after element (.address target) = .ok () := by
  rw [← storable]
  simp only [storableIn, liveAllocation, framed.allocations _ old]
#print axioms storableIn_after_confined

/-- The covariance check reads only allocations, so memory with the same allocations, such as
    after a store, decides it alike. -/
theorem storableIn_of_allocations {before after : Memory}
    (same : after.allocations = before.allocations) (element : CIL.Extraction.TypeExpr)
    (value : ManagedReference) :
    storableIn after element value = storableIn before element value := by
  cases value <;> simp only [storableIn, liveAllocation, same]
#print axioms storableIn_of_allocations

/-- A reference that forms in well-formed memory passes a covariance check after a confined call,
    such as an allocation, as it did before: it names an allocation the call keeps. -/
theorem storableIn_of_confined {footprint : List (Reference × Nat)} {before after : Memory}
    {element : CIL.Extraction.TypeExpr} {value : ManagedReference}
    (storable : storableIn before element value = .ok ())
    (framed : Confined footprint before after) (formedMemory : before.WellFormed)
    (formed : formObject before value = .ok (.object value)) :
    storableIn after element value = .ok () := by
  cases value with
  | null => rfl
  | address target =>
    exact storableIn_after_confined storable framed (formedMemory.object_below formed)
#print axioms storableIn_of_confined

/-- Every element entry of an array allocated at `memory.nextIdentity` lies in an allocation
    younger than all of `memory`'s, so a caller's footprint may forget it. -/
theorem entries_young {memory : Memory} {array : Reference}
    (fresh : (⟨memory.nextIdentity, 0⟩ : Reference) = array) (indices : List Nat) :
    ∀ written ∈ indices.map (entry array), memory.nextIdentity ≤ written.1.allocation := by
  subst fresh
  intro written member
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
  exact Nat.le_refl _
#print axioms entries_young

/-- A slot store keeps every allocation, so what reads only allocations reads alike after it. -/
theorem allocations_of_setSlot {before after : Memory} {field : Reference}
    {value : ManagedReference} (wrote : setSlot before field value = after) :
    after.allocations = before.allocations := by
  subst wrote
  rfl
#print axioms allocations_of_setSlot

/-- A live array stays live, of the same class and length, across a confined call. -/
theorem Live.after_confined {footprint : List (Reference × Nat)} {before after : Memory}
    {array : Reference} {element : CIL.Extraction.TypeExpr} {length : Nat}
    (live : Live before array element length) (framed : Confined footprint before after) :
    Live after array element length :=
  live.of_allocation (framed.allocations _ live.old) framed.grows
#print axioms Live.after_confined

/-- An array is no object with a located field of a class: an array's lineage is its own array
    type, which no class owns a field of. -/
theorem Live.field_ne {memory : Memory} {array object field : Reference}
    {element owner : CIL.Extraction.TypeExpr} {length offset : Nat} {scope name : String}
    (live : Live memory array element length)
    (located : objectFieldAddress memory (.address object) owner offset = .ok field)
    (ownerClass : owner = .object scope name) :
    object.allocation ≠ array.allocation := by
  subst ownerClass
  intro same
  have array_located := live.located
  cases found : liveAllocation memory array.allocation with
  | error fault =>
    simp only [referenceArrayOf, found, checkedAt, Except.mapError, Bind.bind, Except.bind]
      at array_located
    cases array_located
  | ok allocation =>
    simp only [referenceArrayOf, found, checkedAt, Except.mapError, Bind.bind, Except.bind]
      at array_located
    split at array_located
    · rename_i kind
      simp only [objectFieldAddress, same, found, kind, checkedAt, Except.mapError, Bind.bind,
        Except.bind, RuntimeType.lineage] at located
      split at located <;> cases located
    · cases array_located
#print axioms Live.field_ne

/-- Storage in another allocation is apart from the one entry of a footprint. -/
theorem apart_single {address : Reference} {width : Nat} {entry : Reference × Nat}
    (other : address.allocation ≠ entry.1.allocation) :
    ∀ written ∈ [entry], Apart address width written := by
  intro written member
  simp only [List.mem_singleton] at member
  subst member
  exact Or.inl other
#print axioms apart_single

/-- Element `index` is `Readable` and holds `value`: what a load reads after earlier writes. -/
def Reads (memory : Memory) (array : Reference) (element : CIL.Extraction.TypeExpr)
    (length index : Nat) (value : ManagedReference) : Prop :=
  Readable memory array element length index ∧ of memory array index = value

/-- A readable element reads what it holds. -/
theorem Readable.reads {memory : Memory} {array : Reference} {element : CIL.Extraction.TypeExpr}
    {length index : Nat} (readable : Readable memory array element length index) :
    Reads memory array element length index (of memory array index) :=
  ⟨readable, rfl⟩
#print axioms Readable.reads

/-- An owned element holds what it holds. -/
theorem Owned.holds {memory : Memory} {array : Reference} {element : CIL.Extraction.TypeExpr}
    {length index : Nat} (owned : Owned memory array element length index) :
    Holds memory array element length index (of memory array index) :=
  ⟨owned, rfl⟩
#print axioms Owned.holds

/-- An element read as `value` reads it across a call confined to a footprint apart from it. -/
theorem Reads.after_confined {footprint : List (Reference × Nat)} {before after : Memory}
    {array : Reference} {element : CIL.Extraction.TypeExpr} {length index : Nat}
    {value : ManagedReference} (reads : Reads before array element length index value)
    (framed : Confined footprint before after)
    (apart : ∀ entry ∈ footprint, Apart (slot array index) objectFieldSlot entry) :
    Reads after array element length index value :=
  have kept := reads.1.frame framed apart
  ⟨kept.1, kept.2.trans reads.2⟩
#print axioms Reads.after_confined

/-- An element read as `value` reads it after a call confined to another element of its array. -/
theorem Reads.across_ne {before after : Memory} {array : Reference}
    {element : CIL.Extraction.TypeExpr} {length index written : Nat} {value : ManagedReference}
    (reads : Reads before array element length index value)
    (framed : Confined [entry array written] before after) (other : written ≠ index) :
    Reads after array element length index value := by
  refine reads.after_confined framed fun entry member => ?_
  simp only [List.mem_singleton] at member
  subst member
  refine Or.inr ?_
  simp only [ReferenceArray.entry, ReferenceArray.slot, objectFieldSlot]
  omega
#print axioms Reads.across_ne

/-- What a load of an element read as a reference that forms steps with: the slot is located,
    and the load pushes that reference. -/
theorem Reads.facts {memory : Memory} {array : Reference} {element : CIL.Extraction.TypeExpr}
    {length index : Nat} {value : ManagedReference}
    (reads : Reads memory array element length index value)
    (formed : formObject memory value = .ok (.object value)) :
    referenceArraySlot memory (.address array) index = .ok (slot array index, element) ∧
      loadSlot memory (slot array index) = .ok (.object value) := by
  refine ⟨reads.1.slot_located reads.1.inside, ?_⟩
  rw [reads.1.load, reads.2]
  exact formed
#print axioms Reads.facts

/-- An element holding `value` reads it. -/
theorem Holds.reads {memory : Memory} {array : Reference} {element : CIL.Extraction.TypeExpr}
    {length index : Nat} {value : ManagedReference}
    (held : Holds memory array element length index value) :
    Reads memory array element length index value :=
  ⟨held.1.toReadable, held.2⟩
#print axioms Holds.reads

/-- A store into an element of an array allocated at or above `watermark` keeps all memory
    below it, so a method that fills an array it created changes nothing its caller held. -/
theorem setSlot_below {watermark : Nat} (memory : Memory) {field : Reference}
    (fresh : watermark ≤ field.allocation) (value : ManagedReference) :
    MemoryBelow watermark memory (setSlot memory field value) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun identity below offset => by
    simp [CIL.Safety.setSlot, show identity ≠ field.allocation by omega]⟩
#print axioms setSlot_below

/-- Memory that keeps every allocation below a watermark finds each of them live as before. -/
theorem liveAllocation_below {watermark : Nat} {before after : Memory} {identity : Nat}
    (preserved : MemoryBelow watermark before after) (old : identity < watermark) :
    liveAllocation after identity = liveAllocation before identity := by
  simp only [liveAllocation, preserved.allocations _ old]
#print axioms liveAllocation_below

/-- A fresh array of `length` elements is live, and every element inside it is owned and holds
    null. -/
theorem fresh (memory : Memory) (element : CIL.Extraction.TypeExpr) {length index : Nat}
    (bounded : objectFieldSlot * length < nativeLimit) (inside : index < length) :
    Holds (objectMemory memory (referenceArrayType element) (objectFieldSlot * length))
      ⟨memory.nextIdentity, 0⟩ element length index .null := by
  have fits : objectFieldSlot * index + objectFieldSlot ≤ objectFieldSlot * length := by
    simp only [objectFieldSlot]
    omega
  have live : Live (objectMemory memory (referenceArrayType element) (objectFieldSlot * length))
      ⟨memory.nextIdentity, 0⟩ element length := by
    constructor
    · simp [referenceArrayOf, liveAllocation, objectMemory, referenceArrayType, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
        Nat.mul_div_cancel_left length (show 0 < objectFieldSlot by decide)]
    · simp [objectMemory]
  exact ⟨⟨⟨live, inside, objectMemory_access memory _ bounded fits (by decide) false⟩,
    objectMemory_access memory _ bounded fits (by decide) true⟩, by simp [of, objectMemory]⟩
#print axioms fresh

end ReferenceArray
end CIL.Safety
