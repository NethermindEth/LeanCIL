import Std

/-!
# Aggregate layouts

The byte layout of a value type as the extractor admits it: a size and the offset and
width of each field. `AggregateLayout.Valid` is the well-formedness condition that
`LayoutsValid` requires of every computed layout.
-/

namespace CIL

/-- A reference-free field admitted by the initial extractor. Offsets are bytes,
    independent of field order; explicit-layout overlaps are permitted. -/
structure FieldLayout where
  offset : Nat
  width : Nat
  aggregate : Bool := false
  deriving DecidableEq, Repr

/-- The byte size of a value type and its fields. -/
structure AggregateLayout where
  size : Nat
  fields : List FieldLayout
  deriving DecidableEq, Repr

/-- A nonempty layout smaller than `2^64` bytes in which every field lies inside it; a scalar
    field is 1, 2, 4, 8, 16 or 32 bytes wide and a nested aggregate is nonempty. -/
def AggregateLayout.Valid (layout : AggregateLayout) : Prop :=
  0 < layout.size ∧ layout.size < 2^64 ∧
  ∀ field ∈ layout.fields,
    (if field.aggregate then 0 < field.width else field.width ∈ [1, 2, 4, 8, 16, 32]) ∧
    field.offset + field.width ≤ layout.size

instance aggregateLayoutDecidable (layout : AggregateLayout) : Decidable layout.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem field_within_layout (layout : AggregateLayout) (valid : layout.Valid)
    (field : FieldLayout) (member : field ∈ layout.fields) :
    field.offset + field.width ≤ layout.size := (valid.2.2 field member).2

end CIL
