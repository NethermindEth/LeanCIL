import Std

namespace CIL

/-- A reference-free field admitted by the initial extractor. Offsets are bytes,
    independent of field order; explicit-layout overlaps are permitted. -/
structure FieldLayout where
  offset : Nat
  width : Nat
  deriving DecidableEq, Repr

structure AggregateLayout where
  size : Nat
  fields : List FieldLayout
  deriving DecidableEq, Repr

def AggregateLayout.Valid (layout : AggregateLayout) : Prop :=
  0 < layout.size ∧ layout.size < 2^64 ∧
  ∀ field ∈ layout.fields, field.width ∈ [1, 2, 4, 8] ∧ field.offset + field.width ≤ layout.size

instance aggregateLayoutDecidable (layout : AggregateLayout) : Decidable layout.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem field_within_layout (layout : AggregateLayout) (valid : layout.Valid)
    (field : FieldLayout) (member : field ∈ layout.fields) :
    field.offset + field.width ≤ layout.size := (valid.2.2 field member).2

end CIL
