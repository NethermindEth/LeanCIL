import CIL.Layout
import CIL.Features

/-!
# Aggregate layouts from raw metadata

The extractor emits both raw struct metadata (field types, packing, explicit offsets and
declared size) and the computed layout table its instructions use. This file recomputes
CoreCLR's layout of reference-free structs from the raw metadata alone, so `LayoutsValid`
binds every emitted field offset and struct size to an independent calculation.
-/

namespace CIL.Extraction

/-- Storage tags retain metadata distinctions before layout computation. -/
inductive FieldType where
  | signed8 | unsigned8 | boolean | signed16 | unsigned16 | character
  | signed32 | unsigned32 | signed64 | unsigned64 | nativeInt | nativeUInt
  | vector128 | vector256
  | aggregate (index : Nat)
  deriving DecidableEq, Repr

/-- One struct field as declared: its type and, for explicit layout, its byte offset. -/
structure RawField where
  type : FieldType
  offset : Option Nat := none
  deriving DecidableEq, Repr

/-- Children precede parents; indices refer to raw metadata, not computed sizes. -/
structure RawLayout where
  identity : String := ""
  explicit : Bool
  packing : Int
  declaredSize : Int
  fields : List RawField
  /-- Auto layout; CoreCLR keeps declaration order only among fields of equal width. -/
  auto : Bool := false
  /-- Direct interface identities, used when checking closed generic constraints. -/
  interfaces : List String := []
  deriving DecidableEq, Repr

/-- A struct's field offsets and size, with the alignment it imposes when nested. -/
structure ComputedLayout where
  layout : AggregateLayout
  alignment : Nat
  deriving DecidableEq, Repr

/-- Width, natural alignment and whether the field is a nested struct. A nested struct
    must already be in `previous`, which rules out forward references. -/
private def fieldStorage (previous : Array ComputedLayout) (architecture : Architecture) :
    FieldType → Option (Nat × Nat × Bool)
  | .signed8 | .unsigned8 | .boolean => some (1, 1, false)
  | .signed16 | .unsigned16 | .character => some (2, 2, false)
  | .signed32 | .unsigned32 => some (4, 4, false)
  | .signed64 | .unsigned64 | .nativeInt | .nativeUInt => some (8, 8, false)
  | .vector128 => some (16, 16, false)
  | .vector256 => some (32, if architecture == .arm64 then 16 else 32, false)
  | .aggregate index => do
    let child ← previous[index]?
    return (child.layout.size, child.alignment, true)

/-- Byte width of a primitive integer, `bool` or `char` field; vectors and structs have none. -/
def primitiveFieldWidth : FieldType → Option Nat
  | .signed8 | .unsigned8 | .boolean => some 1
  | .signed16 | .unsigned16 | .character => some 2
  | .signed32 | .unsigned32 => some 4
  | .signed64 | .unsigned64 | .nativeInt | .nativeUInt => some 8
  | _ => none

/-- A primitive's width is the width and natural alignment the layout calculation gives it,
    so `sizeof` and `initobj` checks agree with field layout on every architecture. -/
theorem primitiveFieldWidth_layout {kind : FieldType} {width : Nat}
    (primitive : primitiveFieldWidth kind = some width)
    (previous : Array ComputedLayout) (architecture : Architecture) :
    fieldStorage previous architecture kind = some (width, width, false) := by
  cases kind <;> simp [primitiveFieldWidth] at primitive <;> subst primitive <;> rfl

#print axioms primitiveFieldWidth_layout

/-- The least multiple of `alignment` that is at least `size`. -/
private def alignUp (size alignment : Nat) : Nat :=
  (size + alignment - 1) / alignment * alignment

/-- Auto layout is admitted only where it coincides with sequential placement. -/
private def autoSequential (previous : Array ComputedLayout) (raw : RawLayout) : Bool :=
  !raw.explicit && raw.packing ≤ 0 && raw.declaredSize ≤ 0 &&
  match raw.fields.mapM (fun field => do
      if field.offset.isSome || field.type == FieldType.vector128 ||
          field.type == FieldType.vector256 then none else
        let (width, _, aggregate) ← fieldStorage previous .scalar field.type
        if aggregate then none else some width) with
  | some (width :: widths) => widths.all (· == width)
  | _ => false

/-- Recompute CoreCLR reference-free 64-bit layout from ordered metadata fields. -/
def computeLayout (previous : Array ComputedLayout) (raw : RawLayout)
    (architecture : Architecture := .scalar) : Option ComputedLayout := do
  if raw.packing ∉ [-1, 0, 1, 2, 4, 8, 16, 32, 64, 128] then none
  else if raw.declaredSize < -1 || raw.declaredSize > 65536 then none
  else if raw.explicit && raw.declaredSize ≤ 0 then none
  else if raw.auto && !autoSequential previous raw then none
  else
    let pack := if raw.packing ≤ 0 then 64 else raw.packing.toNat
    let (size, alignment, fields) ← raw.fields.foldlM (init := (0, 1, ([] : List FieldLayout)))
        fun (size, alignment, fields) field => do
      if field.type == .vector256 && pack > 16 && architecture == .scalar then none else do
        let (width, natural, aggregate) ← fieldStorage previous architecture field.type
        let aligned := min pack natural
        if aligned = 0 then none else do
          let offset ← if raw.explicit then field.offset else
            if field.offset.isSome then none else some (alignUp size aligned)
          if offset + width > 65536 ||
              (raw.explicit && offset + width > raw.declaredSize.toNat) then none else
            return (max size (offset + width), max alignment aligned,
              fields ++ [⟨offset, width, aggregate⟩])
    let finalSize := max 1
      (if raw.declaredSize > 0 then max size raw.declaredSize.toNat else alignUp size alignment)
    if finalSize > 65536 then none else
      return ⟨⟨finalSize, fields⟩, alignment⟩

/-- Reject forward references and cycles by computing strictly in metadata-table order. -/
def computeLayouts (raw : List RawLayout) (architecture : Architecture := .scalar) :
    Option (Array ComputedLayout) :=
  raw.foldlM (init := #[]) fun previous entry => do
    return previous.push (← computeLayout previous entry architecture)

/-- The claimed table is checked against a separate raw metadata table. -/
def LayoutsValid (raw : List RawLayout) (claimed : Array ComputedLayout)
    (architecture : Architecture := .scalar) : Prop :=
  computeLayouts raw architecture = some claimed ∧ ∀ item ∈ claimed.toList, item.layout.Valid

instance (raw : List RawLayout) (claimed : Array ComputedLayout) (architecture : Architecture) :
    Decidable (LayoutsValid raw claimed architecture) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `LayoutsValid` as a Boolean, for checking by evaluation. -/
def validateLayouts (raw : List RawLayout) (claimed : Array ComputedLayout)
    (architecture : Architecture := .scalar) : Bool :=
  decide (LayoutsValid raw claimed architecture)

theorem validateLayouts_sound {raw : List RawLayout} {claimed : Array ComputedLayout}
    {architecture : Architecture}
    (checked : validateLayouts raw claimed architecture = true) :
    LayoutsValid raw claimed architecture :=
  of_decide_eq_true checked

/-- Every field of a validated layout lies inside its struct. -/
theorem validated_layout_within_bounds {raw : List RawLayout} {claimed : Array ComputedLayout}
    {architecture : Architecture}
    (checked : LayoutsValid raw claimed architecture) (item : ComputedLayout)
    (member : item ∈ claimed.toList) (field : FieldLayout) (present : field ∈ item.layout.fields) :
    field.offset + field.width ≤ item.layout.size :=
  field_within_layout item.layout (checked.2 item member) field present

end CIL.Extraction
