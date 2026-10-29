import CIL.Layout
import CIL.Features
import CIL.TypeExpr

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

/-- Original generic owner metadata and its supplied closed arguments. -/
structure GenericLayout where
  owner : TypeExpr
  arity : Nat
  arguments : List TypeExpr
  fields : List TypeExpr
  constraints : List (Nat × List String)
  deriving DecidableEq, Repr

/-- The closed owner expression preserves argument order and exact scoped type identities. -/
def GenericLayout.closedType (layout : GenericLayout) : TypeExpr :=
  layout.arguments.foldl TypeExpr.apply layout.owner

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
  /-- Closed sequential generic layouts additionally prove their original field substitutions. -/
  generic : Option GenericLayout := none
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

/-- Compute one field's placement without extending the field list. -/
private def placeField (previous : Array ComputedLayout) (raw : RawLayout)
    (architecture : Architecture) (pack size alignment : Nat) (field : RawField) :
    Option (Nat × Nat × FieldLayout) := do
  if field.type == .vector256 && pack > 16 && architecture == .scalar then none else do
    let (width, natural, aggregate) ← fieldStorage previous architecture field.type
    let aligned := min pack natural
    if aligned = 0 then none else do
      let offset ← if raw.explicit then field.offset else
        if field.offset.isSome then none else some (alignUp size aligned)
      if offset + width > 65536 ||
          (raw.explicit && offset + width > raw.declaredSize.toNat) then none else
        return (max size (offset + width), max alignment aligned, ⟨offset, width, aggregate⟩)

/-- Accumulate checked placements in reverse order and restore declaration order once. -/
private def layoutFields (step : Nat → Nat → RawField → Option (Nat × Nat × FieldLayout)) :
    List RawField → Nat → Nat → List FieldLayout → Option (Nat × Nat × List FieldLayout)
  | [], size, alignment, fields => some (size, alignment, fields.reverse)
  | field :: rest, size, alignment, fields => do
    let (size, alignment, placed) ← step size alignment field
    layoutFields step rest size alignment (placed :: fields)

/-- Reverse accumulation preserves ordered placements and every field-computation failure. -/
private theorem layoutFields_eq_fold
    (step : Nat → Nat → RawField → Option (Nat × Nat × FieldLayout))
    (raw : List RawField) (size alignment : Nat) (fields : List FieldLayout) :
    layoutFields step raw size alignment fields =
      raw.foldlM (init := (size, alignment, fields.reverse))
        (fun (size, alignment, fields) field => do
          let (size, alignment, placed) ← step size alignment field
          return (size, alignment, fields ++ [placed])) := by
  induction raw generalizing size alignment fields with
  | nil => rfl
  | cons field rest ih =>
    simp only [layoutFields, List.foldlM_cons]
    cases found : step size alignment field with
    | none => rfl
    | some result =>
      rcases result with ⟨size, alignment, placed⟩
      simpa only [Bind.bind, Option.bind, Pure.pure, List.reverse_cons] using
        ih size alignment (placed :: fields)

#print axioms layoutFields_eq_fold

/-- Recompute CoreCLR reference-free 64-bit layout from ordered metadata fields. -/
def computeLayout (previous : Array ComputedLayout) (raw : RawLayout)
    (architecture : Architecture := .scalar) : Option ComputedLayout := do
  if raw.packing ∉ [-1, 0, 1, 2, 4, 8, 16, 32, 64, 128] then none
  else if raw.declaredSize < -1 || raw.declaredSize > 65536 then none
  else if raw.explicit && raw.declaredSize ≤ 0 then none
  else if raw.auto && !autoSequential previous raw then none
  else
    let pack := if raw.packing ≤ 0 then 64 else raw.packing.toNat
    let (size, alignment, fields) ← layoutFields (placeField previous raw architecture pack)
      raw.fields 0 1 []
    let finalSize := max 1
      (if raw.declaredSize > 0 then max size raw.declaredSize.toNat else alignUp size alignment)
    if finalSize > 65536 then none else
      return ⟨⟨finalSize, fields⟩, alignment⟩
/-- Distribute optional sequencing over a field-validation branch. -/
private theorem bind_if (condition : Prop) [Decidable condition] (left right : Option α)
    (next : α → Option β) :
    (if condition then left else right).bind next =
      if condition then left.bind next else right.bind next := by
  split <;> rfl

#print axioms bind_if

/-- Extending an ordered accumulator after placement is the original field step. -/
private theorem placeField_append (previous : Array ComputedLayout) (raw : RawLayout)
    (architecture : Architecture) (pack size alignment : Nat) (fields : List FieldLayout)
    (field : RawField) :
    (do
      let (size, alignment, placed) ← placeField previous raw architecture pack size alignment field
      return (size, alignment, fields ++ [placed])) = (do
      if field.type == .vector256 && pack > 16 && architecture == .scalar then none else do
        let (width, natural, aggregate) ← fieldStorage previous architecture field.type
        let aligned := min pack natural
        if aligned = 0 then none else do
          let offset ← if raw.explicit then field.offset else
            if field.offset.isSome then none else some (alignUp size aligned)
          if offset + width > 65536 ||
              (raw.explicit && offset + width > raw.declaredSize.toNat) then none else
            return (max size (offset + width), max alignment aligned,
              fields ++ [⟨offset, width, aggregate⟩])) := by
  unfold placeField
  simp only [Option.bind_eq_bind, Option.pure_def, bind_if, Option.bind_assoc,
    Option.bind_none, Option.bind_some]

#print axioms placeField_append

/-- Linear field construction is exactly the former append-based layout computation. -/
theorem computeLayout_eq_append (previous : Array ComputedLayout) (raw : RawLayout)
    (architecture : Architecture) : computeLayout previous raw architecture = do
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
      return ⟨⟨finalSize, fields⟩, alignment⟩ := by
  simp only [computeLayout, layoutFields_eq_fold, List.reverse_nil, placeField_append]

#print axioms computeLayout_eq_append

/-- Resolve a closed generic aggregate by its independently serialized owner and arguments. -/
def genericLayoutIndex (layouts : List RawLayout) (type : TypeExpr) : Option Nat :=
  layouts.findIdx? fun layout => layout.generic.any (fun generic => generic.closedType == type)

/-- Resolve specialized storage tokens after substituting owner or method parameters. -/
def closeLayoutType (layouts : List RawLayout) : TypeExpr → TypeExpr
  | .byref type => .byref (closeLayoutType layouts type)
  | .pointer type => .pointer (closeLayoutType layouts type)
  | .array type => .array (closeLayoutType layouts type)
  | .apply owner argument =>
    let type := .apply (closeLayoutType layouts owner) (closeLayoutType layouts argument)
    match genericLayoutIndex layouts type with
    | some index => .aggregate (layouts[index]?.map RawLayout.identity |>.getD "") index
    | none => type
  | type => type

/-- Field storage is derived from substituted metadata, including exact aggregate identities. -/
private def genericFieldType (layouts : List RawLayout) : TypeExpr → Option FieldType
  | .enum _ underlying => genericFieldType layouts underlying
  | type =>
  match closeLayoutType layouts type with
  | .aggregate identity index =>
    if (layouts[index]?).any (·.identity == identity) then some (.aggregate index) else none
  | .atom scope name => if scope != runtimeScope then none else match name with
    | "System.SByte" => some .signed8 | "System.Byte" => some .unsigned8
    | "System.Boolean" => some .boolean | "System.Char" => some .character
    | "System.Int16" => some .signed16 | "System.UInt16" => some .unsigned16
    | "System.Int32" => some .signed32 | "System.UInt32" => some .unsigned32
    | "System.Int64" => some .signed64 | "System.UInt64" => some .unsigned64
    | "System.IntPtr" => some .nativeInt | "System.UIntPtr" => some .nativeUInt
    | _ => none
  | .apply (.constructor scope name) (.atom elementScope element) =>
    if scope != "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, " ++
        "PublicKeyToken=cc7b13ffcd2ddd51" || elementScope != runtimeScope ||
        element ∉ ["System.Byte", "System.Int32", "System.UInt32",
          "System.Int64", "System.UInt64"] then none else
    if name == "System.Runtime.Intrinsics.Vector128`1" then some .vector128
    else if name == "System.Runtime.Intrinsics.Vector256`1" then some .vector256 else none
  | _ => none

/-- Closed generic identities retain the scope and ordering of every supported argument. -/
def genericOwnerIdentity (owner : TypeExpr) (arguments : List TypeExpr) : Option String := do
      let .constructor scope name := owner | none
      let names ← arguments.mapM fun argument => match argument with
        | .atom scope name => some (scope ++ "::" ++ name)
        | .enum identity _ | .aggregate identity _ =>
          some identity
        | .apply (.constructor scope name) (.atom elementScope element) =>
          some (scope ++ "::" ++ name ++ "<" ++ elementScope ++ "::" ++ element ++ ">")
        | _ => none
      return scope ++ "::" ++ name ++ "<" ++ String.intercalate "," names ++ ">"

/-- Generic layouts cannot replace their argument ordering or original field storage. -/
def genericLayoutValid (layouts : List RawLayout) (layout : RawLayout) : Bool :=
  match layout.generic with
  | none => true
  | some generic =>
    genericOwnerIdentity generic.owner generic.arguments == some layout.identity &&
      !layout.explicit && !layout.auto && generic.arity > 0 &&
      generic.arguments.length == generic.arity &&
      generic.constraints.length == generic.arity && generic.constraints.all (fun constraint =>
        constraint.1 &&& 56 == constraint.1 && constraint.2.all (fun type =>
          type == runtimeScope ++ "::System.ValueType" ||
          type == runtimeScope ++ "::System.Runtime.InteropServices.UnmanagedType!" ++
            runtimeScope ++ "::System.ValueType")) &&
      generic.arguments.all (fun type => substituteType [] type == some type &&
        (genericFieldType layouts type).isSome) &&
      (generic.fields.mapM fun type => do
        genericFieldType layouts (← substituteType generic.arguments type)) ==
          some (layout.fields.map RawField.type)

/-- Reject forward references and cycles by computing strictly in metadata-table order. -/
def computeLayouts (raw : List RawLayout) (architecture : Architecture := .scalar) :
    Option (Array ComputedLayout) :=
  if !raw.all (genericLayoutValid raw) then none else
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
