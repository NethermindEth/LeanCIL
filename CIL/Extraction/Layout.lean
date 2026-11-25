import CIL.Layout
import CIL.Features
import CIL.TypeExpr
import CIL.Extraction.FlowIndex
import Std.Data.TreeSet.Lemmas
import Lean.Elab.Tactic.BuiltinTactic

/-!
# Aggregate layouts from raw metadata

The extractor emits both raw struct metadata (field types, packing, explicit offsets and
declared size) and the computed layout table its instructions use. This file recomputes
CoreCLR's layout of reference-free structs from the raw metadata alone, so `LayoutsValid`
binds every emitted field offset and struct size to an independent calculation.
`layoutsValidIndexed` checks distinct identities by their UTF-8 bytes and reads both tables
through indexes built once. The `Decidable` instance of `LayoutsValid` runs it.
-/

namespace CIL.Extraction

/-- The integer element types a struct's vector field may declare, named by their field kind. -/
inductive VectorLane where
  | unsigned8 | signed32 | unsigned32 | signed64 | unsigned64
  deriving DecidableEq, Repr

/-- Storage tags retain metadata distinctions before layout computation: a vector field's element
    type as its lane, a nested struct as its layout index. -/
inductive FieldType where
  | signed8 | unsigned8 | boolean | signed16 | unsigned16 | character
  | signed32 | unsigned32 | signed64 | unsigned64 | nativeInt | nativeUInt
  | vector128 (lane : VectorLane) | vector256 (lane : VectorLane)
  | aggregate (index : Nat)
  deriving DecidableEq, Repr

/-- The field storage of a primitive; `none` for `Single` and `Double`, which no struct field of
    the model holds. -/
def _root_.CIL.PrimitiveType.fieldType? : PrimitiveType → Option FieldType
  | .sbyte => some .signed8 | .byte => some .unsigned8 | .boolean => some .boolean
  | .int16 => some .signed16 | .uint16 => some .unsigned16 | .char => some .character
  | .int32 => some .signed32 | .uint32 => some .unsigned32
  | .int64 => some .signed64 | .uint64 => some .unsigned64
  | .intPtr => some .nativeInt | .uintPtr => some .nativeUInt
  | .single | .double => none

/-- The exact primitive runtime names and their field storage. -/
private def primitiveFields : List (Prod String FieldType) :=
  [("System.SByte", .signed8), ("System.Byte", .unsigned8), ("System.Boolean", .boolean),
    ("System.Int16", .signed16), ("System.UInt16", .unsigned16), ("System.Char", .character),
    ("System.Int32", .signed32), ("System.UInt32", .unsigned32), ("System.Int64", .signed64),
    ("System.UInt64", .unsigned64), ("System.IntPtr", .nativeInt), ("System.UIntPtr", .nativeUInt)]

/-- Reversed UTF-8 bytes preserve every character and expose primitive-name suffixes first. -/
private def storageNameBytes (name : String) : List UInt8 := name.toByteArray.data.toList.reverse

/-- Byte-name equality uses structural decisions without order-package proof dependencies. -/
private def storageBytesEqual (left right : List UInt8) : Bool :=
  @decide (left = right) (@List.hasDecEq UInt8 UInt8.decEq left right)

/-- Primitive name bytes are materialized so a lookup never encodes the fixed names. -/
private def primitiveNameBytes : List (List UInt8) := by
  run_tac do
    let expression <- Lean.Elab.Term.elabTerm
      (<- `(primitiveFields.map fun entry => storageNameBytes entry.1)) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expression <- Lean.instantiateMVars expression
    let values <- unsafe Lean.Meta.evalExpr (List (List UInt8))
      (<- Lean.Meta.inferType expression) expression
    Lean.Elab.Tactic.closeMainGoal `primitiveNameBytes (Lean.toExpr values)

/-- The materialized bytes spell exactly the primitive field names. -/
private theorem primitiveNameBytes_eq :
    primitiveNameBytes = primitiveFields.map (fun entry => storageNameBytes entry.1) := by
  decide +kernel
#print axioms primitiveNameBytes_eq

/-- Byte equality agrees with string equality for all metadata names. -/
private theorem storageNameBytes_beq (left right : String) :
    storageBytesEqual (storageNameBytes left) (storageNameBytes right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [storageBytesEqual, storageNameBytes, decide_eq_true_eq, beq_iff_eq,
    List.reverse_inj, Array.toList_inj]
  constructor
  . intro equal
    exact String.toByteArray_inj.mp (ByteArray.ext equal)
  . intro equal
    cases equal
    rfl
#print axioms storageNameBytes_beq

/-- The field type of a primitive runtime type, by its exact UTF-8 name. -/
def primitiveField (name : String) : Option FieldType :=
  ((primitiveNameBytes.zip (primitiveFields.map Prod.snd)).find?
    fun entry => storageBytesEqual (storageNameBytes name) entry.1).map Prod.snd

/-- info: 'CIL.Extraction.primitiveField' does not depend on any axioms -/
#guard_msgs in
#print axioms primitiveField

/-- Primitive byte lookup gives exactly the field selected by the runtime name. -/
private theorem primitiveField_eq (name : String) : primitiveField name = (match name with
    | "System.SByte" => some .signed8 | "System.Byte" => some .unsigned8
    | "System.Boolean" => some .boolean | "System.Int16" => some .signed16
    | "System.UInt16" => some .unsigned16 | "System.Char" => some .character
    | "System.Int32" => some .signed32 | "System.UInt32" => some .unsigned32
    | "System.Int64" => some .signed64 | "System.UInt64" => some .unsigned64
    | "System.IntPtr" => some .nativeInt | "System.UIntPtr" => some .nativeUInt
    | _ => none) := by
  simp only [primitiveField, primitiveNameBytes_eq, primitiveFields, List.map_cons,
    List.map_nil, List.zip_cons_cons, List.zip_nil_left, List.find?_cons, List.find?_nil,
    storageNameBytes_beq]
  repeat' (split <;> simp_all)
#print axioms primitiveField_eq

/-- A primitive's typed storage is the storage its runtime name selected, for every primitive. -/
theorem _root_.CIL.PrimitiveType.fieldType?_eq_primitiveField (type : PrimitiveType) :
    type.fieldType? = primitiveField type.display := by
  cases type <;> rfl
#print axioms CIL.PrimitiveType.fieldType?_eq_primitiveField

/-- The field kind of an enum whose immediate underlying type is a runtime integer primitive. -/
def enumUnderlyingField : TypeExpr -> Option FieldType
  | .primitive type =>
    type.fieldType?.filter fun kind => match kind with
      | .signed8 | .unsigned8 | .signed16 | .unsigned16 | .signed32 | .unsigned32
      | .signed64 | .unsigned64 => true
      | _ => false
  | _ => none

/-- The lane of a vector whose elements have field kind `kind`; `none` for a kind no vector
    field holds. -/
def VectorLane.ofField? : FieldType → Option VectorLane
  | .unsigned8 => some .unsigned8
  | .signed32 => some .signed32
  | .unsigned32 => some .unsigned32
  | .signed64 => some .signed64
  | .unsigned64 => some .unsigned64
  | _ => none

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

mutual

/-- A closed value argument, preserving element codes and the name columns of every named type. -/
inductive LayoutArgument where
  | primitive (code : Nat)
  | named (scope : String) (levels : List TypeLevel)
  | instanceType (scope : String) (levels : List TypeLevel) (arguments : LayoutArguments)
  deriving DecidableEq, Repr

/-- The arguments of a generic layout in CLI signature order. -/
inductive LayoutArguments where
  | nil
  | cons (head : LayoutArgument) (tail : LayoutArguments)
  deriving DecidableEq, Repr

end

/-- The type at a layout index, including the scoped spelling consumed by existing methods. -/
structure LayoutIdentity where
  spelling : String
  levels : List TypeLevel
  arguments : Option LayoutArguments
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
  /-- Byref-like structs cannot be elements of heap arrays. -/
  byRefLike : Bool := false
  /-- Direct interface identities, used when checking closed generic constraints. -/
  interfaces : List String := []
  /-- Closed sequential generic layouts additionally prove their original field substitutions. -/
  generic : Option GenericLayout := none
  /-- Physical namespace and simple name of the definition or generic constructor at each level. -/
  declaration : List TypeLevel := []
  /-- Closed type arguments for a constructed layout, including platform aggregates. -/
  genericArguments : Option LayoutArguments := none
  deriving DecidableEq, Repr

/-- The declarations and closed arguments in program layout order. -/
def layoutDeclarations (rows : List RawLayout) : Array LayoutIdentity :=
  (rows.map fun row => ⟨row.identity, row.declaration, row.genericArguments⟩).toArray

/-- A struct's field offsets and size, with the alignment it imposes when nested. -/
structure ComputedLayout where
  layout : AggregateLayout
  alignment : Nat
  deriving DecidableEq, Repr

/-- Width, natural alignment and whether the field is a nested struct. A nested struct must be
    found by `previous`, which callers limit to earlier entries to rule out forward references. -/
private def fieldStorage (previous : Nat → Option ComputedLayout) (architecture : Architecture) :
    FieldType → Option (Nat × Nat × Bool)
  | .signed8 | .unsigned8 | .boolean => some (1, 1, false)
  | .signed16 | .unsigned16 | .character => some (2, 2, false)
  | .signed32 | .unsigned32 => some (4, 4, false)
  | .signed64 | .unsigned64 | .nativeInt | .nativeUInt => some (8, 8, false)
  | .vector128 _ => some (16, 16, false)
  | .vector256 _ => some (32, if architecture == .arm64 then 16 else 32, false)
  | .aggregate index => do
    let child ← previous index
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
    (previous : Nat → Option ComputedLayout) (architecture : Architecture) :
    fieldStorage previous architecture kind = some (width, width, false) := by
  cases kind <;> simp [primitiveFieldWidth] at primitive <;> subst primitive <;> rfl

#print axioms primitiveFieldWidth_layout

/-- The least multiple of `alignment` that is at least `size`. -/
private def alignUp (size alignment : Nat) : Nat :=
  (size + alignment - 1) / alignment * alignment

/-- Auto layout is admitted only where it coincides with sequential placement. -/
private def autoSequential (previous : Nat → Option ComputedLayout) (raw : RawLayout) : Bool :=
  !raw.explicit && raw.packing ≤ 0 && raw.declaredSize ≤ 0 &&
  match raw.fields.mapM (fun field => do
      if field.offset.isSome || (field.type matches .vector128 _ | .vector256 _) then none else
        let (width, _, aggregate) ← fieldStorage previous .scalar field.type
        if aggregate then none else some width) with
  | some (width :: widths) => widths.all (· == width)
  | _ => false

/-- Compute one field's placement without extending the field list. -/
private def placeField (previous : Nat → Option ComputedLayout) (raw : RawLayout)
    (architecture : Architecture) (pack size alignment : Nat) (field : RawField) :
    Option (Nat × Nat × FieldLayout) := do
  if (field.type matches .vector256 _) && pack > 16 && architecture == .scalar then none else do
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

/-- Recompute CoreCLR reference-free 64-bit layout from ordered metadata fields; `previous`
    finds the computed layout of each nested struct. -/
def computeLayout (previous : Nat → Option ComputedLayout) (raw : RawLayout)
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
private theorem placeField_append (previous : Nat → Option ComputedLayout) (raw : RawLayout)
    (architecture : Architecture) (pack size alignment : Nat) (fields : List FieldLayout)
    (field : RawField) :
    (do
      let (size, alignment, placed) ← placeField previous raw architecture pack size alignment field
      return (size, alignment, fields ++ [placed])) = (do
      if (field.type matches .vector256 _) && pack > 16 && architecture == .scalar then none else do
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
theorem computeLayout_eq_append (previous : Nat → Option ComputedLayout) (raw : RawLayout)
    (architecture : Architecture) : computeLayout previous raw architecture = do
  if raw.packing ∉ [-1, 0, 1, 2, 4, 8, 16, 32, 64, 128] then none
  else if raw.declaredSize < -1 || raw.declaredSize > 65536 then none
  else if raw.explicit && raw.declaredSize ≤ 0 then none
  else if raw.auto && !autoSequential previous raw then none
  else
    let pack := if raw.packing ≤ 0 then 64 else raw.packing.toNat
    let (size, alignment, fields) ← raw.fields.foldlM (init := (0, 1, ([] : List FieldLayout)))
        fun (size, alignment, fields) field => do
      if (field.type matches .vector256 _) && pack > 16 && architecture == .scalar then none else do
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

/-- Reads into one raw layout table: the entry at a position, and the position of the first
    closed generic layout whose owner and arguments spell a type. -/
structure LayoutTable where
  entry : Nat → Option RawLayout
  owner : TypeExpr → Option Nat

/-- The reads of a raw layout list, each scanning the list. -/
def LayoutTable.ofList (layouts : List RawLayout) : LayoutTable :=
  ⟨(layouts[·]?), genericLayoutIndex layouts⟩

/-- Closed generic layouts in table order, each with its closed type and position. -/
private def genericOwnersFrom : Nat → List RawLayout → List (TypeExpr × Nat)
  | _, [] => []
  | position, layout :: rest =>
    let later := genericOwnersFrom (position + 1) rest
    match layout.generic with
    | some generic => (generic.closedType, position) :: later
    | none => later

/-- Closed generic layout positions in table order, bucketed by the key of their closed type. -/
def GenericOwnerIndex := Std.TreeMap (List (List UInt8)) (List (TypeExpr × Nat))

/-- Bucket every closed generic layout of a table once. -/
def GenericOwnerIndex.ofList (layouts : List RawLayout) : GenericOwnerIndex :=
  groupIndex (fun owner => typeKeyInto owner.1 []) (genericOwnersFrom 0 layouts)

/-- The first position, in table order, of a closed generic layout with exactly this type. -/
def GenericOwnerIndex.find (index : GenericOwnerIndex) (type : TypeExpr) : Option Nat :=
  ((index.getD (typeKeyInto type []) []).find? (·.1 == type)).map (·.2)

/-- Closed generic owners listed from `start` are found where `genericLayoutIndex` finds them,
    shifted by `start`. -/
private theorem genericOwnersFrom_find (type : TypeExpr) (layouts : List RawLayout)
    (start : Nat) :
    ((genericOwnersFrom start layouts).find? (·.1 == type)).map (·.2) =
      (genericLayoutIndex layouts type).map (· + start) := by
  induction layouts generalizing start with
  | nil => rfl
  | cons layout rest ih =>
    unfold genericLayoutIndex at ih ⊢
    have step := ih (start + 1)
    rw [List.findIdx?_cons]
    cases found : layout.generic with
    | none =>
      simp only [genericOwnersFrom, found, Option.any_none, Bool.false_eq_true, ↓reduceIte,
        step, Option.map_map]
      cases List.findIdx? (fun layout => layout.generic.any (·.closedType == type)) rest <;>
        simp <;> omega
    | some generic =>
      by_cases same : generic.closedType = type
      · simp [genericOwnersFrom, found, same]
      · have skip : (generic.closedType == type) = false := by simpa using same
        simp only [genericOwnersFrom, found, Option.any_some, skip, Bool.false_eq_true,
          ↓reduceIte, List.find?_cons, step, Option.map_map]
        cases List.findIdx? (fun layout => layout.generic.any (·.closedType == type)) rest <;>
          simp <;> omega

#print axioms genericOwnersFrom_find

/-- The bucketed owner lookup is exactly the first-match scan of the raw list. -/
theorem GenericOwnerIndex.find_ofList (layouts : List RawLayout) (type : TypeExpr) :
    (GenericOwnerIndex.ofList layouts).find type = genericLayoutIndex layouts type := by
  have bucketed : ((genericOwnersFrom 0 layouts).filter
      (fun owner => typeKeyInto owner.1 [] == typeKeyInto type [])).find? (·.1 == type) =
      (genericOwnersFrom 0 layouts).find? (·.1 == type) := by
    rw [List.find?_filter]
    congr 1
    funext owner
    by_cases same : owner.1 = type <;> simp [same]
  simp only [GenericOwnerIndex.find, GenericOwnerIndex.ofList, groupIndex_get, bucketed,
    genericOwnersFrom_find]
  cases genericLayoutIndex layouts type <;> rfl

#print axioms GenericOwnerIndex.find_ofList

/-- The reads of a raw layout list through a balanced index and an owner index, each built once,
    so every read costs time logarithmic in the table. -/
def LayoutTable.indexed (layouts : List RawLayout) : LayoutTable :=
  ⟨(FlowIndex.ofList layouts).get?, (GenericOwnerIndex.ofList layouts).find⟩

/-- Indexed reads return exactly what scanning the list returns. -/
theorem LayoutTable.indexed_eq (layouts : List RawLayout) :
    LayoutTable.indexed layouts = LayoutTable.ofList layouts := by
  unfold LayoutTable.indexed LayoutTable.ofList
  congr 1
  · funext position
    exact FlowIndex.get?_ofList layouts position
  · funext type
    exact GenericOwnerIndex.find_ofList layouts type

#print axioms LayoutTable.indexed_eq

/-- `closeLayoutTypeWith` together with whether the type is a class head or a class
    application, found in the same walk, so a class application is never looked up. -/
private def closeLayoutTypeKind (table : LayoutTable) : TypeExpr → TypeExpr × Bool
  | .byref type => (.byref (closeLayoutTypeKind table type).1, false)
  | .pointer type => (.pointer (closeLayoutTypeKind table type).1, false)
  | .array type => (.array (closeLayoutTypeKind table type).1, false)
  | .objectConstructor scope name => (.objectConstructor scope name, true)
  | .apply owner argument =>
    let (closedOwner, classHead) := closeLayoutTypeKind table owner
    let type := .apply closedOwner (closeLayoutTypeKind table argument).1
    if classHead then (type, true) else
    if closedOwner.isSpanHead then (type, false) else
    match table.owner type with
    | some index =>
      (.aggregate ((table.entry index).map RawLayout.identity |>.getD "") index, false)
    | none => (type, false)
  | type => (type, false)

/-- Resolve specialized storage tokens after substituting owner or method parameters. A class
    application stays a class whatever layout the table lists for it. -/
def closeLayoutTypeWith (table : LayoutTable) (type : TypeExpr) : TypeExpr :=
  (closeLayoutTypeKind table type).1

/-- `closeLayoutTypeWith` reading a raw layout list. -/
def closeLayoutType (layouts : List RawLayout) : TypeExpr → TypeExpr :=
  closeLayoutTypeWith (.ofList layouts)

/-- Closing layout indices inside a runtime span preserves its constructor. -/
theorem closeLayoutType_span (layouts : List RawLayout) (scope : String) (name : ClassName) (element : TypeExpr)
    (span : (TypeExpr.constructor scope name).isSpanHead = true) :
    closeLayoutType layouts (.apply (.constructor scope name) element) =
      .apply (.constructor scope name) (closeLayoutType layouts element) := by
  simp [closeLayoutType, closeLayoutTypeWith, closeLayoutTypeKind, span]
#print axioms closeLayoutType_span

/-- Field storage is derived from substituted metadata, including exact aggregate identities. -/
private def genericFieldType (table : LayoutTable) (type : TypeExpr) : Option FieldType :=
  match closeLayoutTypeWith table type with
  | .enum _ underlying => enumUnderlyingField underlying
  | .aggregate identity index =>
    if (table.entry index).any (·.identity == identity) then some (.aggregate index) else none
  | .primitive type => type.fieldType?
  | .apply (.constructor scope name) (.primitive element) => do
    if scope != "System.Runtime.Intrinsics, Version=11.0.0.0, Culture=neutral, " ++
        "PublicKeyToken=cc7b13ffcd2ddd51" then none
    let lane ← element.fieldType?.bind VectorLane.ofField?
    if name == "System.Runtime.Intrinsics.Vector128`1" then some (.vector128 lane)
    else if name == "System.Runtime.Intrinsics.Vector256`1" then some (.vector256 lane) else none
  | _ => none

/-- Closed generic identities retain the scope and ordering of every supported argument. -/
def genericOwnerIdentity (owner : TypeExpr) (arguments : List TypeExpr) : Option String := do
      let (scope, name) ← match owner with
        | .constructor scope name | .objectConstructor scope name =>
          Prod.mk scope <$> name.signatureName?
        | _ => none
      let names ← arguments.mapM fun argument => match argument with
        | .primitive type => some (runtimeScope ++ "::" ++ type.display)
        | .atom scope name => some (scope ++ "::" ++ name)
        | .aggregate identity _ => some identity
        | .enum identity _ => do
          return (← assemblyScope? identity.assembly) ++ "::" ++ (← enumSignatureName? identity)
        | .apply (.constructor scope name) (.primitive element)
        | .apply (.objectConstructor scope name) (.primitive element) =>
          do return scope ++ "::" ++ (← name.signatureName?) ++
            "<" ++ runtimeScope ++ "::" ++ element.display ++ ">"
        | .apply (.constructor scope name) (.atom elementScope element)
        | .apply (.objectConstructor scope name) (.atom elementScope element) =>
          do return scope ++ "::" ++ (← name.signatureName?) ++
            "<" ++ elementScope ++ "::" ++ element ++ ">"
        | _ => none
      return scope ++ "::" ++ name ++ "<" ++ String.intercalate "," names ++ ">"

/-- The exact runtime identity of the value-type constraint. -/
def valueTypeConstraint : String :=
  { toByteArray := ⟨#[
      83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 44, 32,
      86, 101, 114, 115, 105, 111, 110, 61, 49, 49, 46, 48, 46, 48, 46, 48,
      44, 32, 67, 117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97,
      108, 44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101,
      110, 61, 98, 48, 51, 102, 53, 102, 55, 102, 49, 49, 100, 53, 48, 97,
      51, 97, 58, 58, 83, 121, 115, 116, 101, 109, 46, 86, 97, 108, 117, 101,
      84, 121, 112, 101]⟩,
    isValidUTF8 := by decide +kernel }

/-- The byte-backed constraint retains the exact metadata identity. -/
theorem valueTypeConstraint_eq :
    valueTypeConstraint = runtimeScope ++ "::System.ValueType" := by decide +kernel
#print axioms valueTypeConstraint_eq

/-- The exact runtime identity of the unmanaged value-type constraint. -/
def unmanagedTypeConstraint : String :=
  { toByteArray := ⟨#[
      83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 44, 32,
      86, 101, 114, 115, 105, 111, 110, 61, 49, 49, 46, 48, 46, 48, 46, 48,
      44, 32, 67, 117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97,
      108, 44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101,
      110, 61, 98, 48, 51, 102, 53, 102, 55, 102, 49, 49, 100, 53, 48, 97,
      51, 97, 58, 58, 83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105,
      109, 101, 46, 73, 110, 116, 101, 114, 111, 112, 83, 101, 114, 118, 105, 99,
      101, 115, 46, 85, 110, 109, 97, 110, 97, 103, 101, 100, 84, 121, 112, 101,
      33, 83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 44,
      32, 86, 101, 114, 115, 105, 111, 110, 61, 49, 49, 46, 48, 46, 48, 46,
      48, 44, 32, 67, 117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114,
      97, 108, 44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107,
      101, 110, 61, 98, 48, 51, 102, 53, 102, 55, 102, 49, 49, 100, 53, 48,
      97, 51, 97, 58, 58, 83, 121, 115, 116, 101, 109, 46, 86, 97, 108, 117,
      101, 84, 121, 112, 101]⟩,
    isValidUTF8 := by decide +kernel }

/-- The byte-backed constraint retains the exact metadata identity. -/
theorem unmanagedTypeConstraint_eq :
    unmanagedTypeConstraint = runtimeScope ++ "::System.Runtime.InteropServices.UnmanagedType!" ++
      runtimeScope ++ "::System.ValueType" := by decide +kernel
#print axioms unmanagedTypeConstraint_eq

/-- Value-type flags and exact direct interface identities constrain a closed type argument. -/
def genericConstraintValidWith (table : LayoutTable) (argument : TypeExpr)
    (flags : Nat) (types : List String) : Bool :=
  flags &&& 56 == flags && types.all fun type =>
    type == valueTypeConstraint || type == unmanagedTypeConstraint || match argument with
    | .aggregate identity index => match table.entry index with
      | some layout => layout.identity == identity && layout.interfaces.contains type
      | none => false
    | _ => false

/-- `genericConstraintValidWith` reading a raw layout list. -/
def genericConstraintValid (layouts : List RawLayout) (argument : TypeExpr)
    (flags : Nat) (types : List String) : Bool :=
  genericConstraintValidWith (.ofList layouts) argument flags types

/-- A generic layout is owned by the value-type definition at these physical columns. -/
def GenericLayout.declares (generic : GenericLayout) (levels : List TypeLevel) : Bool :=
  match generic.owner with
  | .constructor _ name => name.levels == levels
  | _ => false

/-- Generic layouts cannot replace their argument ordering or original field storage, and only
    a struct's generic definition owns one, since a class instance is a reference. -/
def genericLayoutValid (table : LayoutTable) (layout : RawLayout) : Bool :=
  match layout.generic with
  | none => true
  | some generic =>
    generic.declares layout.declaration &&
    genericOwnerIdentity generic.owner generic.arguments == some layout.identity &&
      !layout.explicit && !layout.auto && generic.arity > 0 &&
      generic.arguments.length == generic.arity &&
      generic.constraints.length == generic.arity &&
      (generic.constraints.zip generic.arguments).all (fun (constraint, argument) =>
        genericConstraintValidWith table argument constraint.1 constraint.2) &&
      generic.arguments.all (fun type => substituteType [] type == some type &&
        (genericFieldType table type).isSome) &&
      (generic.fields.mapM fun type => do
        genericFieldType table (← substituteType generic.arguments type)) ==
          some (layout.fields.map RawField.type)

/-- A heap-storable struct cannot contain a byref-like struct, even with no reference fields. -/
def byRefLikeFieldsValid (table : LayoutTable) (layout : RawLayout) : Bool :=
  layout.byRefLike || layout.fields.all (fun field => match field.type with
    | .aggregate index => (table.entry index).any (fun child => !child.byRefLike)
    | _ => true)

/-- Reject forward references and cycles by computing strictly in metadata-table order. -/
def computeLayouts (raw : List RawLayout) (architecture : Architecture := .scalar) :
    Option (Array ComputedLayout) :=
  let table := LayoutTable.ofList raw
  if !raw.all (fun layout => genericLayoutValid table layout && byRefLikeFieldsValid table layout)
    then none else
    raw.foldlM (init := #[]) fun previous entry => do
      return previous.push (← computeLayout (previous[·]?) entry architecture)

/-- Reject repeated values and values already in the ordered set. -/
private def distinctFrom [Ord α] : Std.TreeSet α → List α → Bool
  | _, [] => true
  | seen, value :: rest => !seen.contains value && distinctFrom (seen.insert value) rest

/-- Ordered membership preserves the exact list uniqueness condition. -/
private theorem distinctFrom_correct [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    (seen : Std.TreeSet α) (values : List α) :
    distinctFrom seen values = true ↔ values.Nodup ∧ ∀ value ∈ values, value ∉ seen := by
  induction values generalizing seen with
  | nil => simp [distinctFrom]
  | cons value rest ih =>
    simp only [distinctFrom, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
      ih, List.nodup_cons, List.forall_mem_cons,
      Std.TreeSet.mem_insert, Std.compare_eq_iff_eq, not_or]
    constructor
    · rintro ⟨fresh, distinct, remaining⟩
      refine ⟨⟨?_, distinct⟩, fresh, ?_⟩
      · intro member
        exact (remaining value member).1 rfl
      · intro other member
        exact (remaining other member).2
    · rintro ⟨⟨fresh, distinct⟩, unseen, remaining⟩
      refine ⟨unseen, distinct, ?_⟩
      intro other member
      exact ⟨fun same => fresh (same ▸ member), remaining other member⟩

#print axioms distinctFrom_correct

/-- Check uniqueness using logarithmic ordered membership instead of repeated list scans. -/
def orderedDistinct [Ord α] (values : List α) : Bool := distinctFrom ∅ values

/-- The ordered uniqueness check accepts exactly the duplicate-free lists. -/
theorem orderedDistinct_iff [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    (values : List α) : orderedDistinct values = true ↔ values.Nodup := by
  simp [orderedDistinct, distinctFrom_correct]

#print axioms orderedDistinct_iff

/-- Distinct UTF-8 keys denote distinct layout identities. -/
private theorem keyBytes_inj {left right : String} :
    keyBytes left = keyBytes right ↔ left = right := by
  simp only [keyBytes, Array.toList_inj, ← ByteArray.ext_iff, String.toByteArray_inj]

#print axioms keyBytes_inj

/-- Suffix-first byte keys distinguish type names before their common assembly prefix. -/
def layoutIdentitiesDistinct (raw : List RawLayout) : Bool :=
  orderedDistinct (raw.map fun row => (keyBytes row.identity).reverse)

/-- The byte-key check accepts exactly the tables with distinct identity strings. -/
theorem layoutIdentitiesDistinct_iff (raw : List RawLayout) :
    layoutIdentitiesDistinct raw = true ↔ (raw.map RawLayout.identity).Nodup := by
  simp only [layoutIdentitiesDistinct, orderedDistinct_iff, List.Nodup, List.pairwise_map,
    ne_eq, List.reverse_inj, keyBytes_inj]

#print axioms layoutIdentitiesDistinct_iff

/-- Each identity names one raw row, and its recomputed layout agrees with the claimed row. -/
def LayoutsValid (raw : List RawLayout) (claimed : Array ComputedLayout)
    (architecture : Architecture := .scalar) : Prop :=
  (raw.map RawLayout.identity).Nodup ∧ computeLayouts raw architecture = some claimed ∧
    ∀ item ∈ claimed.toList, item.layout.Valid

/-- Two indexed reads of the same validated type identity select the same layout row. -/
theorem LayoutsValid.index_eq_of_identity_eq {raw : List RawLayout}
    {claimed : Array ComputedLayout} {architecture : Architecture}
    (valid : LayoutsValid raw claimed architecture) {first second : Nat}
    {left right : RawLayout} (readLeft : raw[first]? = some left)
    (readRight : raw[second]? = some right) (same : left.identity = right.identity) :
    first = second := by
  apply valid.1.eq_of_getElem?_eq
  · simpa using (List.getElem?_eq_some_iff.mp readLeft).choose
  · simp [List.getElem?_map, readLeft, readRight, same]

#print axioms LayoutsValid.index_eq_of_identity_eq

/-- Check raw entries against claimed entries in table order. The entry at `position` reads only
    claimed layouts at earlier positions, and both lists must end together. -/
private def layoutEntriesValid (table : LayoutTable) (architecture : Architecture)
    (claimed : Nat → Option ComputedLayout) : Nat → List RawLayout → List ComputedLayout → Bool
  | position, entry :: rest, item :: items =>
    (genericLayoutValid table entry && byRefLikeFieldsValid table entry &&
      decide (computeLayout (fun child => if child < position then claimed child else none)
        entry architecture = some item) &&
      decide item.layout.Valid) &&
      layoutEntriesValid table architecture claimed (position + 1) rest items
  | _, [], [] => true
  | _, _, _ => false

/-- Read raw entries through `LayoutTable.indexed` and
    claimed layouts through one balanced index, so `L` layouts with `A` fields in total cost
    `O((L + A) log L)` lookups. A generic layout also looks up the closed owner of each `.apply`
    node of its argument and original field types by that node's type key, so a type of size `s`
    and depth `d` adds `O(s * d * log L)`. -/
def layoutsValidIndexed (raw : List RawLayout) (claimed : Array ComputedLayout)
    (architecture : Architecture) : Bool :=
  layoutIdentitiesDistinct raw &&
    layoutEntriesValid (.indexed raw) architecture (FlowIndex.ofList claimed.toList).get? 0 raw
      claimed.toList

/-- Each step of the layout fold appends one computed layout to its accumulator. -/
private theorem layoutFold_extends (architecture : Architecture) (raw : List RawLayout)
    (done result : Array ComputedLayout)
    (folded : raw.foldlM (init := done) (fun previous entry => do
      return previous.push (← computeLayout (previous[·]?) entry architecture)) = some result) :
    ∃ added : List ComputedLayout,
      result.toList = done.toList ++ added ∧ added.length = raw.length := by
  induction raw generalizing done with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at folded
    exact ⟨[], by simp [folded], rfl⟩
  | cons entry rest ih =>
    simp only [List.foldlM_cons] at folded
    cases computed : computeLayout (done[·]?) entry architecture with
    | none => simp [computed] at folded
    | some layout =>
      simp only [computed, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at folded
      obtain ⟨added, extended, length⟩ := ih (done.push layout) folded
      exact ⟨layout :: added, by simp [extended], by simp [length]⟩

#print axioms layoutFold_extends

/-- Reading the claimed table below the accumulator's size reads the accumulator. -/
private theorem claimed_prefix_lookup (claimed done : Array ComputedLayout)
    (remaining : List ComputedLayout) (split : done.toList ++ remaining = claimed.toList) :
    (fun child => if child < done.size then claimed.toList[child]? else none) =
      (done[·]?) := by
  funext child
  by_cases below : child < done.size
  · simp only [below, ↓reduceIte]
    rw [← split, List.getElem?_append_left (by simpa using below), Array.getElem?_toList]
  · simp only [below, ↓reduceIte]
    rw [Array.getElem?_eq_none (by omega)]

#print axioms claimed_prefix_lookup

/-- From any accumulator that is a prefix of the claimed table, the indexed pass accepts exactly
    when the raw-table rules and claimed well-formedness hold for the rest and the fold reaches
    the claimed table. -/
private theorem layoutEntriesValid_iff (table : LayoutTable) (architecture : Architecture)
    (claimed : Array ComputedLayout) (raw : List RawLayout) (done : Array ComputedLayout)
    (remaining : List ComputedLayout) (split : done.toList ++ remaining = claimed.toList) :
    layoutEntriesValid table architecture (claimed.toList[·]?) done.size raw remaining = true ↔
      (∀ entry ∈ raw, genericLayoutValid table entry = true ∧
        byRefLikeFieldsValid table entry = true) ∧
      (∀ item ∈ remaining, item.layout.Valid) ∧
      raw.foldlM (init := done) (fun previous entry => do
        return previous.push (← computeLayout (previous[·]?) entry architecture)) =
          some claimed := by
  induction raw generalizing done remaining with
  | nil =>
    cases remaining with
    | nil =>
      have same : done = claimed := Array.toList_inj.mp (by simpa using split)
      simp [layoutEntriesValid, same]
    | cons item items =>
      simp only [layoutEntriesValid, Bool.false_eq_true, false_iff, List.foldlM_nil,
        Option.pure_def, Option.some.injEq, not_and]
      intro _ _ same
      subst same
      simp at split
  | cons entry rest ih =>
    cases remaining with
    | nil =>
      simp only [layoutEntriesValid, Bool.false_eq_true, false_iff, not_and]
      intro _ _ folded
      obtain ⟨added, extended, length⟩ := layoutFold_extends architecture _ done claimed folded
      rw [← split, List.append_nil] at extended
      have empty : added = [] := by simpa using extended
      simp [empty] at length
    | cons item items =>
      simp only [layoutEntriesValid, claimed_prefix_lookup claimed done (item :: items) split,
        List.foldlM_cons, List.forall_mem_cons, Bool.and_eq_true, decide_eq_true_eq]
      cases computed : computeLayout (done[·]?) entry architecture with
      | none => simp
      | some layout =>
        simp only [Option.some.injEq, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        by_cases same : layout = item
        · subst same
          have pushed : (done.push layout).toList ++ items = claimed.toList := by simp [← split]
          have next := ih (done.push layout) items pushed
          rw [Array.size_push] at next
          rw [next]
          constructor
          · rintro ⟨⟨⟨⟨generic, byRefLike⟩, -⟩, valid⟩, rest, items, folded⟩
            exact ⟨⟨⟨generic, byRefLike⟩, rest⟩, ⟨valid, items⟩, folded⟩
          · rintro ⟨⟨⟨generic, byRefLike⟩, rest⟩, ⟨valid, items⟩, folded⟩
            exact ⟨⟨⟨⟨generic, byRefLike⟩, rfl⟩, valid⟩, rest, items, folded⟩
        · simp only [same, and_false, false_and, false_iff, not_and]
          intro _ _ folded
          obtain ⟨added, extended, -⟩ := layoutFold_extends architecture _ _ claimed folded
          rw [← split] at extended
          simp at extended
          exact same extended.1.symm

#print axioms layoutEntriesValid_iff

/-- The indexed checks are equivalent to identity uniqueness, recomputation and field bounds. -/
theorem layoutsValidIndexed_iff (raw : List RawLayout) (claimed : Array ComputedLayout)
    (architecture : Architecture) :
    layoutsValidIndexed raw claimed architecture = true ↔
      LayoutsValid raw claimed architecture := by
  have lookup : (FlowIndex.ofList claimed.toList).get? = (claimed.toList[·]?) :=
    funext (FlowIndex.get?_ofList claimed.toList)
  have entries := layoutEntriesValid_iff (.ofList raw) architecture claimed raw #[]
    claimed.toList (by simp)
  rw [Array.size_empty] at entries
  unfold layoutsValidIndexed LayoutsValid computeLayouts
  rw [Bool.and_eq_true, layoutIdentitiesDistinct_iff, LayoutTable.indexed_eq, lookup, entries]
  apply and_congr_right
  intro _
  by_cases checks : (raw.all fun layout => genericLayoutValid (.ofList raw) layout &&
      byRefLikeFieldsValid (.ofList raw) layout) = true
  · have holds := checks
    simp only [List.all_eq_true, Bool.and_eq_true] at holds
    simp only [checks, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun ⟨_, valid, folded⟩ => ⟨folded, valid⟩,
      fun ⟨folded, valid⟩ => ⟨holds, valid, folded⟩⟩
  · have fails : ¬ ∀ entry ∈ raw, genericLayoutValid (.ofList raw) entry = true ∧
        byRefLikeFieldsValid (.ofList raw) entry = true := by
      simpa [List.all_eq_true] using checks
    simp only [Bool.not_eq_true] at checks
    simp only [checks, Bool.not_false, ↓reduceIte, reduceCtorEq, false_and, iff_false]
    exact fun ⟨holds, _⟩ => fails holds

/--
info: 'CIL.Extraction.layoutsValidIndexed_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms layoutsValidIndexed_iff

/-- Every decision of `LayoutsValid`, in the extraction header, per method, for import catalogs
    and for layout projections, runs the one-pass indexed check. -/
instance layoutsValidDecidable (raw : List RawLayout) (claimed : Array ComputedLayout)
    (architecture : Architecture) : Decidable (LayoutsValid raw claimed architecture) :=
  decidable_of_iff _ (layoutsValidIndexed_iff raw claimed architecture)

/--
info: 'CIL.Extraction.layoutsValidDecidable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms layoutsValidDecidable

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
  field_within_layout item.layout (checked.2.2 item member) field present

end CIL.Extraction
