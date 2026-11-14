import CIL.Extraction.TypeStorage
import CIL.Identity

/-!
# Narrowing from declared types

`declaredNarrow` is the small-integer narrowing a value of a declared metadata type takes:
the storage of a primitive or of an enum's underlying type. `CIL.Method.returnNarrow` applies it
to a method's declared return type. The lemmas here state the narrowing of every primitive, of
every enum over a primitive and of every other type head, so a generated fact names a method's
narrowing by lemma application and no generated proof evaluates a type name.
-/

namespace CIL

/-- The type expression the extractor writes for a primitive: its full name in the runtime
    scope. -/
def PrimitiveType.typeExpr (type : PrimitiveType) : Extraction.TypeExpr :=
  .atom Extraction.runtimeScope type.display

/-- The narrowing a value of the primitive takes; `none` for every type wider than 16 bits. -/
def PrimitiveType.narrow : PrimitiveType → Option NarrowKind
  | .sbyte => some .signed8
  | .byte | .boolean => some .unsigned8
  | .int16 => some .signed16
  | .uint16 | .char => some .unsigned16
  | .int32 | .uint32 | .int64 | .uint64 | .single | .double | .intPtr | .uintPtr => none

/-- Whether `typeStorage` admits the primitive as an enum's underlying type. -/
def PrimitiveType.enumUnderlying : PrimitiveType → Bool
  | .sbyte | .byte | .int16 | .uint16 | .int32 | .uint32 | .int64 | .uint64 => true
  | .boolean | .char | .single | .double | .intPtr | .uintPtr => false

namespace Extraction

/-- Whether `declaredNarrow` can be `some` for the type's head: an atom or an enum. -/
def TypeExpr.narrowCandidate : TypeExpr → Bool
  | .atom .. | .enum .. => true
  | _ => false

/-- The narrowing a value of declared type `type` takes: the small-integer storage of a primitive
    or of an enum's underlying type, and `none` for every other type. Any other head is `none`
    without decoding its storage, so evaluating it never compares a struct identity. -/
def declaredNarrow (layouts : List RawLayout) (type : TypeExpr) : Option NarrowKind :=
  if type.narrowCandidate then (typeStorage layouts type).bind StorageType.narrow else none

/-- A primitive narrows as its own kind, whatever the layout table. -/
theorem declaredNarrow_primitive (layouts : List RawLayout) (type : PrimitiveType) :
    declaredNarrow layouts type.typeExpr = type.narrow := by
  cases type <;> rfl

#print axioms declaredNarrow_primitive

/-- An enum narrows as its underlying primitive when `typeStorage` admits that primitive as an
    enum's underlying type, and not at all otherwise. -/
theorem declaredNarrow_enum (layouts : List RawLayout) (identity : String)
    (type : PrimitiveType) :
    declaredNarrow layouts (.enum identity type.typeExpr) =
      if type.enumUnderlying then type.narrow else none := by
  cases type <;> rfl

#print axioms declaredNarrow_enum

/-- The narrowing of a storage that is never a small-integer field is `none`. -/
theorem storage_narrow_of_wide {storage : Option StorageType}
    (wide : ∀ field, storage = some (.field field) → ∃ index, field = .aggregate index) :
    storage.bind StorageType.narrow = none := by
  cases storage with
  | none => rfl
  | some storage =>
    cases storage with
    | field field =>
      obtain ⟨index, rfl⟩ := wide field rfl
      rfl
    | _ => rfl

#print axioms storage_narrow_of_wide

/-- Span metadata is never stored as a field. -/
theorem spanStorage_ne_field (type : TypeExpr) (width : Nat) (field : FieldType) :
    spanStorage type width ≠ some (.field field) := by
  unfold spanStorage
  split
  · intro stored
    revert stored
    split
    · simp
    · simp [Option.bind_eq_bind, Option.bind_eq_some_iff]
  · simp

#print axioms spanStorage_ne_field

/-- Every head other than an atom or an enum decodes to a struct field, a reference, a
    vector, a span, an array, a callable or an object, none of which narrows. -/
theorem typeStorage_narrow_of_not_candidate (layouts : List RawLayout) (type : TypeExpr)
    (shape : type.narrowCandidate = false) :
    (typeStorage layouts type).bind StorageType.narrow = none := by
  apply storage_narrow_of_wide
  intro field stored
  cases type with
  | atom => simp [TypeExpr.narrowCandidate] at shape
  | enum => simp [TypeExpr.narrowCandidate] at shape
  | aggregate identity index =>
    simp only [typeStorage] at stored
    revert stored
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
    rintro ⟨metadata, -, chosen⟩
    split at chosen
    · simp only [pure, Option.some.injEq, StorageType.field.injEq] at chosen
      exact ⟨index, chosen.symm⟩
    · cases chosen
  | array element =>
    cases element <;> simp only [typeStorage] at stored <;> revert stored <;> (repeat' split) <;>
      simp_all [Option.map_eq_map, Option.bind_eq_bind, Option.bind_eq_some_iff]
  | pointer element =>
    cases element <;> simp only [typeStorage] at stored <;> revert stored <;> (repeat' split) <;>
      simp_all [Option.bind_eq_bind, Option.bind_eq_some_iff]
    -- A pointer to an enum: the storage of the pointer itself is a reference.
    intro storage _ _ _ result
    cases storage <;> simp at result
  | apply constructor argument =>
    cases constructor <;> simp only [typeStorage] at stored <;> revert stored <;>
      (repeat' split) <;> simp_all [Option.bind_eq_bind, Option.bind_eq_some_iff]
    -- A span: its storage is the one `spanStorage` gives.
    rintro rfl
    exact absurd ‹spanStorage _ _ = _› (spanStorage_ne_field _ _ _)
  | _ => simp [typeStorage] at stored

#print axioms typeStorage_narrow_of_not_candidate

/-- `declaredNarrow` is the narrowing of the type's decoded storage, for every type. -/
theorem declaredNarrow_eq_storage (layouts : List RawLayout) (type : TypeExpr) :
    declaredNarrow layouts type = (typeStorage layouts type).bind StorageType.narrow := by
  unfold declaredNarrow
  split
  · rfl
  · next other =>
    exact (typeStorage_narrow_of_not_candidate layouts type (by simpa using other)).symm

#print axioms declaredNarrow_eq_storage

/-- A type whose storage is never a small-integer field does not narrow. -/
theorem declaredNarrow_of_storage {layouts : List RawLayout} {type : TypeExpr}
    (wide : ∀ field, typeStorage layouts type = some (.field field) →
      ∃ index, field = .aggregate index) :
    declaredNarrow layouts type = none := by
  rw [declaredNarrow_eq_storage]
  exact storage_narrow_of_wide wide

#print axioms declaredNarrow_of_storage

/-- Only an atom or an enum narrows; any other head is `none` without decoding its storage. -/
theorem declaredNarrow_of_not_candidate (layouts : List RawLayout) (type : TypeExpr)
    (shape : type.narrowCandidate = false) : declaredNarrow layouts type = none := by
  simp [declaredNarrow, shape]

#print axioms declaredNarrow_of_not_candidate

/-- An enum cannot introduce narrowing when its underlying storage does not narrow. -/
theorem declaredNarrow_enum_of_none (layouts : List RawLayout) (identity : String)
    (type : TypeExpr) (narrow : declaredNarrow layouts type = none) :
    declaredNarrow layouts (.enum identity type) = none := by
  rw [declaredNarrow_eq_storage] at narrow ⊢
  simp only [typeStorage]
  cases stored : typeStorage layouts type with
  | none => simp
  | some storage =>
    rw [stored] at narrow
    cases storage <;> try simp
    case field kind =>
      cases kind <;> simp_all [StorageType.narrow]

#print axioms declaredNarrow_enum_of_none

end Extraction

/-- The narrowing `ret` applies: the declared return type's small-integer storage, and `none`
    for a method that returns nothing. -/
def Method.returnNarrow (body : Method) : Option NarrowKind :=
  if body.returnsValue then
    Extraction.declaredNarrow body.environment.rawLayouts body.declared.returnType
  else none

/-- A method that returns nothing does not narrow. -/
theorem Method.returnNarrow_of_void {body : Method} (returns : body.returnsValue = false) :
    body.returnNarrow = none := by
  simp [Method.returnNarrow, returns]

#print axioms Method.returnNarrow_of_void

/-- A method that returns a value narrows as its declared return type. -/
theorem Method.returnNarrow_of_declared {body : Method} {type : Extraction.TypeExpr}
    {result : Option NarrowKind} (returns : body.returnsValue = true)
    (declared : body.declared.returnType = type)
    (resolved : Extraction.declaredNarrow body.environment.rawLayouts type = result) :
    body.returnNarrow = result := by
  simp [Method.returnNarrow, returns, declared, resolved]

#print axioms Method.returnNarrow_of_declared

/-- A narrowed method returns a value. -/
theorem Method.returnsValue_of_returnNarrow {body : Method} {kind : NarrowKind}
    (narrowed : body.returnNarrow = some kind) : body.returnsValue = true := by
  unfold Method.returnNarrow at narrowed
  split at narrowed <;> simp_all

#print axioms Method.returnsValue_of_returnNarrow

end CIL
