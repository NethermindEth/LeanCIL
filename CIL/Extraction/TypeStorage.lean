import CIL.Extraction.Parameters
import CIL.Extraction.MetadataText

/-!
# Storage from metadata types

Storage and callable representations of resolved metadata types used by extraction and execution.
-/

namespace CIL.Extraction

/-- The exact `System.Runtime.Intrinsics` assembly identity; `runtimeScope` is in `TypeExpr`. -/
def intrinsicsScope : String :=
  metadata_text%
    "System.Runtime.Intrinsics, Version=11.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

/-- Byte width of an admitted integer vector, bound to both exact runtime type identities. -/
def integerVectorWidth : TypeExpr → Option Nat
  | .apply (.constructor scope name) (.primitive element) =>
    if scope != intrinsicsScope || element ∉ [.byte, .int32, .uint32, .int64, .uint64] then none
    else if name == "System.Runtime.Intrinsics.Vector128`1" then some 16
    else if name == "System.Runtime.Intrinsics.Vector256`1" then some 32
    else if name == "System.Runtime.Intrinsics.Vector512`1" then some 64
    else none
  | _ => none

/-- A closed object operand may retain a type application for a runtime span or an integer
    vector. Other admitted generic structs are represented by their layout index. -/
def objectApplicationAdmitted : TypeExpr → Bool
  | type@(.apply ..) => type.isRuntimeSpan || (integerVectorWidth type).isSome
  | _ => true

/-- The storage of an enum over the primitive; `none` where `typeStorage` admits no enum. -/
def _root_.CIL.PrimitiveType.enumStorage : PrimitiveType → Option EnumStorage
  | .sbyte => some .signed8 | .byte => some .unsigned8
  | .int16 => some .signed16 | .uint16 => some .unsigned16
  | .int32 => some .signed32 | .uint32 => some .unsigned32
  | .int64 => some .signed64 | .uint64 => some .unsigned64
  | .boolean | .char | .single | .double | .intPtr | .uintPtr => none

/-- The array element storage of a primitive; `none` for `Single` and `Double`. -/
def _root_.CIL.PrimitiveType.arrayElement? : PrimitiveType → Option ArrayElement
  | .sbyte => some .signed8 | .byte => some .unsigned8
  | .int16 => some .signed16 | .uint16 => some .unsigned16
  | .int32 => some .signed32 | .uint32 => some .unsigned32
  | .int64 => some .signed64 | .uint64 => some .unsigned64
  | .intPtr => some .nativeInt | .uintPtr => some .nativeUInt
  | .boolean => some .boolean | .char => some .character
  | .single | .double => none

/-- Whether a pointer to the primitive has reference storage: the integers and `Char`, not
    `Boolean` or the floating types. -/
def _root_.CIL.PrimitiveType.pointerStorage : PrimitiveType → Bool
  | .sbyte | .byte | .int16 | .uint16 | .char | .int32 | .uint32 | .int64 | .uint64 | .intPtr
  | .uintPtr => true
  | .boolean | .single | .double => false

/-- Primitive array element identity is derived from the typed runtime primitive. -/
def arrayElementType (type : TypeExpr) (aggregateWidth : Nat := 0) : Option ArrayElement :=
  match type with
  | .aggregate identity _ => some (.aggregate identity aggregateWidth)
  | type@(.apply (.constructor _ name) (.primitive element)) => do
    let width ← integerVectorWidth type
    return .vector ((← name.signatureName?) ++ "<" ++ element.display ++ ">") width
  | .enum identity storage => some (.enumeration identity storage)
  | .primitive type => type.arrayElement?
  | _ => none
/-- Primitive/vector widths are intrinsic; aggregate widths come from checked layout uses. -/
def spanElementWidth (type : TypeExpr) (aggregateWidth : Nat := 0) : Option Nat :=
  if let .aggregate .. := type then some aggregateWidth else
  ((arrayElementType type).map ArrayElement.width).orElse (fun _ => integerVectorWidth type)

/-- Exact span metadata, including element width and write capability. -/
def spanStorage (type : TypeExpr) (aggregateWidth : Nat := 0) : Option StorageType :=
  match type with
  | .apply head@(.constructor _ name) elementType => do
    if !head.isSpanHead then none else
    let width ← spanElementWidth elementType aggregateWidth
    return .span width (name == "System.Span`1")
  | _ => none

/-- Whether a local has a supported span metadata shape; layouts are validated separately. -/
def spanLocal (type : TypeExpr) : Bool := (spanStorage type).isSome

/-- Callable identities retain scoped aggregate names, independent of layout-table ordering.
    Argument storage still validates the original index against the checked layout metadata. -/
def callableType : TypeExpr → TypeExpr
  | .aggregate identity _ => .aggregate identity 0
  | .byref element => .byref (callableType element)
  | .apply constructor argument => .apply (callableType constructor) (callableType argument)
  | .functionPointer result parameters convention hasThis explicitThis =>
    .functionPointer (callableType result) (callableType parameters) convention hasThis
      explicitThis
  | .signatureParameter head tail => .signatureParameter (callableType head) (callableType tail)
  | type => type

/-- Function pointers admit checked aggregates, integer vectors and integer/reference types. -/
def managedParameter : TypeExpr → Bool
  | .primitive type => type.fieldType?.isSome
  | .enum .. => true
  | .byref element => match element with
      | .primitive _ | .enum .. | .aggregate .. | .apply .. => managedParameter element
      | _ => false
  | .aggregate .. => true
  | type => (integerVectorWidth type).isSome

/-- Decode the ordered parameter chain without accepting another metadata constructor. -/
def managedParameters : TypeExpr → Option (List TypeExpr)
  | .void => some []
  | .signatureParameter head tail => do
    if !managedParameter head then none else pure ()
    return callableType head :: (← managedParameters tail)
  | _ => none

/-- Only the exact static managed convention gives callable provenance. -/
def managedSignature : TypeExpr → Option ManagedSignature
  | .functionPointer result parameters 0 false false => do
    if result != .void && !managedParameter result then none else pure ()
    return ⟨callableType result, ← managedParameters parameters⟩
  | _ => none

/-- Raw callable types must bind every aggregate index before their identity is canonicalized. -/
def callableLayoutsAt (layoutAt : Nat → Option RawLayout) : TypeExpr → Bool
  | .aggregate identity index => (layoutAt index).any (·.identity == identity)
  | .byref element => callableLayoutsAt layoutAt element
  | .functionPointer result parameters _ _ _ =>
    callableLayoutsAt layoutAt result && callableLayoutsAt layoutAt parameters
  | .signatureParameter head tail =>
    callableLayoutsAt layoutAt head && callableLayoutsAt layoutAt tail
  | _ => true

/-- Callable metadata binds every aggregate index in the declared layout list. -/
def callableLayoutsValid (layouts : List RawLayout) : TypeExpr → Bool :=
  callableLayoutsAt (layouts[·]?)

/-- Four-byte groups bound the nesting of equality decisions on long metadata identities. -/
private def equalBytes : List UInt8 → List UInt8 → Bool
  | a :: b :: c :: d :: left, w :: x :: y :: z :: right =>
    bif decide (a = w) && decide (b = x) && decide (c = y) && decide (d = z)
    then equalBytes left right else false
  | left, right => @decide (left = right) (@List.hasDecEq UInt8 UInt8.decEq left right)

/-- The grouped comparison accepts exactly equal byte sequences. -/
private theorem equalBytes_iff (left right : List UInt8) :
    equalBytes left right = true ↔ left = right := by
  fun_induction equalBytes <;> simp_all [List.cons.injEq, and_assoc]

#print axioms equalBytes_iff

/-- Two metadata identities are equal exactly when their UTF-8 bytes agree. -/
private def identityEq (left right : String) : Decidable (left = right) :=
  decidable_of_iff (equalBytes left.toByteArray.data.toList right.toByteArray.data.toList = true)
    (by rw [equalBytes_iff, Array.toList_inj, ← ByteArray.ext_iff, String.toByteArray_inj])

/-- Compiled storage checks use the native string comparison. -/
@[csimp] private theorem identityEq_eq : identityEq = String.decEq := by
  funext left right
  apply Subsingleton.elim

#print axioms identityEq_eq

/-- Decode storage independently from the exact metadata type identity. -/
def typeStorageAt (layoutAt : Nat → Option RawLayout) : TypeExpr → Option StorageType
  | .primitive type => .field <$> type.fieldType?
  -- CoreLib defines its own primitives; a runtime-scope atom has no storage.
  | .atom scope name => if scope = coreLibraryScope then .field <$> primitiveField name else none
  | .object _ _ => some .object
  | .aggregate identity index => do
    let metadata ← layoutAt index
    letI := identityEq metadata.identity identity
    if metadata.identity = identity then return .field (.aggregate index) else none
  | .enum _ storage => some (.field storage.fieldType)
  | .byref _ => some .reference
  -- An array of class references is itself an object on the heap.
  | .array (.object _ _) => some .object
  | .array (.aggregate identity index) => do
    let metadata ← layoutAt index
    if metadata.identity == identity && !metadata.byRefLike then
      some (.aggregateArray identity index) else none
  | .array element => match managedSignature element with
    | some signature => if callableLayoutsAt layoutAt element then some (.methodTable signature)
      else none
    | none => StorageType.array <$> arrayElementType element
  | type@(.functionPointer ..) => if callableLayoutsAt layoutAt type then
      StorageType.methodPointer <$> managedSignature type else none
  | .pointer (.primitive type) => if type.pointerStorage then some .reference else none
  | .pointer (.atom scope name) =>
    if scope == coreLibraryScope &&
        name ∈ ["System.SByte", "System.Byte", "System.Int16",
        "System.UInt16", "System.Char", "System.Int32", "System.UInt32", "System.Int64",
        "System.UInt64", "System.IntPtr", "System.UIntPtr"] then some .reference else none
  | .pointer (.enum ..) => some .reference
  | .pointer (.aggregate identity index) => do
    let metadata ← layoutAt index
    if metadata.identity == identity then some .reference else none
  | .pointer type => if (integerVectorWidth type).isSome then some .reference else none
  | type@(.apply (.constructor scope name) elementType) => do
    if let some storage := spanStorage type then
      if let .aggregate identity index := elementType then
        let metadata ← layoutAt index
        if metadata.identity != identity then none else
          return .aggregateSpan index (name == "System.Span`1")
      else return storage
    let .primitive element := elementType | none
    if scope != intrinsicsScope ||
        element ∉ [.uint64, .int64, .uint32, .int32, .byte, .double, .single] then none
    else if name = "System.Runtime.Intrinsics.Vector128`1" then some .vector128
    else if name = "System.Runtime.Intrinsics.Vector256`1" then some .vector256
    else if name = "System.Runtime.Intrinsics.Vector512`1" then some .vector512 else none
  | _ => none

/-- Storage of a type under the supplied raw metadata. -/
def typeStorage (layouts : List RawLayout) : TypeExpr → Option StorageType :=
  typeStorageAt (layouts[·]?)

/-- The struct field tag a field holding `type` is declared with: a primitive's kind, an enum's
    underlying kind, a checked struct's index, or an integer vector's width and element lane. -/
def fieldKind? (layouts : List RawLayout) (type : TypeExpr) : Option FieldType :=
  match typeStorage layouts type, type with
  | some (.field kind), _ => some kind
  -- `typeStorage` has decided the vector's scope; the element primitive decides the lane.
  | some .vector128, .apply _ (.primitive element) =>
    FieldType.vector128 <$> element.fieldType?.bind VectorLane.ofField?
  | some .vector256, .apply _ (.primitive element) =>
    FieldType.vector256 <$> element.fieldType?.bind VectorLane.ofField?
  | _, _ => none

/-- Storage accepted by Unsafe reference casts and element offsets. -/
def StorageType.isFieldOrVector : StorageType → Bool
  | .field _ | .vector128 | .vector256 | .vector512 => true
  | _ => false

end CIL.Extraction
