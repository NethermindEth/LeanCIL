import CIL.Extraction.Parameters

/-!
# Storage from metadata types

Storage and callable representations of resolved metadata types used by extraction and execution.
-/

namespace CIL.Extraction

/-- The exact `System.Runtime.Intrinsics` assembly identity; `runtimeScope` is in `TypeExpr`. -/
def intrinsicsScope : String :=
  "System.Runtime.Intrinsics, Version=11.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

/-- Byte width of an admitted integer vector, bound to both exact runtime type identities. -/
def integerVectorWidth : TypeExpr → Option Nat
  | .apply (.constructor scope name) (.atom elementScope element) =>
    if scope != intrinsicsScope || elementScope != runtimeScope ||
        element ∉ ["System.Byte", "System.Int32", "System.UInt32", "System.Int64",
          "System.UInt64"] then none
    else if name == "System.Runtime.Intrinsics.Vector128`1" then some 16
    else if name == "System.Runtime.Intrinsics.Vector256`1" then some 32
    else if name == "System.Runtime.Intrinsics.Vector512`1" then some 64
    else none
  | _ => none

/-- The field type of a primitive runtime type, by full name. -/
private def primitiveField : String → Option FieldType
  | "System.SByte" => some .signed8 | "System.Byte" => some .unsigned8
  | "System.Boolean" => some .boolean | "System.Int16" => some .signed16
  | "System.UInt16" => some .unsigned16 | "System.Char" => some .character
  | "System.Int32" => some .signed32 | "System.UInt32" => some .unsigned32
  | "System.Int64" => some .signed64 | "System.UInt64" => some .unsigned64
  | "System.IntPtr" => some .nativeInt | "System.UIntPtr" => some .nativeUInt
  | _ => none

/-- The integer types an enum may have as its underlying type. -/
private def enumField : FieldType → Bool
  | .signed8 | .unsigned8 | .signed16 | .unsigned16 | .signed32 | .unsigned32
  | .signed64 | .unsigned64 => true
  | _ => false

/-- Primitive array element identity is derived from the exact runtime metadata scope. -/
def arrayElementType (type : TypeExpr) (aggregateWidth : Nat := 0) : Option ArrayElement :=
  match type with
  | .aggregate identity _ => some (.aggregate identity aggregateWidth)
  | type@(.apply (.constructor _ name) (.atom _ element)) => do
    let width ← integerVectorWidth type
    return .vector (name ++ "<" ++ element ++ ">") width
  | .enum identity (.atom scope name) => do
    if scope != runtimeScope then none else pure ()
    let storage ← match name with
      | "System.SByte" => some EnumStorage.signed8 | "System.Byte" => some .unsigned8
      | "System.Int16" => some .signed16 | "System.UInt16" => some .unsigned16
      | "System.Int32" => some .signed32 | "System.UInt32" => some .unsigned32
      | "System.Int64" => some .signed64 | "System.UInt64" => some .unsigned64
      | _ => none
    return .enumeration identity storage
  | .atom scope name =>
    if scope != runtimeScope then none else match name with
      | "System.SByte" => some .signed8 | "System.Byte" => some .unsigned8
      | "System.Int16" => some .signed16 | "System.UInt16" => some .unsigned16
      | "System.Int32" => some .signed32 | "System.UInt32" => some .unsigned32
      | "System.Int64" => some .signed64 | "System.UInt64" => some .unsigned64
      | "System.IntPtr" => some .nativeInt | "System.UIntPtr" => some .nativeUInt
      | "System.Boolean" => some .boolean | "System.Char" => some .character
      | _ => none
  | _ => none
/-- Primitive/vector widths are intrinsic; aggregate widths come from checked layout uses. -/
def spanElementWidth (type : TypeExpr) (aggregateWidth : Nat := 0) : Option Nat :=
  if let .aggregate .. := type then some aggregateWidth else
  ((arrayElementType type).map ArrayElement.width).orElse (fun _ => integerVectorWidth type)

/-- Exact span metadata, including element width and write capability. -/
def spanStorage (type : TypeExpr) (aggregateWidth : Nat := 0) : Option StorageType :=
  match type with
  | .apply (.constructor scope name) elementType => do
    if scope != runtimeScope ||
        name ∉ ["System.Span`1", "System.ReadOnlySpan`1"] then none else
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
    .functionPointer (callableType result) (callableType parameters) convention hasThis explicitThis
  | .signatureParameter head tail => .signatureParameter (callableType head) (callableType tail)
  | type => type

/-- Function pointers admit checked aggregates, integer vectors and integer/reference types. -/
def managedParameter : TypeExpr → Bool
  | .atom scope name => scope == runtimeScope && (primitiveField name).isSome
  | .enum _ (.atom scope name) => scope == runtimeScope &&
      ((primitiveField name).map enumField).getD false
  | .byref element => match element with
      | .atom .. | .enum .. | .aggregate .. | .apply .. => managedParameter element
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
def callableLayoutsValid (layouts : List RawLayout) : TypeExpr → Bool
  | .aggregate identity index => (layouts[index]?).any (·.identity == identity)
  | .byref element => callableLayoutsValid layouts element
  | .functionPointer result parameters _ _ _ =>
    callableLayoutsValid layouts result && callableLayoutsValid layouts parameters
  | .signatureParameter head tail =>
    callableLayoutsValid layouts head && callableLayoutsValid layouts tail
  | _ => true

/-- Decode storage independently from the exact metadata type identity. -/
def typeStorage (layouts : List RawLayout) : TypeExpr → Option StorageType
  | .atom scope name => if scope = runtimeScope then .field <$> primitiveField name else none
  | .object _ _ => some .object
  | .aggregate identity index => do
    let metadata ← layouts[index]?
    if metadata.identity = identity then return .field (.aggregate index) else none
  | .enum _ underlying => do
    let .field kind ← typeStorage layouts underlying | none
    if enumField kind then return .field kind else none
  | .byref _ => some .reference
  -- An array of class references is itself an object on the heap.
  | .array (.object _ _) => some .object
  | .array (.aggregate identity index) => do
    let metadata ← layouts[index]?
    if metadata.identity == identity && !metadata.byRefLike then
      some (.aggregateArray identity index) else none
  | .array element => match managedSignature element with
    | some signature => if callableLayoutsValid layouts element then some (.methodTable signature)
      else none
    | none => StorageType.array <$> arrayElementType element
  | type@(.functionPointer ..) => if callableLayoutsValid layouts type then
      StorageType.methodPointer <$> managedSignature type else none
  | .pointer (.atom scope name) =>
    if scope == runtimeScope && name ∈ ["System.SByte", "System.Byte", "System.Int16",
        "System.UInt16", "System.Char", "System.Int32", "System.UInt32", "System.Int64",
        "System.UInt64", "System.IntPtr", "System.UIntPtr"] then some .reference else none
  | .pointer (.enum identity underlying) => do
    let .field _ ← typeStorage layouts (.enum identity underlying) | none
    return .reference
  | .pointer (.aggregate identity index) => do
    let metadata ← layouts[index]?
    if metadata.identity == identity then some .reference else none
  | .pointer type => if (integerVectorWidth type).isSome then some .reference else none
  | type@(.apply (.constructor scope name) elementType) => do
    if let some storage := spanStorage type then
      if let .aggregate identity index := elementType then
        let metadata ← layouts[index]?
        if metadata.identity != identity then none else
          return .aggregateSpan index (name == "System.Span`1")
      else return storage
    let .atom elementScope element := elementType | none
    if scope != intrinsicsScope || elementScope != runtimeScope ||
        element ∉ ["System.UInt64", "System.Int64", "System.UInt32", "System.Int32",
          "System.Byte", "System.Double", "System.Single"] then none
    else if name = "System.Runtime.Intrinsics.Vector128`1" then some .vector128
    else if name = "System.Runtime.Intrinsics.Vector256`1" then some .vector256
    else if name = "System.Runtime.Intrinsics.Vector512`1" then some .vector512 else none
  | _ => none

end CIL.Extraction

