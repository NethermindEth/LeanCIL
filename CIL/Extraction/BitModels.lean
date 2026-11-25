import CIL.Extraction.IntegerMath
import CIL.Extraction.SpanCalls

/-!
# Bit and byte-order helper models

`BitOperations.IsPow2`, `PopCount`, `LeadingZeroCount`, `TrailingZeroCount`, `Log2`,
`RoundUpToPowerOf2`, `RotateLeft` and `RotateRight`, the same helpers each integer type declares,
and `BinaryPrimitives.ReverseEndianness` are modelled by the scalar intrinsic of that operation
and width. Each entry covers one owner and name. Its resolve gives a model only to a static,
non-generic reference that takes one runtime integer type, followed by `System.Int32` for a
rotation, and returns the result its owner declares for that type: `System.Int32` for a count
of `BitOperations`, the integer type for a count the type declares, and `System.Boolean` for
`IsPow2`.
-/

namespace CIL.Extraction

/-- The modelled bit and byte-order helpers. -/
inductive BitHelper where
  | isPow2 | popCount | leadingZeroCount | trailingZeroCount | log2 | roundUpToPowerOf2
  | rotateLeft | rotateRight | reverseEndianness

/-- Where a helper is declared: `System.Numerics.BitOperations`, the integer type it takes, or
    `System.Buffers.Binary.BinaryPrimitives`. -/
inductive BitOwner where
  | bitOperations | integer | binaryPrimitives

/-- `System.Boolean`, the result of `IsPow2`. -/
def booleanType : TypeExpr := .primitive .boolean

/-- `System.Int32`, a rotation's count and the result of a count of `BitOperations`. -/
def int32Type : TypeExpr := .primitive .int32

/-- The result `owner` declares for `helper` on the integer `type` of `width` bits and
    `signed`ness, with the intrinsic the helper runs as; `none` where the owner declares no
    such helper on the type or it has no model. A count the type declares returns the type, as
    a 64-bit word at 64 bits and a 32-bit word otherwise; `Log2` of a signed type throws on a
    negative value and has no model, nor does a rotation of a signed 8- or 16-bit type. -/
def bitHelperModel (owner : BitOwner) (helper : BitHelper) (type : TypeExpr) (width : Nat)
    (signed : Bool) : Option (TypeExpr × ScalarIntrinsic) :=
  let wide := width == 32 || width == 64
  let count := if width == 64 then ScalarResultWidth.word64 else .word32
  match owner, helper with
  | .bitOperations, .isPow2 => if wide then some (booleanType, .isPow2 width signed) else none
  | .bitOperations, .popCount => if wide && !signed then some (int32Type, .popCount width .word32)
      else none
  | .bitOperations, .leadingZeroCount => if wide && !signed then
      some (int32Type, .leadingZeroCount width .word32) else none
  | .bitOperations, .trailingZeroCount => if wide && !signed then
      some (int32Type, .trailingZeroCount width .word32) else none
  | .bitOperations, .log2 => if wide && !signed then some (int32Type, .log2 width .word32)
      else none
  | .bitOperations, .roundUpToPowerOf2 => if wide && !signed then
      some (type, .roundUpToPowerOf2 width) else none
  | .bitOperations, .rotateLeft => if wide && !signed then some (type, .rotateLeft width)
      else none
  | .bitOperations, .rotateRight => if wide && !signed then some (type, .rotateRight width)
      else none
  | .integer, .isPow2 => some (booleanType, .isPow2 width signed)
  | .integer, .popCount => some (type, .popCount width count)
  | .integer, .leadingZeroCount => some (type, .leadingZeroCount width count)
  | .integer, .trailingZeroCount => some (type, .trailingZeroCount width count)
  | .integer, .log2 => if signed then none else some (type, .log2 width count)
  | .integer, .rotateLeft => if wide || !signed then some (type, .rotateLeft width) else none
  | .integer, .rotateRight => if wide || !signed then some (type, .rotateRight width) else none
  | .binaryPrimitives, .reverseEndianness => some (type, .reverseEndianness width signed)
  | _, _ => none

/-- The operation on the given parameter and result types. A rotation takes an additional
    `System.Int32` count. A primitive owner fixes the operand type. -/
def bitOperation (owner : BitOwner) (helper : BitHelper) (fixed : Option TypeExpr)
    (returned : TypeExpr) (parameters : List TypeExpr) : Option ScalarIntrinsic := do
  let type ← parameters.head?
  let rotation := match helper with | .rotateLeft | .rotateRight => true | _ => false
  if parameters != (if rotation then [type, int32Type] else [type]) then none
  if fixed.any (· != type) then none
  let .primitive primitive := type | none
  let (width, signed) ← mathIntegers.lookup primitive
  let (result, operation) ← bitHelperModel owner helper type width signed
  if returned != result then none
  some operation

/-- The model of a call of `method` as `helper` declared by `owner`: the scalar intrinsic
    `bitOperation` gives, on the call's arguments. -/
def bitModel (owner : BitOwner) (helper : BitHelper) (fixed : Option TypeExpr)
    (method : MethodRef) : Option RuntimeModel := do
  if method.hasThis || method.genericArity != 0 || !method.methodArguments.isEmpty then none
  let operation ← bitOperation owner helper fixed method.returnType method.parameters
  some (.intrinsic (.scalar operation) method.parameters.length)

/-- The helpers `BitOperations` and the integer types declare, by metadata name. -/
def bitHelpers : List (MetadataName × BitHelper) :=
  [(name!"IsPow2", .isPow2), (name!"PopCount", .popCount),
    (name!"LeadingZeroCount", .leadingZeroCount), (name!"TrailingZeroCount", .trailingZeroCount),
    (name!"Log2", .log2), (name!"RoundUpToPowerOf2", .roundUpToPowerOf2),
    (name!"RotateLeft", .rotateLeft), (name!"RotateRight", .rotateRight)]

/-- The `call` entry of `helper` named `name` and declared by `owner` as the type `declaring`,
    whose parameter must be `fixed` when given. -/
def bitEntry (owner : BitOwner) (declaring : TypeExpr) (fixed : Option TypeExpr)
    (helper : MetadataName × BitHelper) : ModelEntry :=
  .single .call declaring helper.1 (.declaration fun sig => sig.convention == 0 &&
    (bitOperation owner helper.2 fixed sig.returnType sig.parameters).isSome)
    (fun _ => bitModel owner helper.2 fixed)

/-- The helpers of `BitOperations`, those each integer type declares on itself, and
    `BinaryPrimitives.ReverseEndianness`. A type has an entry only for a helper it declares
    with a model. -/
def bitEntries : List ModelEntry :=
  bitHelpers.map
      (bitEntry .bitOperations (.atom runtimeScope "System.Numerics.BitOperations") none) ++
    mathIntegers.flatMap (fun (primitive, width, signed) =>
      let type := TypeExpr.primitive primitive
      (bitHelpers.filter fun helper =>
        (bitHelperModel .integer helper.2 type width signed).isSome).map
          (bitEntry .integer type (some type))) ++
    [bitEntry .binaryPrimitives
      (.atom spanMemoryScope "System.Buffers.Binary.BinaryPrimitives") none
      (name!"ReverseEndianness", .reverseEndianness)]

/-- Every model a bit helper entry resolves is an intrinsic, so a property every intrinsic model
    has holds of them. -/
theorem bitEntries_yields {property : RuntimeModel → Prop}
    (intrinsic : ∀ operation argc, property (.intrinsic operation argc)) :
    ∀ entry ∈ bitEntries, entry.Yields property := by
  intro entry member environment method model found
  have resolved : ∃ owner helper fixed, bitModel owner helper fixed method = some model := by
    simp only [bitEntries, bitEntry, List.mem_append, List.mem_map, List.mem_flatMap,
      List.mem_filter, List.mem_singleton] at member
    rcases member with (⟨helper, _, rfl⟩ | ⟨integer, _, helper, _, rfl⟩) | rfl
    · exact ⟨_, _, _, found⟩
    · exact ⟨_, _, _, found⟩
    · exact ⟨.binaryPrimitives, .reverseEndianness, none, found⟩
  rcases resolved with ⟨owner, helper, fixed, resolved⟩
  unfold bitModel at resolved
  split at resolved
  · contradiction
  obtain ⟨operation, _, same⟩ := Option.bind_eq_some_iff.mp resolved
  cases same
  exact intrinsic _ _

#print axioms bitEntries_yields

end CIL.Extraction
