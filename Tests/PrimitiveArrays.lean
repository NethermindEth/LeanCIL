import CIL.Safety.Execution
import CIL.Safety.ObjectSteps
import CIL.Safety.SymbolicExecution
import CIL.Extraction.Translation

/-! # Supplied-array operations retain null, bounds, initialization and authority checks -/

namespace Tests.PrimitiveArrays
open CIL.Safety

private def rawArray (opcode : Nat) (operand : CIL.Extraction.RawOperand := .none) :
    CIL.Extraction.RawInstruction := ⟨0, opcode, operand⟩

/-- The element type `System.Int32`. -/
private def int32 : CIL.Extraction.TypeExpr := .atom CIL.Extraction.runtimeScope "System.Int32"

/-- The struct `Record`, at layout index 0. -/
private def record : CIL.Extraction.TypeExpr := .aggregate "Record" 0

/-- A typed load cannot claim an element token differing from the supplied array type. -/
theorem wrong_element_token :
    CIL.Extraction.scalarOpMatches
      (rawArray 163 (.type (.atom CIL.Extraction.runtimeScope "System.UInt32")))
      [.word32, .array .signed32] (.memory (.arrayLoad 4 false)) = false := by decide +kernel
#print axioms wrong_element_token

/-- Equal physical widths do not make native and fixed-width array accesses interchangeable. -/
theorem native_element_mismatch :
    CIL.Extraction.scalarOpMatches (rawArray 151) [.word32, .array .signed64]
      (.memory (.arrayLoad 8 false)) = false := by decide +kernel
#print axioms native_element_mismatch

/-- A native-width array store requires a native stack value, not an int64 claim. -/
theorem native_store_mismatch :
    CIL.Extraction.scalarOpMatches (rawArray 155) [.word64, .word32, .array .nativeInt]
      (.memory (.arrayStore 8)) = false := by decide +kernel
#print axioms native_store_mismatch

/-- Unsupported floating-point loads cannot certify an integer load via equal stack effects. -/
theorem float_load_forgery :
    CIL.Extraction.scalarEmissionMatches #[] none (rawArray 152) [.word32, .array .signed32]
      (.memory (.arrayLoad 4 false)) = false := by decide +kernel
#print axioms float_load_forgery

/-- An ordinary int64 is not a valid array index in raw CIL stack evidence. -/
theorem invalid_index_kind :
    CIL.Extraction.scalarOpMatches (rawArray 148) [.word64, .array .signed32]
      (.memory (.arrayLoad 4 false)) = false := by decide +kernel
#print axioms invalid_index_kind

private def memory : Memory := {
  allocations := fun identity =>
    if identity == 0 then some ⟨.managedHeap, ⟨16, 8, []⟩, true, [16]⟩
    else if identity == 1 then some ⟨.managedHeap, ⟨0, 8, []⟩, true, [0]⟩ else none
  cells := fun _ offset => ⟨if offset == 0 then 255 else 0, true⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 2 }

private def words : ArrayView := ⟨.address ⟨0, 0⟩, 4, .signed32⟩
private def bytes : ArrayView := ⟨.address ⟨0, 0⟩, 16, .signed8⟩
private def noAuthority : Memory := { memory with views := [] }
private def uninitialized : Memory := { memory with cells := fun _ _ => ⟨0, false⟩ }

/-- Distinct high-bit bytes distinguish load widths, byte order and narrow sign extension. -/
private def numericMemory : Memory :=
  { memory with cells := fun _ offset =>
      { bits := BitVec.ofNat 8 (128 + offset), initialized := true } }

/-- Every admitted numeric suffix, including distinct signed and unsigned encodings. -/
private def numericKinds : List CIL.NumericKind := [.i1, .u1, .i2, .u2, .i4, .u4, .i8, .i]

/-- The `ldind` of a kind. -/
private def numericLoad (kind : CIL.NumericKind) : MemoryStep := instruction (.ldind kind)

/-- Every suffix loads its exact value, with sign or zero extension for the narrow kinds. -/
theorem numeric_kind_load_values :
    numericKinds.map (fun kind =>
      (numericLoad kind [.reference (.address { allocation := 0, offset := 0 })]
        numericMemory).map Prod.snd) =
    [.ok [.scalar (.i32 0xFFFFFF80)], .ok [.scalar (.i32 0x80)],
      .ok [.scalar (.i32 0xFFFF8180)], .ok [.scalar (.i32 0x8180)],
      .ok [.scalar (.i32 0x83828180)], .ok [.scalar (.i32 0x83828180)],
      .ok [.scalar (.i64 0x8786858483828180)],
      .ok [.scalar (.i64 0x8786858483828180)]] := rfl
#print axioms numeric_kind_load_values

/-- The `stind` of a kind. -/
private def numericStore (kind : CIL.NumericKind) : MemoryStep := instruction (.stind kind)

/-- Each store keeps the low bytes in little-endian order and preserves the following bytes. -/
theorem numeric_kind_store_bytes :
    ([(.i1, .i32 0x44332211), (.u1, .i32 0x44332211),
      (.i2, .i32 0x44332211), (.u2, .i32 0x44332211),
      (.i4, .i32 0x44332211), (.u4, .i32 0x44332211),
      (.i8, .i64 0x8877665544332211), (.i, .i64 0x8877665544332211)] :
      List (Prod CIL.NumericKind CIL.Value)).map (fun (kind, value) => do
        let (stored, _) <- numericStore kind
          [.scalar value, .reference (.address { allocation := 0, offset := 0 })] numericMemory
        checkedAt (.address { allocation := 0, offset := 0 }) 8
          (read stored { allocation := 0, offset := 0 } 8 1)) =
    [.ok [0x11, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87],
      .ok [0x11, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87],
      .ok [0x11, 0x22, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87],
      .ok [0x11, 0x22, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87],
      .ok [0x11, 0x22, 0x33, 0x44, 0x84, 0x85, 0x86, 0x87],
      .ok [0x11, 0x22, 0x33, 0x44, 0x84, 0x85, 0x86, 0x87],
      .ok [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
      .ok [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]] := rfl
#print axioms numeric_kind_store_bytes

/-- Length is native-sized and does not read array data or require read authority. -/
theorem length_without_authority :
    memoryInstruction .arrayLength [.array words] noAuthority =
      .ok (noAuthority, [.scalar (.i64 4)]) := rfl
#print axioms length_without_authority

/-- A non-null empty array has length zero. -/
theorem empty_length :
    memoryInstruction .arrayLength [.array ⟨.address ⟨1, 0⟩, 0, .signed32⟩] memory =
      .ok (memory, [.scalar (.i64 0)]) := rfl
#print axioms empty_length

/-- Null is distinct from an empty array and raises the named runtime exception. -/
theorem null_length :
    memoryInstruction .arrayLength [.array ⟨.null, 0, .signed32⟩] memory =
      .error (.thrown .nullReference) := rfl
#print axioms null_length

/-- The raw null literal has the same runtime array-null behavior. -/
theorem literal_null_length :
    memoryInstruction .arrayLength [.object .null] memory =
      .error (.thrown .nullReference) := rfl
#print axioms literal_null_length

/-- A null byref, as `Unsafe.NullRef` produces, is not an array and has no length. -/
theorem byref_null_not_array :
    memoryInstruction .arrayLength [.reference .null] memory = .error .invalidState := rfl
#print axioms byref_null_not_array

/-- Narrow signed loads extend the stored byte. -/
theorem signed_byte_read :
    memoryInstruction (.arrayLoad 1 true) [.scalar (.i32 0), .array bytes] memory =
      .ok (memory, [.scalar (.i32 4294967295)]) := rfl
#print axioms signed_byte_read

/-- The unsigned encoding reads the same byte without sign extension. -/
theorem unsigned_byte_read :
    memoryInstruction (.arrayLoad 1 false) [.scalar (.i32 0), .array bytes] memory =
      .ok (memory, [.scalar (.i32 255)]) := rfl
#print axioms unsigned_byte_read

/-- Native indices are accepted without truncating them to int32. -/
theorem native_index :
    memoryInstruction (.arrayLoad 4 false) [.scalar (.i64 0), .array words] memory =
      .ok (memory, [.scalar (.i32 255)]) := rfl
#print axioms native_index

/-- Index equal to length is outside the array even if its address could be a sentinel. -/
theorem end_index_rejected :
    memoryInstruction (.arrayLoad 4 false) [.scalar (.i32 4), .array words] memory =
      .error (.thrown .indexOutOfRange) := rfl
#print axioms end_index_rejected

/-- Negative int32 indexes are out of bounds. -/
theorem negative_index_rejected :
    memoryInstruction (.arrayLoad 4 false) [.scalar (.i32 4294967295), .array words] memory =
      .error (.thrown .indexOutOfRange) := rfl
#print axioms negative_index_rejected

/-- A high native index cannot wrap into the array. -/
theorem high_native_index_rejected :
    memoryInstruction (.arrayLoad 4 false)
      [.scalar (.i64 18446744073709551615), .array words] memory =
      .error (.thrown .indexOutOfRange) := rfl
#print axioms high_native_index_rejected

/-- Null is checked before index bounds. -/
theorem null_before_bounds :
    memoryInstruction (.arrayLoad 4 false)
      [.scalar (.i32 4294967295), .array ⟨.null, 0, .signed32⟩] memory =
      .error (.thrown .nullReference) := rfl
#print axioms null_before_bounds

/-- Array shape does not grant read authority. -/
theorem unreadable_rejected :
    memoryInstruction (.arrayLoad 4 false) [.scalar (.i32 0), .array words] noAuthority =
      .error (.memory .unreadable (.address ⟨0, 0⟩) 4) := rfl
#print axioms unreadable_rejected

/-- An array value cannot make uninitialized data readable. -/
theorem uninitialized_rejected :
    memoryInstruction (.arrayLoad 4 false) [.scalar (.i32 0), .array words] uninitialized =
      .error (.memory .uninitialized (.address ⟨0, 0⟩) 4) := rfl
#print axioms uninitialized_rejected

/-- Writes need authority even though the array itself has no readonly-view flag. -/
theorem unwritable_rejected :
    memoryInstruction (.arrayStore 4) [.scalar (.i32 7), .scalar (.i32 1), .array words]
      noAuthority = .error (.memory .unwritable (.address ⟨0, 4⟩) 4) := rfl
#print axioms unwritable_rejected

/-- The selected element is initialized by a store without reading its previous contents. -/
theorem store_initializes_element :
    (do
      let (updated, _) ← memoryInstruction (.arrayStore 4)
        [.scalar (.i32 305419896), .scalar (.i32 1), .array words] uninitialized
      memoryInstruction (.arrayLoad 4 false) [.scalar (.i32 1), .array words] updated :
        ExecutionResult (Memory × List Value)).map Prod.snd = .ok [.scalar (.i32 305419896)] := rfl
#print axioms store_initializes_element

/-- Bytes on both sides of the updated element retain their initial values. -/
theorem store_preserves_neighbors :
    (memoryInstruction (.arrayStore 4)
      [.scalar (.i32 7), .scalar (.i32 1), .array words] memory).map
        (fun (updated, _) => (updated.cells 0 0, updated.cells 0 8)) =
      .ok (memory.cells 0 0, memory.cells 0 8) := rfl
#print axioms store_preserves_neighbors

/-- A valid array cannot be read using an unrelated element width. -/
theorem wrong_width_rejected :
    memoryInstruction (.arrayLoad 8 false) [.scalar (.i32 0), .array words] memory =
      .error .invalidState := rfl
#print axioms wrong_width_rejected

/-- Invalid backing extents fail as model errors, not as expected runtime exceptions. -/
theorem invalid_extent_rejected :
    memoryInstruction .arrayLength [.array { words with length := 5 }] memory =
      .error (.memory .outsideAllocation (.address ⟨0, 0⟩) 0) := rfl
#print axioms invalid_extent_rejected

/-- Array homes preserve the element identity and shape across local stores and loads. -/
theorem array_local_round_trip :
    (do
      let (slot, updated) ← storeLocal memory (.array .signed32 none) (.array words)
      loadLocal updated slot) = .ok (.array words) := rfl
#print axioms array_local_round_trip

/-- A null literal stored in a typed array home becomes that array type's null value. -/
theorem null_local_round_trip :
    (do
      let (slot, updated) ← storeLocal memory (.array .signed32 none) (.object .null)
      loadLocal updated slot) = .ok (.array ⟨.null, 0, .signed32⟩) := rfl
#print axioms null_local_round_trip

/-- The maximum modeled payload initializes without enumerating its elements. -/
theorem allocation_maximum_constant_initialization :
    (match allocateArray memory .unsigned8 maxArrayLength with
     | .ok (view, result) => view.length == maxArrayLength &&
         (result.cells memory.nextIdentity (maxArrayLength - 1)).initialized &&
         (result.cells memory.nextIdentity (maxArrayLength - 1)).bits == 0
     | .error _ => false) = true := by decide +kernel
#print axioms allocation_maximum_constant_initialization

/-- Lengths outside the runtime element-count ceiling remain model failures, not CLR throws. -/
theorem allocation_extent_is_not_exception :
    (match newArray memory .signed32 (.i64 (maxArrayLength + 1)) with
     | .error fault => fault == .unsupported "Array length outside supported extent"
     | .ok _ => false) = true := by decide +kernel
#print axioms allocation_extent_is_not_exception

/-- A forged allocator watermark is rejected instead of establishing an allocation exception. -/
theorem allocation_identity_reuse_is_not_exception :
    (match newArray { memory with nextIdentity := 0 } .signed32 (.i32 2) with
     | .error fault => fault == .memory .identityReuse .null 8
     | .ok _ => false) = true := by decide +kernel
#print axioms allocation_identity_reuse_is_not_exception

/-- Native negative lengths retain the CLI overflow exception. -/
theorem native_negative_array_length :
    (match newArray memory .signed32 (.i64 (2^63)) with
     | .error fault => fault == .thrown .overflow
     | .ok _ => false) = true := by decide +kernel
#print axioms native_negative_array_length

/-- Unsupported element extents cannot claim an expected exception through their length. -/
theorem unsupported_allocation_is_not_exception :
    (match newArray memory (.aggregate "Record" (2^16)) (.i32 (-1)) with
     | .error fault => fault == .unsupported "Unsupported array element allocation"
     | .ok _ => false) = true := by decide +kernel
#print axioms unsupported_allocation_is_not_exception

/-- A zero-width composite cannot form an array even when its length is zero. -/
theorem zero_width_allocation_rejected :
    (newArray memory (.aggregate "Record" 0) (.i32 0)).isOk = false := rfl
#print axioms zero_width_allocation_rejected

/-- Maximum supported component size and count stay bounded without materializing cells. -/
theorem composite_maximum_constant_initialization :
    (match allocateArray memory (.aggregate "Record" (2^16 - 1)) maxArrayLength with
     | .ok (view, result) => view.length == maxArrayLength &&
         (view.validate result).isOk &&
         (result.cells memory.nextIdentity (maxArrayLength * (2^16 - 1) - 1)).initialized &&
         (result.cells memory.nextIdentity 0).bits == 0
     | .error _ => false) = true := by decide +kernel
#print axioms composite_maximum_constant_initialization

/-- Ref-like containment is accepted only when the enclosing struct is also ref-like. -/
theorem byref_like_layout_containment :
    let child : CIL.Extraction.RawLayout :=
      { identity := "Child", explicit := false, packing := 0, declaredSize := 0,
        fields := [], byRefLike := true }
    let parent : CIL.Extraction.RawLayout :=
      { identity := "Parent", explicit := false, packing := 0, declaredSize := 0,
        fields := [⟨.aggregate 0, none⟩] }
    (CIL.Extraction.computeLayouts [child, { parent with byRefLike := true }]).isSome = true ∧
      CIL.Extraction.computeLayouts [child, parent] = none := by decide +kernel
#print axioms byref_like_layout_containment

/-- Native length operands certify, while raw int64 stack kinds do not. -/
theorem allocation_native_kind :
    CIL.Extraction.scalarOpMatches
      (rawArray 141 (.type (.atom CIL.Extraction.runtimeScope "System.Int32")))
      [.native] (.newarr int32) = true ∧
    CIL.Extraction.scalarOpMatches
      (rawArray 141 (.type (.atom CIL.Extraction.runtimeScope "System.Int32")))
      [.word64] (.newarr int32) = false := by decide +kernel
#print axioms allocation_native_kind

/-- `newarr` carries the raw token itself: another element type, even one of equal width, or
    the same struct under another identity or layout index, does not match it. -/
theorem allocation_token_mismatch :
    CIL.Extraction.scalarOpMatches (rawArray 141 (.type int32)) [.word32]
      (.newarr (.atom CIL.Extraction.runtimeScope "System.UInt32")) = false ∧
    CIL.Extraction.scalarOpMatches (rawArray 141 (.type record)) [.word32]
      (.newarr (.aggregate "Other" 0)) = false ∧
    CIL.Extraction.scalarOpMatches (rawArray 141 (.type record)) [.word32]
      (.newarr (.aggregate "Record" 1)) = false ∧
    CIL.Extraction.scalarOpMatches (rawArray 141 (.type record)) [.word32]
      (.newarr record) = true := by decide +kernel
#print axioms allocation_token_mismatch

/-- Checked layouts holding one 5-byte struct under the identity `Record`. -/
private def recordEnvironment : CIL.LayoutEnvironment :=
  { rawLayouts :=
      [{ identity := "Record", explicit := false, packing := 0, declaredSize := 0, fields := [] }]
    layouts := #[⟨⟨5, []⟩, 1⟩] }

/-- `newarr` of two `Record` elements in a body over `recordEnvironment`. -/
@[cil_code] def aggregating : CIL.Method :=
  { returnsValue := true, locals := [], environment := recordEnvironment,
    code := [.ldc_i4 2, .newarr record, .ret] }

/-- A struct array takes its stride from the body's checked layout, not from the instruction;
    without a layout entry for the struct the allocation is outside the model. -/
theorem aggregate_stride_from_environment :
    (match invoke [aggregating] 8 0 [] memory with
     | .ok (after, [.array view]) => view.elementType == .aggregate "Record" 5 &&
         view.length == 2 && (view.validate after).isOk
     | _ => false) = true ∧
    invoke [{ aggregating with environment := { recordEnvironment with layouts := #[] } }]
        8 0 [] memory = .error ⟨0, 1, .unsupported CIL.ElementShape.outsideLayouts⟩ :=
  ⟨by decide +kernel, rfl⟩
#print axioms aggregate_stride_from_environment

/-- A `newarr` step reduces through the body's element shape to a value allocation of the
    checked stride. -/
theorem aggregate_allocation_step (frame : Frame) (rest : List Value) :
    step aggregating (.newarr record) 1 [] frame (.scalar (.i32 2) :: rest) memory = do
      let (view, allocated) ← newArray memory (.aggregate "Record" 5) (.i32 2)
      return .next 2 (.array view :: rest) frame allocated := by
  simp only [cil_step, bind_assoc, pure_bind, Nat.reduceAdd]
#print axioms aggregate_allocation_step

end Tests.PrimitiveArrays
