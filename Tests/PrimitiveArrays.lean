import CIL.Safety.Execution
import CIL.Extraction.Translation

/-! # Supplied-array operations retain null, bounds, initialization and authority checks -/

namespace Tests.PrimitiveArrays
open CIL.Safety

private def rawArray (opcode : Nat) (operand : CIL.Extraction.RawOperand := .none) :
    CIL.Extraction.RawInstruction := ⟨0, opcode, operand⟩

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
    CIL.Extraction.scalarEmissionMatches none (rawArray 152) [.word32, .array .signed32]
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
      .error (.thrown "System.NullReferenceException") := rfl
#print axioms null_length

/-- The raw null literal has the same runtime array-null behavior. -/
theorem literal_null_length :
    memoryInstruction .arrayLength [.reference .null] memory =
      .error (.thrown "System.NullReferenceException") := rfl
#print axioms literal_null_length

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
      .error (.thrown "System.IndexOutOfRangeException") := rfl
#print axioms end_index_rejected

/-- Negative int32 indexes are out of bounds. -/
theorem negative_index_rejected :
    memoryInstruction (.arrayLoad 4 false) [.scalar (.i32 4294967295), .array words] memory =
      .error (.thrown "System.IndexOutOfRangeException") := rfl
#print axioms negative_index_rejected

/-- A high native index cannot wrap into the array. -/
theorem high_native_index_rejected :
    memoryInstruction (.arrayLoad 4 false)
      [.scalar (.i64 18446744073709551615), .array words] memory =
      .error (.thrown "System.IndexOutOfRangeException") := rfl
#print axioms high_native_index_rejected

/-- Null is checked before index bounds. -/
theorem null_before_bounds :
    memoryInstruction (.arrayLoad 4 false)
      [.scalar (.i32 4294967295), .array ⟨.null, 0, .signed32⟩] memory =
      .error (.thrown "System.NullReferenceException") := rfl
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
      let (slot, updated) ← storeLocal memory (.array .signed32 none) (.reference .null)
      loadLocal updated slot) = .ok (.array ⟨.null, 0, .signed32⟩) := rfl
#print axioms null_local_round_trip

end Tests.PrimitiveArrays
