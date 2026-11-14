import CIL.Safety.Execution

/-! # Span values across interpreter calls, locals and frame lifetimes

Also the `Vector128.LoadUnsafe` and `StoreUnsafe` byte transfers over one 32-byte allocation:
the offset form reaches the second half, one byte further is outside the allocation, and a
store needs a writable reference and a vector. -/

namespace Tests.MemorySpanExecution
open CIL CIL.Safety

private def memory : Safety.Memory := {
  allocations := fun identity => if identity == 0 then
    some ⟨.callerStack, ⟨12, 1, []⟩, true, []⟩ else none
  cells := fun _ offset => ⟨if offset == 4 then 7 else 0, true⟩
  views := [⟨0, 0, 12, true, true⟩]
  nextIdentity := 1 }

private def view : SpanView := ⟨.address ⟨0, 0⟩, 3, 4, false⟩

private def reader : Method := {
  code := [.arg 0, .arg 1, .memory (.spanItem 4), .loadScalar 4, .ret]
  locals := [], returnsValue := true }

private def caller : Method := {
  code := [.arg 0, .setLocal 0, .local 0, .arg 1, .arg 2, .memory (.spanSlice true),
    .arg 3, .call 1 2, .ret]
  locals := [.nullRef], localKinds := [.span 4 false], returnsValue := true }

theorem local_slice_and_call :
    (invoke [caller, reader] 32 0
      [.bufferSpan view, .scalar (.i32 1), .scalar (.i32 2), .scalar (.i32 0)] memory).map Prod.snd =
      .ok [.scalar (.i32 7)] := rfl
#print axioms local_slice_and_call

private def emptyLength : Method := {
  code := [.arg 0, .ldc_i4 3, .ldc_i4 0, .memory (.spanSlice true), .memory .spanLength, .ret]
  locals := [], returnsValue := true }

theorem end_empty_slice :
    (invoke [emptyLength] 16 0 [.bufferSpan view] memory).map Prod.snd =
      .ok [.scalar (.i32 0)] := rfl
#print axioms end_empty_slice

/-- Invalid slice ranges report the specified runtime exception before any element access. -/
theorem invalid_slice_ranges :
    memoryInstruction (.spanSlice true)
      [.scalar (.i32 0), .scalar (.i32 4), .bufferSpan view] memory =
        .error (.thrown "System.ArgumentOutOfRangeException") ∧
    memoryInstruction (.spanSlice true)
      [.scalar (.i32 2), .scalar (.i32 2), .bufferSpan view] memory =
        .error (.thrown "System.ArgumentOutOfRangeException") ∧
    memoryInstruction (.spanSlice true)
      [.scalar (.i32 0), .scalar (.i32 4294967295), .bufferSpan view] memory =
        .error (.thrown "System.ArgumentOutOfRangeException") := by
  exact ⟨rfl, rfl, rfl⟩
#print axioms invalid_slice_ranges

/-- A default empty span can be sliced and queried without a backing allocation. -/
theorem null_empty_slice :
    memoryInstruction (.spanSlice true)
      [.scalar (.i32 0), .scalar (.i32 0), .bufferSpan ⟨.null, 0, 4, false⟩] memory =
        .ok (memory, [.bufferSpan ⟨.null, 0, 4, false⟩]) := rfl
#print axioms null_empty_slice

theorem invalid_index :
    (invoke [reader] 16 0 [.bufferSpan view, .scalar (.i32 3)] memory).map Prod.snd =
      .error ⟨0, 2, .thrown "System.IndexOutOfRangeException"⟩ := rfl
#print axioms invalid_index

private def illegalWriter : Method := {
  code := [.arg 0, .ldc_i4 0, .memory (.spanItem 4), .ldc_i4 1, .storeScalar 4, .ret]
  locals := [], returnsValue := false }

theorem readonly_reference_rejects_store :
    (invoke [illegalWriter] 16 0 [.bufferSpan view] memory).map Prod.snd =
      .error ⟨0, 4, .memory .unwritable (.address ⟨0, 0⟩) 4⟩ := rfl
#print axioms readonly_reference_rejects_store

private def escaping : Method := {
  code := [.localAddr 0, .ldc_i4 1, .memory (.spanFromReference 4 true), .ret]
  locals := [.i32 7], localKinds := [.word32], returnsValue := true }

theorem expired_local_cannot_escape :
    (invoke [escaping] 16 0 [] memory).map Prod.snd =
      .error ⟨0, 3, .memory .expiredLifetime (.address ⟨1, 0⟩) 0⟩ := rfl
#print axioms expired_local_cannot_escape

/-- Thirty-two writable bytes, byte `i` holding `i`. -/
private def counting : Safety.Memory := {
  allocations := fun identity => if identity == 0 then
    some ⟨.callerStack, ⟨32, 1, []⟩, true, []⟩ else none
  cells := fun _ offset => ⟨BitVec.ofNat 8 offset, true⟩
  views := [⟨0, 0, 32, true, true⟩]
  nextIdentity := 1 }

/-- The start of the allocation. -/
private def start : ManagedReference := .address ⟨0, 0⟩

/-- Loads read sixteen little-endian bytes at the byte offset, through either reference kind;
    sixteen bytes past offset 17 would cross the end of the allocation. -/
theorem vector128_loads :
    (memoryInstruction (.vector128Unsafe false false) [.reference start] counting).map Prod.snd =
      .ok [.scalar (.v128 0x0f0e0d0c0b0a09080706050403020100)] ∧
    (memoryInstruction (.vector128Unsafe false true)
      [.scalar (.i64 16), .readOnlyReference start] counting).map Prod.snd =
      .ok [.scalar (.v128 0x1f1e1d1c1b1a19181716151413121110)] ∧
    memoryInstruction (.vector128Unsafe false true)
      [.scalar (.i64 17), .readOnlyReference start] counting =
      .error (.memory .outsideAllocation (.address ⟨0, 17⟩) 16) := by
  exact ⟨rfl, rfl, rfl⟩
#print axioms vector128_loads

/-- A store at offset 16 writes the vector's bytes low first and leaves the first half alone. -/
theorem vector128_store_at :
    (memoryInstruction (.vector128Unsafe true true)
      [.scalar (.i64 16), .reference start, .scalar (.v128 0xaabbccddeeff00112233445566778899)]
      counting).map (fun (written, stack) =>
        ((List.range 32).map fun offset => (written.cells 0 offset).1.toNat, stack)) =
      .ok ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x00, 0xff, 0xee, 0xdd, 0xcc, 0xbb,
        0xaa], []) := by
  rfl
#print axioms vector128_store_at

/-- A store past the end, through a readonly reference, or of a non-vector value faults. -/
theorem vector128_store_faults :
    memoryInstruction (.vector128Unsafe true true)
      [.scalar (.i64 17), .reference start, .scalar (.v128 0)] counting =
      .error (.memory .outsideAllocation (.address ⟨0, 17⟩) 16) ∧
    memoryInstruction (.vector128Unsafe true false)
      [.readOnlyReference start, .scalar (.v128 0)] counting =
      .error (.memory .unwritable start 16) ∧
    memoryInstruction (.vector128Unsafe true false) [.reference start, .scalar (.i64 0)] counting =
      .error .invalidState := by
  exact ⟨rfl, rfl, rfl⟩
#print axioms vector128_store_faults

end Tests.MemorySpanExecution
