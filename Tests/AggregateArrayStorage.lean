import CIL.Safety.Execution
import CIL.Extraction.Translation

/-! Supplied aggregate arrays preserve masks, authority, lifetimes and exact element identity. -/

namespace Tests.AggregateArrayStorage
open CIL.Safety

private def element : CIL.ArrayElement := .aggregate "Pair" 16
private def view : ArrayView := ⟨.address ⟨0, 0⟩, 2, element⟩
private def mask : List (BitVec 8 × Bool) :=
  List.replicate 8 (7, true) ++ List.replicate 8 (0, false)
private def memory : Memory := {
  allocations := fun identity => if identity == 0 then
    some ⟨.callerStack, ⟨48, 16, []⟩, true, [48]⟩ else none
  cells := fun _ _ => ⟨3, true⟩
  views := [⟨0, 0, 48, true, true⟩]
  nextIdentity := 1 }

/-- Aggregate stores preserve an uninitialized suffix and both neighbouring regions. -/
theorem masked_store :
    (memoryInstruction (.arrayTransfer element true)
      [.scalar (.snapshot (.aggregate 16) mask), .scalar (.i32 1), .array view] memory).map
      (fun result => ((result.1.cells 0 0).bits, (result.1.cells 0 16).bits,
        (result.1.cells 0 24).initialized, (result.1.cells 0 32).bits)) =
      .ok (3, 7, false, 3) := rfl
#print axioms masked_store

/-- Aggregate loads retain initialization masks instead of inventing readable bytes. -/
theorem masked_load :
    (memoryInstruction (.arrayTransfer element false) [.scalar (.i32 0), .array view]
      { memory with cells := fun _ offset => if offset < 8 then ⟨7, true⟩ else ⟨0, false⟩ }).map
      Prod.snd = .ok [.scalar (.snapshot (.aggregate 16) mask)] := rfl
#print axioms masked_load

/-- A typed write still requires authority over the destination bytes. -/
theorem missing_authority :
    (memoryInstruction (.arrayTransfer element true)
      [.scalar (.aggregate (List.replicate 16 0)), .scalar (.i32 0), .array view]
      { memory with views := [] }).isOk = false := rfl
#print axioms missing_authority

/-- Equal-sized vector and struct storage cannot be interchanged by an array instruction. -/
theorem wrong_identity :
    memoryInstruction (.arrayTransfer (.vector "Vector128<UInt64>" 16) false)
      [.scalar (.i32 0), .array view] memory = .error .invalidState := rfl
#print axioms wrong_identity

/-- Array indexing preserves named bounds exceptions. -/
theorem past_end :
    memoryInstruction (.arrayTransfer element false) [.scalar (.i32 2), .array view] memory =
      .error (.thrown "System.IndexOutOfRangeException") := rfl
#print axioms past_end

/-- Expired storage cannot yield a typed element, even when its bytes remain present. -/
theorem expired :
    (memoryInstruction (.arrayTransfer element false) [.scalar (.i32 0), .array view]
      { memory with allocations := fun _ => some ⟨.callerStack, ⟨48, 16, []⟩, false, [48]⟩ }).isOk =
      false := rfl
#print axioms expired

/-- A readonly element address retains its restriction on subsequent writes. -/
theorem readonly_address :
    memoryInstruction (.arrayAddress element false) [.scalar (.i32 1), .array view] memory =
      .ok (memory, [.readOnlyReference (.address ⟨0, 16⟩)]) := rfl
#print axioms readonly_address

/-- Empty slices at the end preserve allocation identity and need no readable contents. -/
theorem empty_slice :
    (memoryInstruction (.arraySpan element true .counted)
      [.scalar (.i32 0), .scalar (.i32 2), .array view] { memory with views := [] }).map
      Prod.snd = .ok [.bufferSpan ⟨.address ⟨0, 32⟩, 0, 16, true⟩] := rfl
#print axioms empty_slice

/-- Array metadata with a forged extent is rejected before dereferencing any element. -/
theorem invalid_extent :
    (memoryInstruction (.arrayTransfer element false)
      [.scalar (.i32 0), .array { view with length := 4 }] memory).isOk = false := rfl
#print axioms invalid_extent

end Tests.AggregateArrayStorage
