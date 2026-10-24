import CIL.Safety.Execution

/-! # Span values across interpreter calls, locals and frame lifetimes -/

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
  code := [.arg 0, .const32 3, .const32 0, .memory (.spanSlice true), .memory .spanLength, .ret]
  locals := [], returnsValue := true }

theorem end_empty_slice :
    (invoke [emptyLength] 16 0 [.bufferSpan view] memory).map Prod.snd =
      .ok [.scalar (.i32 0)] := rfl
#print axioms end_empty_slice

theorem invalid_index :
    (invoke [reader] 16 0 [.bufferSpan view, .scalar (.i32 3)] memory).map Prod.snd =
      .error ⟨0, 2, .thrown "System.IndexOutOfRangeException"⟩ := rfl
#print axioms invalid_index

private def illegalWriter : Method := {
  code := [.arg 0, .const32 0, .memory (.spanItem 4), .const32 1, .storeScalar 4, .ret]
  locals := [], returnsValue := false }

theorem readonly_reference_rejects_store :
    (invoke [illegalWriter] 16 0 [.bufferSpan view] memory).map Prod.snd =
      .error ⟨0, 4, .memory .unwritable (.address ⟨0, 0⟩) 4⟩ := rfl
#print axioms readonly_reference_rejects_store

private def escaping : Method := {
  code := [.localAddr 0, .const32 1, .memory (.spanFromReference 4 true), .ret]
  locals := [.i32 7], localKinds := [.word32], returnsValue := true }

theorem expired_local_cannot_escape :
    (invoke [escaping] 16 0 [] memory).map Prod.snd =
      .error ⟨0, 3, .memory .expiredLifetime (.address ⟨1, 0⟩) 0⟩ := rfl
#print axioms expired_local_cannot_escape

end Tests.MemorySpanExecution
