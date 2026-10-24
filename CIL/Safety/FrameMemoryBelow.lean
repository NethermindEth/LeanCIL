import CIL.Safety.MemoryBelow
import CIL.Safety.FrameOwnership

/-!
# Frame setup leaves caller memory alone

Building a frame changes nothing below the entry watermark `m.nextIdentity`: allocation
metadata, bytes and permissions of every older allocation are exactly preserved. This is
what lets a caller's facts about its own memory survive a call.
-/

namespace CIL.Safety

theorem store_numeric_local_preserves_memory_below (m result : Memory) (kind : CIL.LocalKind)
    (r : Reference) (value : CIL.Value) (slot : LocalSlot) (watermark : Nat)
    (fresh : watermark ≤ r.allocation)
    (h : storeLocal m (.bytes kind r) (.scalar value) = .ok (slot, result)) :
    MemoryBelow watermark m result := by
  exact storeLocal_memory_below (slot := .bytes kind r) fresh h

theorem makeLocal_preserves_caller_memory (m result : Memory) (activation : Nat)
    (kind : CIL.LocalKind) (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    MemoryBelow m.nextIdentity m result := by
  exact (makeLocal_setup _ _ _ _ _ _ _ h).below

theorem makeLocals_preserves_caller_memory (m result : Memory) (activation : Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value)
    (slots : List LocalSlot) (owned : List AllocationId)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    MemoryBelow m.nextIdentity m result := by
  exact (makeLocals_setup _ _ _ _ _ _ _ h).below

theorem makeArgumentHomes_preserves_caller_memory (m result : Memory) (activation : Nat)
    (indices : List Nat) (args : List Value) (homes : List (Nat × LocalSlot))
    (owned : List AllocationId)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    MemoryBelow m.nextIdentity m result := by
  exact (makeArgumentHomes_setup _ _ _ _ _ _ _ h).below

theorem initialize_parameter_preserves_caller_memory (m home result : Memory) (activation : Nat)
    (kind : CIL.LocalKind) (slot final : LocalSlot) (owned : List AllocationId) (value : Value)
    (made : makeLocal activation kind .unmodeled m = .ok (slot, owned, home))
    (stored : storeLocal home slot value = .ok (final, result)) :
    MemoryBelow m.nextIdentity m result := by
  exact ((makeLocal_setup _ _ _ _ _ _ _ made).store stored).below

theorem makeParameterHomes_preserves_caller_memory (m result : Memory) (activation : Nat)
    (parameters : List (Nat × CIL.LocalKind)) (args : List Value)
    (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeParameterHomes activation parameters args m = .ok (homes, owned, result)) :
    MemoryBelow m.nextIdentity m result := by
  exact (makeParameterHomes_setup _ _ _ _ _ _ _ h).below

theorem enterFrame_preserves_caller_memory (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame)
    (h : enterFrame body args m = .ok (frame, result)) : MemoryBelow m.nextIdentity m result := by
  exact (enterFrame_setup _ _ _ _ _ h).below

#print axioms allocateHome_preserves_caller_memory
#print axioms makeLocal_preserves_caller_memory
#print axioms makeLocals_preserves_caller_memory
#print axioms makeArgumentHomes_preserves_caller_memory
#print axioms enterFrame_preserves_caller_memory

end CIL.Safety
