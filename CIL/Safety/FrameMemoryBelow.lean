import CIL.Safety.MemoryBelow
import CIL.Safety.FrameOwnership

/-!
# Frame setup leaves caller memory alone

Building a frame changes nothing below the entry watermark `m.nextIdentity`: allocation
metadata, bytes and permissions of every older allocation are exactly preserved. This is
what lets a caller's facts about its own memory survive a call.
-/

namespace CIL.Safety

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

theorem enterFrame_preserves_caller_memory (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame)
    (h : enterFrame body args m = .ok (frame, result)) : MemoryBelow m.nextIdentity m result := by
  exact (enterFrame_setup _ _ _ _ _ h).below

#print axioms allocateHome_preserves_caller_memory
#print axioms makeLocal_preserves_caller_memory
#print axioms makeLocals_preserves_caller_memory
#print axioms enterFrame_preserves_caller_memory

/-- A valid view of well-formed memory addresses an existing allocation, so it stays valid in any
    memory that keeps everything below the watermark, such as a callee frame's memory. -/
theorem SpanView.validate_below (view : SpanView) {before after : Memory}
    (valid : view.validate before = .ok ()) (wellFormed : before.WellFormed)
    (kept : MemoryBelow before.nextIdentity before after) : view.validate after = .ok () := by
  cases address : view.reference with
  | null => simpa only [SpanView.validate, address] using valid
  | address base =>
    cases present : before.allocations base.allocation with
    | none =>
      simp only [SpanView.validate, address, liveAllocation, present] at valid
      repeat' first
        | contradiction
        | split at valid
        | simp_all [Bind.bind, Except.bind, Pure.pure, Except.pure]
    | some allocation =>
      have old := (wellFormed.allocations _ _ present).1
      simpa only [SpanView.validate, address, liveAllocation, kept.allocations _ old] using valid
#print axioms SpanView.validate_below

end CIL.Safety
