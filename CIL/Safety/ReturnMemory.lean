import CIL.Safety.FrameMemoryBelow

/-!
# Caller memory across a call

Leaving a frame expires only the identities that frame owns, so `MemoryBelow` (memory older
than a watermark is unchanged) survives teardown. Composed with frame entry this gives the
round trip that call-composition proofs use to keep caller facts across a callee.
-/

namespace CIL.Safety

/-- Teardown expires only owned identities; it preserves all earlier memory
    metadata, bytes, initialization and access authority. -/
theorem leaveFrame_preserves_memory_below (frame : Frame) (memory : Memory) (watermark : Nat)
    (owned : ∀ id ∈ frame.owned, watermark ≤ id) :
    MemoryBelow watermark memory (leaveFrame frame memory) := by
  have retained := expireAll_retained_fields frame.owned memory
  refine ⟨leaveFrame_preserves_older_allocations frame memory watermark owned, ?_, ?_⟩
  · intro id _ offset
    exact congrFun (congrFun retained.1 id) offset
  · intro id _ offset writing
    simp only [permitted, leaveFrame, retained.2.1]

#print axioms leaveFrame_preserves_memory_below

/-- A call keeps caller memory if its body does: frame entry and teardown touch only fresh
    identities. -/
theorem MemoryBelow.frame_round_trip {body : CIL.Method} {args : List Value}
    {m entered updated : Memory} {frame : Frame}
    (enter : enterFrame body args m = .ok (frame, entered))
    (inside : MemoryBelow m.nextIdentity entered updated) :
    MemoryBelow m.nextIdentity m (leaveFrame frame updated) :=
  ((enterFrame_preserves_caller_memory _ _ _ _ _ enter).trans inside).trans
    (leaveFrame_preserves_memory_below frame updated _ fun id member =>
      ((enterFrame_fresh _ _ _ _ _ enter).2 id member).1)

#print axioms MemoryBelow.frame_round_trip

end CIL.Safety
