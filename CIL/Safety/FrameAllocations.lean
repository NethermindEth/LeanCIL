import CIL.Safety.FrameOwnership

/-!
# Frame-owned allocations

The allocations a frame records as owned are live and belong to that activation, for
`makeLocals` in `CIL/Safety/Frames.lean` and for `enterFrame` as a whole. Projections of
`FrameSetup` from `CIL/Safety/FrameSetupLemmas.lean`.
-/

namespace CIL.Safety

theorem makeLocals_owned (m result : Memory) (activation : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (slots : List LocalSlot) (owned : List AllocationId)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    FrameAllocations result activation owned := by
  exact (makeLocals_setup _ _ _ _ _ _ _ h).allocations

#print axioms makeLocals_owned

theorem enterFrame_owned (body : CIL.Method) (args : List Value) (m result : Memory)
    (frame : Frame) (h : enterFrame body args m = .ok (frame, result)) :
    FrameAllocations result frame.activation frame.owned := by
  exact (enterFrame_setup _ _ _ _ _ h).allocations

#print axioms enterFrame_owned
end CIL.Safety
