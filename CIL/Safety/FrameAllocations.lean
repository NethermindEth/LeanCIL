import CIL.Safety.FrameOwnership

/-!
# Frame-owned allocations

The allocations a frame records as owned are live and belong to that activation, for each
frame builder in `CIL/Safety/Frames.lean` and for `enterFrame` as a whole. Projections of
`FrameSetup` from `CIL/Safety/FrameSetupLemmas.lean`.
-/

namespace CIL.Safety

theorem makeLocal_owned (m result : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    FrameAllocations result activation owned := by
  exact (makeLocal_setup _ _ _ _ _ _ _ h).allocations

theorem makeLocals_owned (m result : Memory) (activation : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (slots : List LocalSlot) (owned : List AllocationId)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    FrameAllocations result activation owned := by
  exact (makeLocals_setup _ _ _ _ _ _ _ h).allocations

#print axioms makeLocals_owned

theorem makeArgumentHomes_owned (m result : Memory) (activation : Nat) (indices : List Nat)
    (args : List Value) (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    FrameAllocations result activation owned := by
  exact (makeArgumentHomes_setup _ _ _ _ _ _ _ h).allocations

theorem makeParameterHomes_owned (m result : Memory) (activation : Nat)
    (parameters : List (Nat × CIL.LocalKind)) (args : List Value)
    (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeParameterHomes activation parameters args m = .ok (homes, owned, result)) :
    FrameAllocations result activation owned := by
  exact (makeParameterHomes_setup _ _ _ _ _ _ _ h).allocations

theorem enterFrame_owned (body : CIL.Method) (args : List Value) (m result : Memory)
    (frame : Frame) (h : enterFrame body args m = .ok (frame, result)) :
    FrameAllocations result frame.activation frame.owned := by
  exact (enterFrame_setup _ _ _ _ _ h).allocations

#print axioms enterFrame_owned
end CIL.Safety
