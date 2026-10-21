import CIL.Safety.FrameSetupContracts
namespace CIL.Safety

theorem makeLocal_preserves_wellFormed (m result : Memory) (activation : Nat)
    (kind : CIL.LocalKind) (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId)
    (hm : m.WellFormed) (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    result.WellFormed := by
  exact (makeLocal_setup _ _ _ _ _ _ _ h).wellFormed hm

theorem makeLocals_preserves_wellFormed (m result : Memory) (activation : Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value)
    (slots : List LocalSlot) (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    result.WellFormed := by
  exact (makeLocals_setup _ _ _ _ _ _ _ h).wellFormed hm

#print axioms makeLocal_preserves_wellFormed
#print axioms makeLocals_preserves_wellFormed

theorem makeArgumentHomes_preserves_wellFormed (m result : Memory) (activation : Nat)
    (indices : List Nat) (args : List Value) (homes : List (Nat × LocalSlot))
    (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    result.WellFormed := by
  exact (makeArgumentHomes_setup _ _ _ _ _ _ _ h).wellFormed hm

theorem makeParameterHomes_preserves_wellFormed (m result : Memory) (activation : Nat)
    (parameters : List (Nat × CIL.LocalKind)) (args : List Value)
    (homes : List (Nat × LocalSlot)) (owned : List AllocationId) (hm : m.WellFormed)
    (h : makeParameterHomes activation parameters args m = .ok (homes, owned, result)) :
    result.WellFormed := by
  exact (makeParameterHomes_setup _ _ _ _ _ _ _ h).wellFormed hm

theorem enterFrame_preserves_wellFormed (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame) (hm : m.WellFormed)
    (h : enterFrame body args m = .ok (frame, result)) : result.WellFormed := by
  exact (enterFrame_setup _ _ _ _ _ h).wellFormed hm

#print axioms makeArgumentHomes_preserves_wellFormed
#print axioms enterFrame_preserves_wellFormed
end CIL.Safety
