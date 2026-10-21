import CIL.Safety.FrameSetupLemmas
import CIL.Safety.AllocationExtension
namespace CIL.Safety

theorem makeLocal_fresh (m result : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    FreshOwned m result owned := by
  exact (makeLocal_setup _ _ _ _ _ _ _ h).fresh

#print axioms makeLocal_fresh

theorem makeLocals_fresh (m result : Memory) (activation : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (slots : List LocalSlot) (owned : List AllocationId)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    FreshOwned m result owned := by
  exact (makeLocals_setup _ _ _ _ _ _ _ h).fresh

theorem makeArgumentHomes_fresh (m result : Memory) (activation : Nat) (indices : List Nat)
    (args : List Value) (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    FreshOwned m result owned := by
  exact (makeArgumentHomes_setup _ _ _ _ _ _ _ h).fresh

theorem makeParameterHomes_fresh (m result : Memory) (activation : Nat)
    (parameters : List (Nat × CIL.LocalKind)) (args : List Value)
    (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeParameterHomes activation parameters args m = .ok (homes, owned, result)) :
    FreshOwned m result owned := by
  exact (makeParameterHomes_setup _ _ _ _ _ _ _ h).fresh

theorem enterFrame_fresh (body : CIL.Method) (args : List Value) (m result : Memory) (frame : Frame)
    (h : enterFrame body args m = .ok (frame, result)) : FreshOwned m result frame.owned := by
  exact (enterFrame_setup _ _ _ _ _ h).fresh

theorem leaveFrame_preserves_older_allocations (frame : Frame) (m : Memory) (watermark : Nat)
    (fresh : ∀ id ∈ frame.owned, watermark ≤ id) (id : AllocationId) (old : id < watermark) :
    (leaveFrame frame m).allocations id = m.allocations id := by
  have notOwned : id ∉ frame.owned := by
    intro owned
    exact Nat.not_lt_of_ge (fresh id owned) old
  simp [leaveFrame, expireAll_allocations, notOwned]

theorem frame_entry_exit_preserves_caller (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame) (id : AllocationId)
    (h : enterFrame body args m = .ok (frame, result)) (old : id < m.nextIdentity) :
    (leaveFrame frame result).allocations id = m.allocations id := by
  have fresh := enterFrame_fresh _ _ _ _ _ h
  rw [leaveFrame_preserves_older_allocations frame result m.nextIdentity
    (fun id member => (fresh.2 id member).1) id old]
  exact fresh.1.lookup id old

#print axioms enterFrame_fresh
#print axioms leaveFrame_preserves_older_allocations
#print axioms frame_entry_exit_preserves_caller

theorem frame_entry_exit_preserves_reference (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame) (r formed : Reference) (hm : m.WellFormed)
    (enter : enterFrame body args m = .ok (frame, result)) (valid : form m r = .ok formed) :
    form (leaveFrame frame result) r = .ok formed := by
  obtain ⟨a, present, _, _⟩ := formed_reference_live _ _ _ valid
  have old := (hm.1 _ _ present).1
  rw [form_allocation_congr _ _ _ (frame_entry_exit_preserves_caller _ _ _ _ _ _ enter old)]
  exact valid

#print axioms frame_entry_exit_preserves_reference

theorem expireAll_retained_fields (ids : List AllocationId) (m : Memory) :
    (ids.foldl expire m).cells = m.cells ∧ (ids.foldl expire m).views = m.views ∧
    (ids.foldl expire m).staticBindings = m.staticBindings ∧
    (ids.foldl expire m).nextIdentity = m.nextIdentity := by
  induction ids generalizing m with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons id ids ih => exact ih (expire m id)
end CIL.Safety
