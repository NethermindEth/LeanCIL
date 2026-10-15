import CIL.Safety.Frames
namespace CIL.Safety
theorem expireAll_allocations (ids : List AllocationId) (m : Memory) (id : AllocationId) :
    (ids.foldl expire m).allocations id =
      if id ∈ ids then (m.allocations id).map (fun a => { a with live := false })
      else m.allocations id := by
  induction ids generalizing m with
  | nil => simp
  | cons head rest ih =>
    rw [List.foldl_cons, ih]
    by_cases h : id = head <;> by_cases hr : id ∈ rest <;>
      simp [expire, h, hr, Option.map_map, Function.comp_def]

theorem leaveFrame_expires_owned (frame : Frame) (m : Memory) (id : AllocationId)
    (owned : id ∈ frame.owned) (a : Allocation) (present : m.allocations id = some a) :
    liveAllocation (leaveFrame frame m) id = .error .expiredLifetime := by
  simp [liveAllocation, leaveFrame, expireAll_allocations, owned, present]
#print axioms expireAll_allocations
#print axioms leaveFrame_expires_owned
theorem allocateHome_preserves_wellFormed {alignment : Nat} (m result : Memory) (activation width : Nat)
    (reference : Reference) (hm : m.WellFormed)
    (h : allocateHome m activation width alignment = .ok (reference, result)) : result.WellFormed := by
  unfold allocateHome at h
  cases ha : allocate m ⟨.frame activation, ⟨width, alignment, []⟩, true, [width]⟩ with
  | error fault => simp [ha, checkedAt, Except.mapError, Bind.bind, Except.bind] at h
  | ok value =>
    obtain ⟨id, memory⟩ := value
    simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at h
    cases h
    have hw := allocate_preserves_wellFormed _ _ _ _ hm ha
    refine ⟨hw.1, ?_⟩
    intro view hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · have lookup := allocation_lookup m _ id memory ha
      exact ⟨_, lookup, by simp⟩
    · exact hw.2 view hv

theorem leaveFrame_preserves_wellFormed (frame : Frame) (m : Memory)
    (hm : m.WellFormed) : (leaveFrame frame m).WellFormed := by
  unfold leaveFrame
  generalize frame.owned = ids
  induction ids generalizing m with
  | nil => exact hm
  | cons id rest ih =>
    exact ih (expire m id) (expire_preserves_wellFormed m id hm)

#print axioms allocateHome_preserves_wellFormed
#print axioms leaveFrame_preserves_wellFormed

theorem storeLocal_preserves_wellFormed (m result : Memory) (slot final : LocalSlot)
    (value : Value) (hm : m.WellFormed)
    (h : storeLocal m slot value = .ok (final, result)) : result.WellFormed := by
  unfold storeLocal at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals repeat' first
    | exact hm
    | solve | exact write_preserves_wellFormed _ _ _ _ _ hm (checkedAt_ok (by assumption))
    | solve | exact writeSnapshot_preserves_wellFormed _ _ _ _ _ hm (checkedAt_ok (by assumption))
    | cases h
    | split at h
#print axioms storeLocal_preserves_wellFormed

end CIL.Safety
