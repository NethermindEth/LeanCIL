import CIL.Safety.Memory

namespace CIL.Safety

theorem readableRange_iff (m : Memory) (r : Reference) (width : Nat) :
    readableRange m r width = true ↔
      ∀ i < width, permitted m false { r with offset := r.offset + i } = true := by
  constructor
  · intro covered i bound
    simp only [readableRange, Bool.or_eq_true, beq_iff_eq] at covered
    rcases covered with (zero | single) | fragmented
    · omega
    · obtain ⟨view, member, readable, same, start, finish⟩ := by
        simpa only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using single
      apply List.any_eq_true.mpr
      refine ⟨view, member, ?_⟩
      simp only [viewContains, Bool.false_eq_true, ↓reduceIte, readable, Bool.and_true, decide_eq_true_eq]
      exact ⟨same, by omega, by omega⟩
    · exact List.all_eq_true.mp fragmented i (List.mem_range.mpr bound)
  · intro covered
    simp only [readableRange, Bool.or_eq_true]
    right
    exact List.all_eq_true.mpr (fun i member => covered i (List.mem_range.mp member))

/-- Omitting a redundant readable view preserves both kinds of authority at
    every address, including addresses outside the written interval. -/
theorem writeViews_permitted (m : Memory) (r : Reference) (width : Nat)
    (writing : Bool) (q : Reference) :
    permitted { m with views := writeViews m r width } writing q =
      permitted { m with views := ⟨r.allocation, r.offset, width, true, false⟩ :: m.views } writing q := by
  unfold writeViews
  split
  · rename_i covered
    cases writing
    · by_cases inside : r.allocation = q.allocation ∧ r.offset ≤ q.offset ∧ q.offset < r.offset + width
      · have permission := (readableRange_iff m r width).mp covered (q.offset - r.offset) (by omega)
        have same : { r with offset := r.offset + (q.offset - r.offset) } = q := by
          cases r; cases q; simp_all <;> omega
        rw [same] at permission
        simp [permitted, viewContains, inside] at permission ⊢
        exact permission
      · simp [permitted, viewContains, inside]
    · simp [permitted]
  · rfl

theorem writeViews_length_le (m : Memory) (r : Reference) (width : Nat) :
    (writeViews m r width).length ≤ m.views.length + 1 := by
  unfold writeViews
  split <;> simp

#print axioms readableRange_iff
#print axioms writeViews_permitted
end CIL.Safety
