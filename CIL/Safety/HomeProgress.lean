import CIL.Safety.AccessRequirements
import CIL.Safety.LiveState

namespace CIL.Safety

theorem allocateHome_succeeds {alignment : Nat} (m : Memory) (activation width : Nat)
    (wellFormed : m.WellFormed) (bounded : width < nativeLimit) (positive : 0 < alignment) :
    ∃ reference memory, allocateHome m activation width alignment = .ok (reference, memory) := by
  have unused := wellFormed_next_unused m wellFormed
  have valid : (Allocation.mk (.frame activation) ⟨width, alignment, []⟩ true [width]).valid = true := by
    simp [Allocation.valid, bounded, positive]
  simp only [allocateHome, allocate, valid, Bool.not_true, Bool.false_eq_true,
    ite_false, unused, Option.isSome_none, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem allocateHome_write_access {alignment : Nat} (m result : Memory) (activation width : Nat) (r : Reference)
    (h : allocateHome m activation width alignment = .ok (r, result)) :
    AccessRequirements result r width 1 true
      ⟨.frame activation, ⟨width, alignment, []⟩, true, [width]⟩ := by
  unfold allocateHome at h
  cases ha : allocate m ⟨.frame activation, ⟨width, alignment, []⟩, true, [width]⟩ <;>
    simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at h
  · cases h
  · rename_i home
    obtain ⟨id, memory⟩ := home
    cases h
    have lookup := allocation_lookup m _ id memory ha
    have position : 0 < width ∨ 0 = width := by omega
    refine ⟨lookup, rfl, ?_, ?_, by simp, by simp [Nat.mod_one], ?_, ?_⟩
    · simp [validPosition, nativeLimit, position]
    · simp
    · simp
    · intro i bound
      apply permitted_by_view (view := ⟨id, 0, width, true, true⟩)
      · exact List.mem_cons_self
      · rfl
      · simp
      · simpa using bound
      · rfl

theorem fresh_home_storeLocal_succeeds (m result : Memory) (activation : Nat)
    (kind : CIL.LocalKind) (r : Reference) (value : CIL.Value) (number : Nat)
    (home : allocateHome m activation (localWidth kind) (localAlignment kind) = .ok (r, result))
    (fits : localNumber kind value = .ok number) :
    ∃ slot stored, storeLocal result (.bytes kind r) (.scalar value) = .ok (slot, stored) := by
  have accessOK := (allocateHome_write_access _ _ _ _ _ home).access
  have width : (numberBytes number (localWidth kind)).length = localWidth kind := by
    simp [numberBytes]
  have writable : access result r (numberBytes number (localWidth kind)).length 1 true = .ok () := by
    simpa only [width] using accessOK
  cases value
  case snapshot shape bytes => cases kind <;> simp [localNumber, CIL.Value.hasUnspecified] at fits
  case v128Low64 low => simp [localNumber, CIL.Value.hasUnspecified] at fits
  all_goals simp only [storeLocal, fits, write, writable, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals exact ⟨_, _, rfl⟩

#print axioms allocateHome_succeeds
#print axioms allocateHome_write_access
#print axioms fresh_home_storeLocal_succeeds

end CIL.Safety
