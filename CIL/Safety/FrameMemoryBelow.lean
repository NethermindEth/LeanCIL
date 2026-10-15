import CIL.Safety.MemoryBelow
import CIL.Safety.FrameOwnership

namespace CIL.Safety

theorem allocateHome_preserves_caller_memory {alignment : Nat} (m result : Memory) (activation width : Nat) (r : Reference)
    (h : allocateHome m activation width alignment = .ok (r, result)) : MemoryBelow m.nextIdentity m result := by
  unfold allocateHome at h
  cases ha : allocate m ⟨.frame activation, ⟨width, alignment, []⟩, true, [width]⟩ <;>
    simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at h
  · cases h
  · rename_i home
    obtain ⟨id, memory⟩ := home
    cases h
    apply (allocate_preserves_memory_below _ _ _ _ ha).trans
    apply prepend_view_preserves_memory_below
    change m.nextIdentity ≤ id
    rw [(allocation_identity_fresh _ _ _ _ ha).1]
    exact Nat.le_refl _

theorem store_numeric_local_preserves_memory_below (m result : Memory) (kind : CIL.LocalKind)
    (r : Reference) (value : CIL.Value) (slot : LocalSlot) (watermark : Nat)
    (fresh : watermark ≤ r.allocation)
    (h : storeLocal m (.bytes kind r) (.scalar value) = .ok (slot, result)) :
    MemoryBelow watermark m result := by
  cases value <;> simp only [storeLocal] at h
  all_goals repeat' first
    | solve | exact write_preserves_memory_below _ _ _ _ _ _ fresh (checkedAt_ok (by assumption))
    | solve | exact writeSnapshot_preserves_memory_below _ _ _ _ _ _ fresh (checkedAt_ok (by assumption))
    | cases h
    | split at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
theorem makeLocal_preserves_caller_memory (m result : Memory) (activation : Nat)
    (kind : CIL.LocalKind) (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    MemoryBelow m.nextIdentity m result := by
  unfold makeLocal at h
  split at h
  · split at h
    · cases h; exact .refl _ _
    · cases h; exact .refl _ _
    · cases h
  all_goals
    cases ha : allocateHome m activation (localWidth kind) (localAlignment kind) <;>
      simp only [ha, Bind.bind, Except.bind] at h
    · cases h
    · rename_i home
      obtain ⟨reference, memory⟩ := home
      have preserved := allocateHome_preserves_caller_memory _ _ _ _ _ ha
      have fresh := (allocateHome_fresh _ _ _ _ _ ha).2.1
      split at h
      · simp only [Pure.pure, Except.pure] at h
        cases h
        exact preserved
      · cases hs : storeLocal memory (.bytes kind reference) (.scalar initial) <;>
          simp only [hs, Pure.pure, Except.pure] at h
        · cases h
        · rename_i stored
          obtain ⟨slot, result⟩ := stored
          cases h
          exact preserved.trans (store_numeric_local_preserves_memory_below _ _ _ _ _ _ _ (Nat.le_of_eq fresh.symm) hs)

theorem makeLocals_preserves_caller_memory (m result : Memory) (activation : Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value)
    (slots : List LocalSlot) (owned : List AllocationId)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    MemoryBelow m.nextIdentity m result := by
  induction kinds generalizing initializers m slots owned result with
  | nil =>
    cases initializers
    · cases h; exact .refl _ _
    · cases h
  | cons kind kinds ih =>
    cases initializers with
    | nil => cases h
    | cons initial initials =>
      simp only [makeLocals] at h
      cases hl : makeLocal activation kind initial m <;>
        simp only [hl, Bind.bind, Except.bind] at h
      · cases h
      · rename_i home
        obtain ⟨slot, ids, memory⟩ := home
        cases hr : makeLocals activation kinds initials memory <;>
          simp only [hr, Pure.pure, Except.pure] at h
        · cases h
        · rename_i rest
          obtain ⟨rest, other, final⟩ := rest
          cases h
          exact (makeLocal_preserves_caller_memory _ _ _ _ _ _ _ hl).trans
            ((ih memory final initials rest other hr).weaken (makeLocal_fresh _ _ _ _ _ _ _ hl).1.next)

theorem makeArgumentHomes_preserves_caller_memory (m result : Memory) (activation : Nat)
    (indices : List Nat) (args : List Value) (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    MemoryBelow m.nextIdentity m result := by
  induction indices generalizing m homes owned result with
  | nil => cases h; exact .refl _ _
  | cons index indices ih =>
    simp only [makeArgumentHomes] at h
    split at h
    · rename_i bits argument
      cases ha : allocateHome m activation (localWidth .vector256) <;>
        simp only [ha, Bind.bind, Except.bind] at h
      · cases h
      · rename_i home
        obtain ⟨reference, memory⟩ := home
        cases hs : storeLocal memory (.bytes .vector256 reference) (.scalar (.v256 bits)) <;>
          simp only [hs] at h
        · cases h
        · rename_i stored
          obtain ⟨slot, stored⟩ := stored
          cases hr : makeArgumentHomes activation indices args stored <;>
            simp only [hr, Pure.pure, Except.pure] at h
          · cases h
          · rename_i rest
            obtain ⟨rest, other, final⟩ := rest
            cases h
            have fresh := allocateHome_fresh _ _ _ _ _ ha
            have ext := fresh.1.trans (storeLocal_extends_allocations _ _ _ _ _ hs)
            exact ((allocateHome_preserves_caller_memory _ _ _ _ _ ha).trans
              (store_numeric_local_preserves_memory_below _ _ _ _ _ _ _ (Nat.le_of_eq fresh.2.1.symm) hs)).trans
              ((ih stored final rest other hr).weaken ext.next)
    · cases h

theorem initialize_parameter_preserves_caller_memory (m home result : Memory) (activation : Nat)
    (kind : CIL.LocalKind) (slot final : LocalSlot) (owned : List AllocationId) (value : Value)
    (made : makeLocal activation kind .unmodeled m = .ok (slot, owned, home))
    (stored : storeLocal home slot value = .ok (final, result)) :
    MemoryBelow m.nextIdentity m result := by
  unfold makeLocal at made
  split at made
  · cases made
    cases value with
    | scalar value => cases stored
    | span r length => cases stored
    | reference r =>
      simp only [storeLocal] at stored
      cases hf : formValue m r <;>
        simp only [hf, Bind.bind, Except.bind, Pure.pure, Except.pure] at stored
      · cases stored
      · cases stored; exact .refl _ _
  all_goals
    cases ha : allocateHome m activation (localWidth kind) (localAlignment kind) <;>
      simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at made
    · cases made
    · rename_i allocation
      obtain ⟨reference, memory⟩ := allocation
      cases made
      cases value with
      | reference r => cases stored
      | span r length => cases stored
      | scalar value =>
        exact (allocateHome_preserves_caller_memory _ _ _ _ _ ha).trans
          (store_numeric_local_preserves_memory_below _ _ _ _ _ _ _
            (Nat.le_of_eq (allocateHome_fresh _ _ _ _ _ ha).2.1.symm) stored)

theorem makeParameterHomes_preserves_caller_memory (m result : Memory) (activation : Nat)
    (parameters : List (Nat × CIL.LocalKind)) (args : List Value)
    (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeParameterHomes activation parameters args m = .ok (homes, owned, result)) :
    MemoryBelow m.nextIdentity m result := by
  induction parameters generalizing m homes owned result with
  | nil => cases h; exact .refl _ _
  | cons parameter parameters ih =>
    obtain ⟨index, kind⟩ := parameter
    simp only [makeParameterHomes] at h
    split at h
    · rename_i value argument
      cases hl : makeLocal activation kind .unmodeled m <;>
        simp only [hl, Bind.bind, Except.bind] at h
      · cases h
      · rename_i made
        obtain ⟨slot, ids, memory⟩ := made
        cases hs : storeLocal memory slot value <;> simp only [hs] at h
        · cases h
        · rename_i stored
          obtain ⟨slot', memory'⟩ := stored
          have first := initialize_parameter_preserves_caller_memory _ _ _ _ _ _ _ _ _ hl hs
          have ext := (makeLocal_fresh _ _ _ _ _ _ _ hl).1.trans
            (storeLocal_extends_allocations _ _ _ _ _ hs)
          cases hr : makeParameterHomes activation parameters args memory' <;>
            simp only [hr, Pure.pure, Except.pure] at h
          · cases h
          · rename_i remaining
            obtain ⟨rest, other, final⟩ := remaining
            cases h
            exact first.trans ((ih memory' final rest other hr).weaken ext.next)
    · cases h

theorem enterFrame_preserves_caller_memory (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame)
    (h : enterFrame body args m = .ok (frame, result)) : MemoryBelow m.nextIdentity m result := by
  simp only [enterFrame] at h
  cases hl : makeLocals m.nextIdentity body.localKinds body.locals m <;>
    simp only [hl, Bind.bind, Except.bind] at h
  · cases h
  · rename_i locals
    obtain ⟨slots, owned, memory⟩ := locals
    cases ha : makeArgumentHomes m.nextIdentity body.vectorArgs args memory <;>
      simp only [ha, Pure.pure, Except.pure] at h
    · cases h
    · rename_i homes
      obtain ⟨arguments, ids, final⟩ := homes
      have first := (makeLocals_preserves_caller_memory _ _ _ _ _ _ _ hl).trans
        ((makeArgumentHomes_preserves_caller_memory _ _ _ _ _ _ _ ha).weaken
          (makeLocals_fresh _ _ _ _ _ _ _ hl).1.next)
      have ext := (makeLocals_fresh _ _ _ _ _ _ _ hl).1.trans
        (makeArgumentHomes_fresh _ _ _ _ _ _ _ ha).1
      cases hp : makeParameterHomes m.nextIdentity body.parameterHomes args final <;>
        simp only [hp] at h
      · cases h
      · rename_i parameters
        obtain ⟨parameters, ids, final'⟩ := parameters
        cases h
        exact first.trans ((makeParameterHomes_preserves_caller_memory _ _ _ _ _ _ _ hp).weaken ext.next)

#print axioms allocateHome_preserves_caller_memory
#print axioms makeLocal_preserves_caller_memory
#print axioms makeLocals_preserves_caller_memory
#print axioms makeArgumentHomes_preserves_caller_memory
#print axioms enterFrame_preserves_caller_memory

end CIL.Safety
