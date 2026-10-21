import CIL.Safety.FrameEffects

namespace CIL.Safety

/-- Byte homes are allocated after the entry watermark; roots do not own bytes. -/
def LocalSlot.Above (watermark : Nat) : LocalSlot → Prop
  | .root _ => True
  | .bytes _ r => watermark ≤ r.allocation

theorem write_staticBindings {m result : Memory} {r : Reference} {bytes : List (BitVec 8)}
    {alignment : Nat} (h : write m r bytes alignment = .ok result) :
    result.staticBindings = m.staticBindings := by
  unfold write at h
  cases ha : access m r bytes.length alignment true <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h; rfl

theorem writeSnapshot_staticBindings {m result : Memory} {r : Reference}
    {bytes : List (BitVec 8 × Bool)} {alignment : Nat}
    (h : writeSnapshot m r bytes alignment = .ok result) : result.staticBindings = m.staticBindings := by
  unfold writeSnapshot at h
  cases hw : write m r (bytes.map Prod.fst) alignment <;>
    simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    have registry := write_staticBindings hw
    exact registry

theorem storeLocal_staticBindings {m result : Memory} {slot final : LocalSlot} {value : Value}
    (h : storeLocal m slot value = .ok (final, result)) : result.staticBindings = m.staticBindings := by
  unfold storeLocal at h
  repeat' first
    | rfl
    | solve | exact write_staticBindings (checkedAt_ok (by assumption))
    | solve | exact writeSnapshot_staticBindings (checkedAt_ok (by assumption))
    | cases h
    | split at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h

theorem storeLocal_above {m result : Memory} {slot final : LocalSlot} {value : Value} {watermark : Nat}
    (above : slot.Above watermark) (h : storeLocal m slot value = .ok (final, result)) :
    final.Above watermark := by
  unfold storeLocal at h
  repeat' first
    | exact above
    | exact True.intro
    | cases h
    | split at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h

theorem storeLocal_memory_below {m result : Memory} {slot final : LocalSlot} {value : Value}
    {watermark : Nat} (above : slot.Above watermark)
    (h : storeLocal m slot value = .ok (final, result)) : MemoryBelow watermark m result := by
  unfold storeLocal at h
  repeat' first
    | exact .refl _ _
    | solve | exact write_preserves_memory_below _ _ _ _ _ _ above (checkedAt_ok (by assumption))
    | solve | exact writeSnapshot_preserves_memory_below _ _ _ _ _ _ above (checkedAt_ok (by assumption))
    | cases h
    | split at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h

theorem formValue_root_valid {m : Memory} {r : ManagedReference} {value : Value}
    (h : formValue m r = .ok value) : (LocalSlot.root (some r)).ReferencesValid m := by
  cases r with
  | null => trivial
  | address r =>
    cases hf : form m r <;>
      simp only [formValue, hf, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at h
    · cases h
    · have same := form_preserves_provenance _ _ _ hf
      subst_vars
      exact hf

theorem storeLocal_preserves_reference_validity (m result : Memory) (slot final : LocalSlot)
    (value : Value) (hm : m.WellFormed) (valid : slot.ReferencesValid m)
    (h : storeLocal m slot value = .ok (final, result)) : final.ReferencesValid result := by
  have retained := valid.preserve hm (storeLocal_extends_allocations _ _ _ _ _ h)
  unfold storeLocal at h
  repeat' first
    | exact retained
    | solve | exact formValue_root_valid (by assumption)
    | cases h
    | split at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h

/-- The effects of setup, independent of the traversal that produced the homes.
    Conditional fields preserve the original contracts on malformed input memory. -/
structure FrameSetup (activation : Nat) (before after : Memory)
    (slots : List LocalSlot) (owned : List AllocationId) : Prop where
  fresh : FreshOwned before after owned
  allocations : FrameAllocations after activation owned
  below : MemoryBelow before.nextIdentity before after
  registry : after.staticBindings = before.staticBindings
  wellFormed : before.WellFormed → after.WellFormed
  references : before.WellFormed → SlotsReferencesValid after slots
  above : ∀ slot ∈ slots, slot.Above before.nextIdentity

theorem FrameSetup.empty (activation : Nat) (m : Memory) : FrameSetup activation m m [] [] :=
  ⟨⟨.refl _, by simp⟩, by simp [FrameAllocations], .refl _ _, rfl, id,
    by simp [SlotsReferencesValid], by simp⟩

/-- Compose effects once; clients project their required invariant. -/
theorem FrameSetup.append {activation : Nat} {first middle last : Memory}
    {left right : List LocalSlot} {leftIds rightIds : List AllocationId}
    (a : FrameSetup activation first middle left leftIds)
    (b : FrameSetup activation middle last right rightIds) :
    FrameSetup activation first last (left ++ right) (leftIds ++ rightIds) := by
  refine ⟨a.fresh.trans b.fresh,
    (a.allocations.preserve b.fresh.1 (fun id member => (a.fresh.2 id member).2)).append b.allocations,
    a.below.trans (b.below.weaken a.fresh.1.next), b.registry.trans a.registry,
    fun hm => b.wellFormed (a.wellFormed hm), ?_, ?_⟩
  · intro hm slot member
    rcases List.mem_append.mp member with member | member
    · exact (a.references hm slot member).preserve (a.wellFormed hm) b.fresh.1
    · exact b.references (a.wellFormed hm) slot member
  · intro slot member
    rcases List.mem_append.mp member with member | member
    · exact a.above slot member
    · have bound := b.above slot member
      cases slot with
      | root _ => trivial
      | bytes _ _ => exact Nat.le_trans a.fresh.1.next bound

theorem allocateHome_setup {alignment : Nat} (m result : Memory) (activation width : Nat)
    (r : Reference) (kind : CIL.LocalKind)
    (h : allocateHome m activation width alignment = .ok (r, result)) :
    FrameSetup activation m result [.bytes kind r] [r.allocation] := by
  have fresh := allocateHome_fresh _ _ _ _ _ h
  refine ⟨⟨fresh.1, ?_⟩, allocateHome_owned _ _ _ _ _ h,
    allocateHome_preserves_caller_memory _ _ _ _ _ h, ?_,
    fun hm => allocateHome_preserves_wellFormed _ _ _ _ _ hm h, ?_, ?_⟩
  · intro id member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨Nat.le_of_eq fresh.2.1.symm, fresh.2.2⟩
  · unfold allocateHome at h
    cases ha : allocate m ⟨.frame activation, ⟨width, alignment, []⟩, true, [width]⟩ <;>
      simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    · cases h
    · cases h
      unfold allocate at ha
      repeat' first | rfl | cases ha | split at ha
  · intro _ slot member
    obtain rfl := List.mem_singleton.mp member
    exact allocateHome_reference_valid _ _ _ _ _ h
  · intro slot member
    obtain rfl := List.mem_singleton.mp member
    exact Nat.le_of_eq fresh.2.1.symm

theorem FrameSetup.store {activation : Nat} {before home result : Memory}
    {slot final : LocalSlot} {owned : List AllocationId} {value : Value}
    (setup : FrameSetup activation before home [slot] owned)
    (h : storeLocal home slot value = .ok (final, result)) :
    FrameSetup activation before result [final] owned := by
  have ext := storeLocal_extends_allocations _ _ _ _ _ h
  have above := setup.above slot (by simp)
  refine ⟨⟨setup.fresh.1.trans ext, fun id member =>
    ⟨(setup.fresh.2 id member).1, Nat.lt_of_lt_of_le (setup.fresh.2 id member).2 ext.next⟩⟩,
    setup.allocations.preserve ext (fun id member => (setup.fresh.2 id member).2),
    setup.below.trans (storeLocal_memory_below above h),
    (storeLocal_staticBindings h).trans setup.registry,
    fun hm => storeLocal_preserves_wellFormed _ _ _ _ _ (setup.wellFormed hm) h, ?_, ?_⟩
  · intro hm slot member
    obtain rfl := List.mem_singleton.mp member
    exact storeLocal_preserves_reference_validity _ _ _ _ _ (setup.wellFormed hm)
      (setup.references hm _ (by simp)) h
  · intro slot member
    obtain rfl := List.mem_singleton.mp member
    exact storeLocal_above above h

theorem FrameSetup.root (activation : Nat) (m : Memory) (r : Option ManagedReference)
    (valid : (LocalSlot.root r).ReferencesValid m) : FrameSetup activation m m [.root r] [] :=
  ⟨⟨.refl _, by simp⟩, by simp [FrameAllocations], .refl _ _, rfl, id,
    fun _ slot member => by obtain rfl := List.mem_singleton.mp member; exact valid,
    fun slot member => by obtain rfl := List.mem_singleton.mp member; trivial⟩

theorem makeLocal_setup (m result : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (initial : CIL.Value) (slot : LocalSlot) (owned : List AllocationId)
    (h : makeLocal activation kind initial m = .ok (slot, owned, result)) :
    FrameSetup activation m result [slot] owned := by
  unfold makeLocal at h
  split at h
  · split at h
    · cases h; exact .root _ _ _ True.intro
    · cases h; exact .root _ _ _ True.intro
    · cases h
  all_goals
    cases ha : allocateHome m activation (localWidth kind) (localAlignment kind) <;>
      simp only [ha, Bind.bind, Except.bind] at h
    · cases h
    · rename_i home
      obtain ⟨reference, memory⟩ := home
      have setup := allocateHome_setup _ _ _ _ _ kind ha
      split at h
      · simp only [Pure.pure, Except.pure] at h
        cases h; exact setup
      · cases hs : storeLocal memory (.bytes kind reference) (.scalar initial) <;>
          simp only [hs, Pure.pure, Except.pure] at h
        · cases h
        · cases h; exact setup.store hs

theorem makeLocals_setup (m result : Memory) (activation : Nat) (kinds : List CIL.LocalKind)
    (initializers : List CIL.Value) (slots : List LocalSlot) (owned : List AllocationId)
    (h : makeLocals activation kinds initializers m = .ok (slots, owned, result)) :
    FrameSetup activation m result slots owned := by
  induction kinds generalizing initializers m slots owned result with
  | nil =>
    cases initializers
    · cases h; exact .empty _ _
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
          exact (makeLocal_setup _ _ _ _ _ _ _ hl).append (ih memory final initials rest other hr)

theorem makeArgumentHomes_setup (m result : Memory) (activation : Nat) (indices : List Nat)
    (args : List Value) (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    FrameSetup activation m result (homes.map Prod.snd) owned := by
  induction indices generalizing m homes owned result with
  | nil => cases h; exact .empty _ _
  | cons index indices ih =>
    simp only [makeArgumentHomes] at h
    split at h
    · rename_i bits hv
      cases ha : allocateHome m activation (localWidth .vector256) <;>
        simp only [ha, Bind.bind, Except.bind] at h
      · cases h
      · rename_i home
        obtain ⟨reference, memory⟩ := home
        cases hs : storeLocal memory (.bytes .vector256 reference) (.scalar (.v256 bits)) <;>
          simp only [hs] at h
        · cases h
        · rename_i stored
          obtain ⟨slot, memory'⟩ := stored
          have first := (allocateHome_setup _ _ _ _ _ .vector256 ha).store hs
          cases hr : makeArgumentHomes activation indices args memory' <;>
            simp only [hr, Pure.pure, Except.pure] at h
          · cases h
          · rename_i rest
            obtain ⟨rest, other, final⟩ := rest
            cases h
            exact first.append (ih memory' final rest other hr)
    · cases h

theorem makeParameterHomes_setup (m result : Memory) (activation : Nat)
    (parameters : List (Nat × CIL.LocalKind)) (args : List Value)
    (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeParameterHomes activation parameters args m = .ok (homes, owned, result)) :
    FrameSetup activation m result (homes.map Prod.snd) owned := by
  induction parameters generalizing m homes owned result with
  | nil => cases h; exact .empty _ _
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
          have first := (makeLocal_setup _ _ _ _ _ _ _ hl).store hs
          cases hr : makeParameterHomes activation parameters args memory' <;>
            simp only [hr, Pure.pure, Except.pure] at h
          · cases h
          · rename_i remaining
            obtain ⟨rest, other, final⟩ := remaining
            cases h
            exact first.append (ih memory' final rest other hr)
    · cases h

theorem FrameSetup.select {activation : Nat} {before after : Memory}
    {slots selected : List LocalSlot} {owned : List AllocationId}
    (setup : FrameSetup activation before after slots owned)
    (subset : ∀ slot ∈ selected, slot ∈ slots) : FrameSetup activation before after selected owned :=
  { setup with
    references := fun hm slot member => setup.references hm slot (subset slot member)
    above := fun slot member => setup.above slot (subset slot member) }

theorem enterFrame_setup (body : CIL.Method) (args : List Value) (m result : Memory) (frame : Frame)
    (h : enterFrame body args m = .ok (frame, result)) :
    FrameSetup frame.activation m result (frame.locals ++ frame.arguments.map Prod.snd) frame.owned := by
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
      obtain ⟨arguments, other, final⟩ := homes
      cases hp : makeParameterHomes m.nextIdentity body.parameterHomes args final <;>
        simp only [hp] at h
      · cases h
      · rename_i parameters
        obtain ⟨parameters, ids, final'⟩ := parameters
        cases h
        apply ((makeLocals_setup _ _ _ _ _ _ _ hl).append
          (makeArgumentHomes_setup _ _ _ _ _ _ _ ha) |>.append
          (makeParameterHomes_setup _ _ _ _ _ _ _ hp)).select
        intro slot member
        simp only [List.mem_append] at member ⊢
        rcases member with (left | right) | middle
        · exact Or.inl (Or.inl left)
        · exact Or.inr right
        · exact Or.inl (Or.inr middle)

#print axioms makeLocal_setup
#print axioms makeLocals_setup
#print axioms makeArgumentHomes_setup
#print axioms makeParameterHomes_setup
#print axioms enterFrame_setup

end CIL.Safety
