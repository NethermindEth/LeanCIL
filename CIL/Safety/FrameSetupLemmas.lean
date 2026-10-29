import CIL.Safety.FrameLemmas
import CIL.Safety.MemoryBelow
import CIL.Safety.SpanViewLemmas
import CIL.Safety.ArrayViewLemmas

/-!
# Frame setup effects

What `enterFrame` (in `CIL/Safety/Frames.lean`) does to memory, collected in one
`FrameSetup` record: the frame owns only fresh allocations of its own activation, caller
memory below the entry watermark is untouched, the static registry is unchanged, and every
slot refers to live storage. Each builder (`makeLocal`, `makeArgumentHomes`, ...) proves a
`FrameSetup`, and `FrameSetup.append` composes them; the other `Frame*` files project it.
-/

namespace CIL.Safety

theorem allocateHome_fresh {alignment : Nat} (m result : Memory) (activation width : Nat)
    (r : Reference)
    (h : allocateHome m activation width alignment = .ok (r, result)) :
    AllocationExtension m result ∧ r.allocation = m.nextIdentity ∧
      r.allocation < result.nextIdentity := by
  unfold allocateHome at h
  cases ha : allocate m ⟨.frame activation, ⟨width, alignment, []⟩, true, [width]⟩ <;>
    simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at h
  · cases h
  · rename_i home
    obtain ⟨id, memory⟩ := home
    cases h
    have ext := allocate_extends_allocations _ _ _ _ ha
    have ids := allocation_identity_fresh _ _ _ _ ha
    exact ⟨⟨ext.next, ext.lookup⟩, ids.1, by rw [ids.1, ids.2]; exact Nat.lt_succ_self _⟩

theorem storeLocal_extends_allocations (m result : Memory) (slot final : LocalSlot)
    (value : Value) (h : storeLocal m slot value = .ok (final, result)) :
    AllocationExtension m result := by
  unfold storeLocal at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals repeat' first
    | exact .refl m
    | solve | exact write_extends_allocations _ _ _ _ _ (checkedAt_ok (by assumption))
    | solve | exact writeSnapshot_extends_allocations _ _ _ _ _ (checkedAt_ok (by assumption))
    | cases h
    | split at h

/-- `after` extends `before`, and every id in `owned` was allocated between them. -/
def FreshOwned (before after : Memory) (owned : List AllocationId) : Prop :=
  AllocationExtension before after ∧
    ∀ id ∈ owned, before.nextIdentity ≤ id ∧ id < after.nextIdentity

theorem FreshOwned.trans {first middle last : Memory} {left right : List AllocationId}
    (hl : FreshOwned first middle left) (hr : FreshOwned middle last right) :
    FreshOwned first last (left ++ right) := by
  refine ⟨hl.1.trans hr.1, ?_⟩
  intro id member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨lo, hi⟩ := hl.2 id member
    exact ⟨lo, Nat.lt_of_lt_of_le hi hr.1.next⟩
  · obtain ⟨lo, hi⟩ := hr.2 id member
    exact ⟨Nat.le_trans hl.1.next lo, hi⟩

/-- Every id in `owned` is a live allocation belonging to frame `activation`. -/
def FrameAllocations (m : Memory) (activation : Nat) (owned : List AllocationId) : Prop :=
  ∀ id ∈ owned, ∃ a, m.allocations id = some a ∧ a.kind = .frame activation ∧ a.live = true

theorem FrameAllocations.preserve {before after : Memory} {activation : Nat}
    {owned : List AllocationId}
    (ext : AllocationExtension before after) (bounds : ∀ id ∈ owned, id < before.nextIdentity)
    (owns : FrameAllocations before activation owned) :
    FrameAllocations after activation owned := by
  intro id member
  obtain ⟨a, present, kind, live⟩ := owns id member
  exact ⟨a, (ext.lookup id (bounds id member)).trans present, kind, live⟩

theorem FrameAllocations.append {m : Memory} {activation : Nat} {left right : List AllocationId}
    (hl : FrameAllocations m activation left) (hr : FrameAllocations m activation right) :
    FrameAllocations m activation (left ++ right) := by
  intro id member
  rcases List.mem_append.mp member with member | member
  · exact hl id member
  · exact hr id member

theorem allocateHome_owned {alignment : Nat} (m result : Memory) (activation width : Nat)
    (r : Reference)
    (h : allocateHome m activation width alignment = .ok (r, result)) :
    FrameAllocations result activation [r.allocation] := by
  unfold allocateHome at h
  cases ha : allocate m ⟨.frame activation, ⟨width, alignment, []⟩, true, [width]⟩ <;>
    simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at h
  · cases h
  · rename_i home
    obtain ⟨id, memory⟩ := home
    cases h
    intro other member
    simp only [List.mem_singleton] at member
    subst other
    have lookup := allocation_lookup m _ id memory ha
    exact ⟨_, lookup, rfl, rfl⟩

theorem allocateHome_preserves_caller_memory {alignment : Nat} (m result : Memory)
    (activation width : Nat) (r : Reference)
    (h : allocateHome m activation width alignment = .ok (r, result)) :
    MemoryBelow m.nextIdentity m result := by
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

/-- Roots and spans retain checked references and extents; byte slots name live storage. -/
def LocalSlot.ReferencesValid (m : Memory) : LocalSlot → Prop
  | .methodPointer .. | .methodTable .. => True
  | .root none | .root (some .null) | .readOnlyRoot .null | .opaque128 _ => True
  | .root (some (.address r)) | .readOnlyRoot (.address r) | .bytes _ r => form m r = .ok r
  | .span _ _ none => True
  | .span _ _ (some view) => view.validate m = .ok ()
  | .array _ none => True
  | .array _ (some view) => view.validate m = .ok ()

/-- Every slot in `slots` satisfies `LocalSlot.ReferencesValid`. -/
def SlotsReferencesValid (m : Memory) (slots : List LocalSlot) : Prop :=
  ∀ slot ∈ slots, slot.ReferencesValid m

theorem LocalSlot.ReferencesValid.preserve {m result : Memory} {slot : LocalSlot}
    (valid : slot.ReferencesValid m) (hm : m.WellFormed) (ext : AllocationExtension m result) :
    slot.ReferencesValid result := by
  cases slot with
  | bytes kind r => exact ext.preserves_reference hm r r valid
  | opaque128 _ | methodPointer _ _ | methodTable _ _ => trivial
  | readOnlyRoot reference =>
    cases reference with
    | null => trivial
    | address reference => exact ext.preserves_reference hm reference reference valid
  | span width writable value =>
    cases value with
    | none => trivial
    | some view => exact view.validate_preserved valid hm ext
  | array element value =>
    cases value with
    | none => trivial
    | some view => exact view.validate_preserved valid hm ext
  | root value =>
    cases value with
    | none => exact True.intro
    | some r =>
      cases r with
      | null => exact True.intro
      | address r => exact ext.preserves_reference hm r r valid

theorem allocateHome_reference_valid {alignment : Nat} (m result : Memory)
    (activation width : Nat) (r : Reference)
    (h : allocateHome m activation width alignment = .ok (r, result)) :
    form result r = .ok r := by
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
    simp [form, liveAllocation, lookup, validPosition, nativeLimit, position,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Byte homes are allocated after the entry watermark; roots do not own bytes. -/
def LocalSlot.Above (watermark : Nat) : LocalSlot → Prop
  | .root _ | .readOnlyRoot _ | .opaque128 _ | .span .. | .array ..
  | .methodPointer .. | .methodTable .. => True
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
    (h : writeSnapshot m r bytes alignment = .ok result) :
    result.staticBindings = m.staticBindings := by
  unfold writeSnapshot at h
  cases hw : write m r (bytes.map Prod.fst) alignment <;>
    simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    have registry := write_staticBindings hw
    exact registry

theorem storeLocal_staticBindings {m result : Memory} {slot final : LocalSlot} {value : Value}
    (h : storeLocal m slot value = .ok (final, result)) :
    result.staticBindings = m.staticBindings := by
  unfold storeLocal at h
  repeat' first
    | rfl
    | solve | exact write_staticBindings (checkedAt_ok (by assumption))
    | solve | exact writeSnapshot_staticBindings (checkedAt_ok (by assumption))
    | cases h
    | split at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h

theorem storeLocal_above {m result : Memory} {slot final : LocalSlot} {value : Value}
    {watermark : Nat}
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
    | contradiction
    | exact .refl _ _
    | solve | exact write_preserves_memory_below _ _ _ _ _ _ above (checkedAt_ok (by assumption))
    | solve | exact writeSnapshot_preserves_memory_below _ _ _ _ _ _ above
                  (checkedAt_ok (by assumption))
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

/-- A restricted root retains the same live reference validated at storage. -/
theorem formValue_readOnlyRoot_valid {m : Memory} {r : ManagedReference} {value : Value}
    (formed : formValue m r = .ok value) : (LocalSlot.readOnlyRoot r).ReferencesValid m := by
  cases r <;> exact formValue_root_valid formed

#print axioms formValue_readOnlyRoot_valid

theorem storeLocal_preserves_reference_validity (m result : Memory) (slot final : LocalSlot)
    (value : Value) (hm : m.WellFormed) (valid : slot.ReferencesValid m)
    (h : storeLocal m slot value = .ok (final, result)) : final.ReferencesValid result := by
  have retained := valid.preserve hm (storeLocal_extends_allocations _ _ _ _ _ h)
  unfold storeLocal at h
  repeat' first
    | exact retained
    | solve | exact ArrayView.null_valid _ _
    | solve | exact formValue_root_valid (by assumption)
    | solve | exact formValue_readOnlyRoot_valid (by assumption)
    | solve | exact checkedAt_ok (by assumption)
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
    (a.allocations.preserve b.fresh.1 (fun id member => (a.fresh.2 id member).2)).append
      b.allocations,
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
      | readOnlyRoot _ => trivial
      | opaque128 _ | methodPointer _ _ | methodTable _ _ => trivial
      | span _ _ _ => trivial
      | array _ _ => trivial
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
      simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure,
        Except.pure] at h
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
  · split at h <;> first
      | (solve | cases h)
      | (cases h; exact ⟨⟨.refl _, by simp⟩, by simp [FrameAllocations], .refl _ _, rfl, id,
          by simp [SlotsReferencesValid, LocalSlot.ReferencesValid],
          by simp [LocalSlot.Above]⟩)
  · split at h <;> first
      | (solve | cases h)
      | (cases h; exact ⟨⟨.refl _, by simp⟩, by simp [FrameAllocations], .refl _ _, rfl, id,
          by simp [SlotsReferencesValid, LocalSlot.ReferencesValid],
          by simp [LocalSlot.Above]⟩)
  · rename_i element
    split at h
    · cases h
      refine ⟨⟨.refl _, by simp⟩, by simp [FrameAllocations], .refl _ _, rfl, id, ?_, ?_⟩
      · intro _ entry member
        obtain rfl := List.mem_singleton.mp member
        exact ArrayView.null_valid element m
      · intro entry member
        obtain rfl := List.mem_singleton.mp member
        trivial
    · cases h
      exact ⟨⟨.refl _, by simp⟩, by simp [FrameAllocations], .refl _ _, rfl, id,
        by simp [SlotsReferencesValid, LocalSlot.ReferencesValid],
        by simp [LocalSlot.Above]⟩
    · cases h
  · rename_i width writable
    split at h
    · cases h
    · rename_i widthValid
      split at h
      · cases h
        refine ⟨⟨.refl _, by simp⟩, by simp [FrameAllocations], .refl _ _, rfl, id, ?_, ?_⟩
        · intro _ entry member
          obtain rfl := List.mem_singleton.mp member
          simp_all [LocalSlot.ReferencesValid, SpanView.validate, Bind.bind, Except.bind,
            Pure.pure, Except.pure]
        · intro entry member
          obtain rfl := List.mem_singleton.mp member
          trivial
      · cases h
        exact ⟨⟨.refl _, by simp⟩, by simp [FrameAllocations], .refl _ _, rfl, id,
          by simp [SlotsReferencesValid, LocalSlot.ReferencesValid],
          by simp [LocalSlot.Above]⟩
      · cases h
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

theorem FrameSetup.opaque128 (activation : Nat) (m : Memory) (value : Option Opaque128Value) :
    FrameSetup activation m m [.opaque128 value] [] :=
  ⟨⟨.refl _, by simp⟩, by simp [FrameAllocations], .refl _ _, rfl, id,
    fun _ slot member => by obtain rfl := List.mem_singleton.mp member; trivial,
    fun slot member => by obtain rfl := List.mem_singleton.mp member; trivial⟩

theorem makeOpaque128_setup (m result : Memory) (activation : Nat) (initial : CIL.Value)
    (slot : LocalSlot) (owned : List AllocationId)
    (h : makeOpaque128 initial m = .ok (slot, owned, result)) :
    FrameSetup activation m result [slot] owned := by
  cases initial with
  | v128 bits =>
    change Except.ok (LocalSlot.opaque128 (some (.known bits)), [], m) =
      .ok (slot, owned, result) at h
    cases h
    exact FrameSetup.opaque128 activation m _
  | unmodeled =>
    change Except.ok (LocalSlot.opaque128 none, [], m) = .ok (slot, owned, result) at h
    cases h
    exact FrameSetup.opaque128 activation m _
  | _ => cases h

theorem makeSelectedLocalsFrom_setup (m result : Memory) (activation : Nat) (indices : List Nat)
    (index : Nat) (kinds : List CIL.LocalKind) (initializers : List CIL.Value)
    (slots : List LocalSlot) (owned : List AllocationId)
    (h : makeSelectedLocalsFrom activation indices index kinds initializers m =
      .ok (slots, owned, result)) :
    FrameSetup activation m result slots owned := by
  induction kinds generalizing index initializers m slots owned result with
  | nil =>
    cases initializers
    · cases h; exact .empty _ _
    · cases h
  | cons kind kinds ih =>
    cases initializers with
    | nil => cases h
    | cons initial initials =>
      simp only [makeSelectedLocalsFrom] at h
      have finish (first : ExecutionResult (LocalSlot × List AllocationId × Memory))
          (setup : ∀ slot ids memory, first = .ok (slot, ids, memory) →
            FrameSetup activation m memory [slot] ids)
          (bound : (do
            let (slot, ids, memory) ← first
            let (rest, other, final) ←
              makeSelectedLocalsFrom activation indices (index + 1) kinds initials memory
            pure (slot :: rest, ids ++ other, final)) = .ok (slots, owned, result)) :
          FrameSetup activation m result slots owned := by
        cases hl : first <;> simp only [hl, Bind.bind, Except.bind] at bound
        · cases bound
        · rename_i home
          obtain ⟨slot, ids, memory⟩ := home
          cases hr : makeSelectedLocalsFrom activation indices (index + 1) kinds initials memory <;>
            simp only [hr, Pure.pure, Except.pure] at bound
          · cases bound
          · rename_i rest
            obtain ⟨rest, other, final⟩ := rest
            cases bound
            exact (setup slot ids memory hl).append
              (ih memory final (index + 1) initials rest other hr)
      split at h
      · split at h
        · exact finish (makeOpaque128 initial m) (fun slot ids memory bound =>
            makeOpaque128_setup _ _ _ _ _ _ bound) h
        · cases h
      · exact finish (makeLocal activation kind initial m) (fun slot ids memory bound =>
          makeLocal_setup _ _ _ _ _ _ _ bound) h

theorem makeSelectedLocals_setup (m result : Memory) (activation : Nat) (indices : List Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value) (slots : List LocalSlot)
    (owned : List AllocationId)
    (h : makeSelectedLocals activation indices kinds initializers m = .ok (slots, owned, result)) :
    FrameSetup activation m result slots owned := by
  unfold makeSelectedLocals at h
  split at h
  · exact makeLocals_setup _ _ _ _ _ _ _ h
  · exact makeSelectedLocalsFrom_setup _ _ _ _ _ _ _ _ _ h

theorem makeArgumentHomes_setup (m result : Memory) (activation : Nat) (indices : List Nat)
    (args : List Value) (homes : List (Nat × LocalSlot)) (owned : List AllocationId)
    (h : makeArgumentHomes activation indices args m = .ok (homes, owned, result)) :
    FrameSetup activation m result (homes.map Prod.snd) owned := by
  induction indices generalizing m homes owned result with
  | nil => cases h; exact .empty _ _
  | cons index indices ih =>
    simp only [makeArgumentHomes] at h
    have known : (args[index]?.map Value.hasUnspecified).getD false = false := by
      cases hu : (args[index]?.map Value.hasUnspecified).getD false with
      | false => rfl
      | true => simp only [hu, ite_true] at h; cases h
    simp only [known, Bool.false_eq_true, ite_false] at h
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
    (subset : ∀ slot ∈ selected, slot ∈ slots) :
    FrameSetup activation before after selected owned :=
  { setup with
    references := fun hm slot member => setup.references hm slot (subset slot member)
    above := fun slot member => setup.above slot (subset slot member) }

/-- Everything `enterFrame` guarantees about the memory it returns and the frame's slots. -/
theorem enterFrame_setup (body : CIL.Method) (args : List Value) (m result : Memory)
    (frame : Frame) (h : enterFrame body args m = .ok (frame, result)) :
    FrameSetup frame.activation m result (frame.locals ++ frame.arguments.map Prod.snd)
      frame.owned := by
  simp only [enterFrame] at h
  cases hl : makeSelectedLocals m.nextIdentity body.opaqueVectorLocals body.localKinds
      body.locals m <;>
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
        apply ((makeSelectedLocals_setup _ _ _ _ _ _ _ _ hl).append
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
