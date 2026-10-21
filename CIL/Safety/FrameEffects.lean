import CIL.Safety.FrameLemmas
import CIL.Safety.MemoryBelow

namespace CIL.Safety

theorem allocateHome_fresh {alignment : Nat} (m result : Memory) (activation width : Nat) (r : Reference)
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

def FrameAllocations (m : Memory) (activation : Nat) (owned : List AllocationId) : Prop :=
  ∀ id ∈ owned, ∃ a, m.allocations id = some a ∧ a.kind = .frame activation ∧ a.live = true

theorem FrameAllocations.preserve {before after : Memory} {activation : Nat} {owned : List AllocationId}
    (ext : AllocationExtension before after) (bounds : ∀ id ∈ owned, id < before.nextIdentity)
    (owns : FrameAllocations before activation owned) : FrameAllocations after activation owned := by
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

theorem allocateHome_owned {alignment : Nat} (m result : Memory) (activation width : Nat) (r : Reference)
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

/-- A root must contain a checked reference; byte slots must name live storage. -/
def LocalSlot.ReferencesValid (m : Memory) : LocalSlot → Prop
  | .root none | .root (some .null) => True
  | .root (some (.address r)) | .bytes _ r => form m r = .ok r

def SlotsReferencesValid (m : Memory) (slots : List LocalSlot) : Prop :=
  ∀ slot ∈ slots, slot.ReferencesValid m
theorem LocalSlot.ReferencesValid.preserve {m result : Memory} {slot : LocalSlot}
    (valid : slot.ReferencesValid m) (hm : m.WellFormed) (ext : AllocationExtension m result) :
    slot.ReferencesValid result := by
  cases slot with
  | bytes kind r => exact ext.preserves_reference hm r r valid
  | root value =>
    cases value with
    | none => exact True.intro
    | some r =>
      cases r with
      | null => exact True.intro
      | address r => exact ext.preserves_reference hm r r valid

theorem allocateHome_reference_valid {alignment : Nat} (m result : Memory) (activation width : Nat) (r : Reference)
    (h : allocateHome m activation width alignment = .ok (r, result)) : form result r = .ok r := by
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

end CIL.Safety
