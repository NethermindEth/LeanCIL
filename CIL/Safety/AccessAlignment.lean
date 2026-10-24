import CIL.Safety.AccessSlices
import CIL.Safety.Relocation

/-!
# What a successful access guarantees

Each successful checked access, value load or value store in the checked interpreter
(`CIL/Safety/Execution.lean`) is traced back to the `AccessRequirements` it passed. The
alignment result holds at every valid `Placement`, so it does not depend on where the
allocator happened to put an allocation.
-/

namespace CIL.Safety

/-- A successful access establishes the requested alignment at every legal
    placement, even when it is weaker than the allocation's alignment. This
    uses guaranteed layout alignment, never incidental physical placement. -/
theorem access_alignment_at_placement {m : Memory} {r : Reference}
    {width alignment : Nat} {writing : Bool} (p : Placement) (placed : p.Valid m)
    (checked : access m r width alignment writing = .ok ()) :
    0 < alignment ∧ (p r.allocation + r.offset) % alignment = 0 := by
  obtain ⟨allocation, ready⟩ := access_requirements checked
  have base := (placed.1 r.allocation allocation ready.present ready.live).2.2
  have divides : alignment ∣ p r.allocation :=
    Nat.dvd_trans (Nat.dvd_of_mod_eq_zero ready.aligned.2.1)
      (Nat.dvd_of_mod_eq_zero base)
  exact ⟨ready.aligned.1, Nat.mod_eq_zero_of_dvd
    (Nat.dvd_add divides (Nat.dvd_of_mod_eq_zero ready.aligned.2.2))⟩

/-- Copying a vector may retain unknown bytes, but never bypasses the checked
    read authority, lifetime, bounds or alignment requirements. -/
theorem loadValue_checked_read {m : Memory} {reference : ManagedReference}
    {width : Nat} {value : CIL.Value} {signed : Bool}
    (loaded : loadValue m reference width signed = .ok value) :
    ∃ r, reference = .address r ∧ access m r width 1 false = .ok () := by
  cases reference with
  | null =>
    simp [loadValue, dereference, checkedAt, Except.mapError,
      Bind.bind, Except.bind] at loaded
  | address r =>
    cases ha : access m r width 1 false with
    | error fault =>
      by_cases h16 : width = 16 <;> by_cases h32 : width = 32 <;> by_cases h64 : width = 64 <;>
        simp_all [loadValue, dereference, read, checkedAt, loadSnapshot, referenceAt,
          ordinaryAccessAlignment, CIL.SnapshotShape.width, readSnapshot, Except.mapError,
          Bind.bind, Except.bind]
      all_goals repeat' first | cases loaded | split at loaded
    | ok result => cases result; exact ⟨r, rfl, ha⟩

/-- Byte alignment at the supported ordinary value-load boundary imposes no
    hidden natural/vector alignment on a caller offset. Other read obligations
    still come from the actual checked access. This is a model theorem, not a
    theorem about CLR lowering; see ALIGNMENT.md for that correspondence audit. -/
theorem loadValue_access_requirements {m : Memory} {reference : ManagedReference}
    {width : Nat} {value : CIL.Value} {signed : Bool}
    (loaded : loadValue m reference width signed = .ok value) :
    ∃ r allocation, reference = .address r ∧
      AccessRequirements m r width 1 false allocation := by
  obtain ⟨r, href, checked⟩ := loadValue_checked_read loaded
  obtain ⟨allocation, ready⟩ := access_requirements checked
  exact ⟨r, allocation, href, ready⟩

private theorem checkedAt_success {reference : ManagedReference} {width : Nat}
    {result : Checked α} {value : α} (checked : checkedAt reference width result = .ok value) :
    result = .ok value := by
  cases result <;> simp_all [checkedAt, Except.mapError]

/-- Stores copy either initialized bytes or exact byte/mask snapshots. -/
theorem storeValue_checked_write {m final : Memory} {reference : ManagedReference}
    {value : CIL.Value} (stored : storeValue m reference value = .ok final) :
    ∃ r, reference = .address r ∧
      ((∃ bytes, write m r bytes 1 = .ok final) ∨
       (∃ bytes, writeSnapshot m r bytes 1 = .ok final)) := by
  cases value <;> cases reference <;>
    simp only [storeValue, referenceAt, Bind.bind, Except.bind] at stored <;>
    try cases stored
  all_goals repeat' first
    | solve | exact ⟨_, rfl, Or.inl ⟨_, checkedAt_success stored⟩⟩
    | solve | exact ⟨_, rfl, Or.inr ⟨_, checkedAt_success stored⟩⟩
    | cases stored
    | split at stored

/-- A successful value store passed the write `AccessRequirements` for some width. -/
theorem storeValue_access_requirements {m final : Memory} {reference : ManagedReference}
    {value : CIL.Value} (stored : storeValue m reference value = .ok final) :
    ∃ r width allocation, reference = .address r ∧
      AccessRequirements m r width 1 true allocation := by
  obtain ⟨r, href, ordinary | snapshot⟩ := storeValue_checked_write stored
  · obtain ⟨bytes, hwritten⟩ := ordinary
    have checked : access m r bytes.length 1 true = .ok () := by
      unfold write at hwritten
      cases ha : access m r bytes.length 1 true <;> simp_all [Bind.bind, Except.bind]
    obtain ⟨allocation, ready⟩ := access_requirements checked
    exact ⟨r, bytes.length, allocation, href, ready⟩
  · obtain ⟨bytes, hwritten⟩ := snapshot
    have checked : access m r bytes.length 1 true = .ok () := by
      unfold writeSnapshot write at hwritten
      simp only [List.length_map] at hwritten
      cases ha : access m r bytes.length 1 true <;> simp_all [Bind.bind, Except.bind]
    obtain ⟨allocation, ready⟩ := access_requirements checked
    exact ⟨r, bytes.length, allocation, href, ready⟩
#print axioms access_alignment_at_placement
#print axioms loadValue_checked_read
#print axioms loadValue_access_requirements
#print axioms storeValue_checked_write
#print axioms storeValue_access_requirements

end CIL.Safety
