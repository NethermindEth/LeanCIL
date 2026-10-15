import CIL.Safety.MemoryLemmas
import CIL.Types
import CIL.Safety.MemoryBelow
import CIL.Safety.MemoryEquivalence

namespace CIL.Safety

/-- A value copy checks authority and lifetime but does not inspect initialization. -/
def readSnapshot (m : Memory) (r : Reference) (width alignment : Nat) :
    Checked (List (BitVec 8 × Bool)) := do
  access m r width alignment false
  return (List.range width).map fun i =>
    let cell := m.cells r.allocation (r.offset + i)
    (cell.bits, cell.initialized)

theorem readSnapshot_length {m : Memory} {r : Reference} {width alignment : Nat}
    {bytes : List (BitVec 8 × Bool)} (h : readSnapshot m r width alignment = .ok bytes) :
    bytes.length = width := by
  unfold readSnapshot at h
  cases ha : access m r width alignment false <;>
    simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    simp

/-- Copy bits and initialization flags together. Uninitialized input never becomes
    initialized just because it was assigned to another value or local. -/
def writeSnapshot (m : Memory) (r : Reference) (bytes : List (BitVec 8 × Bool))
    (alignment : Nat) : Checked Memory := do
  let written ← write m r (bytes.map Prod.fst) alignment
  return { written with cells := (fun id offset =>
    if id = r.allocation ∧ r.offset ≤ offset then
      match bytes[offset - r.offset]? with
      | some cell => ⟨cell.1, cell.2⟩
      | none => m.cells id offset
    else m.cells id offset) }

theorem writeSnapshot_preserves_wellFormed (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8 × Bool)) (alignment : Nat) (hm : m.WellFormed)
    (h : writeSnapshot m r bytes alignment = .ok result) : result.WellFormed := by
  unfold writeSnapshot at h
  cases hw : write m r (bytes.map Prod.fst) alignment <;>
    simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    have preserved := write_preserves_wellFormed _ _ _ _ _ hm hw
    exact ⟨preserved.1, preserved.2⟩

theorem writeSnapshot_extends_allocations (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8 × Bool)) (alignment : Nat)
    (h : writeSnapshot m r bytes alignment = .ok result) : AllocationExtension m result := by
  unfold writeSnapshot at h
  cases hw : write m r (bytes.map Prod.fst) alignment <;>
    simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    have preserved := write_extends_allocations _ _ _ _ _ hw
    exact ⟨preserved.next, preserved.lookup⟩

theorem writeSnapshot_preserves_memory_below (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8 × Bool)) (alignment watermark : Nat) (fresh : watermark ≤ r.allocation)
    (h : writeSnapshot m r bytes alignment = .ok result) : MemoryBelow watermark m result := by
  unfold writeSnapshot at h
  cases hw : write m r (bytes.map Prod.fst) alignment <;>
    simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · cases h
    have preserved := write_preserves_memory_below _ _ _ _ _ _ fresh hw
    refine ⟨preserved.allocations, ?_, preserved.permissions⟩
    intro id old offset
    have different : id ≠ r.allocation := by omega
    simp [different]

theorem Memory.Equivalent.readSnapshot {m n : Memory} (same : m.Equivalent n)
    (r : Reference) (width alignment : Nat) :
    readSnapshot m r width alignment = readSnapshot n r width alignment := by
  simp only [CIL.Safety.readSnapshot, same.access, same.cells]

theorem Memory.Equivalent.writeSnapshot {m n : Memory} (same : m.Equivalent n)
    (r : Reference) (bytes : List (BitVec 8 × Bool)) (alignment : Nat) :
    ResultEquivalent Memory.Equivalent (writeSnapshot m r bytes alignment) (writeSnapshot n r bytes alignment) := by
  unfold CIL.Safety.writeSnapshot
  apply ResultEquivalent.bind (same.write r _ alignment)
  intro left right related
  apply ResultEquivalent.ok
  exact ⟨related.allocations, by simp only [same.cells], related.permissions, related.nextIdentity, related.staticBindings⟩

end CIL.Safety
