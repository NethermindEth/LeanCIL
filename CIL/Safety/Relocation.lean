import CIL.Safety.MemoryLemmas

/-!
# Placements and relocation

References in the checked interpreter are abstract (allocation identity plus offset). A
`Placement` maps identities to physical base addresses; this file defines when a placement
is valid and shows that changing it alters no reference check, read or arithmetic.
`CIL.Safety.RelocationAddress` relates concrete addresses and alignment to placements.
-/

namespace CIL.Safety

/-- Concrete placement is an interpretation of identity, not part of a byref. -/
abbrev Placement := AllocationId → Nat

/-- Every live allocation sits at a nonzero base that is suitably aligned and does not wrap,
    and live allocations do not overlap. -/
def Placement.Valid (p : Placement) (m : Memory) : Prop :=
  (∀ id a, m.allocations id = some a → a.live = true →
    0 < p id ∧ p id + a.layout.size < nativeLimit ∧
      p id % a.layout.alignment = 0) ∧
  (∀ left right a b, left ≠ right → m.allocations left = some a →
    m.allocations right = some b → a.live = true → b.live = true →
    p left + a.layout.size ≤ p right ∨ p right + b.layout.size ≤ p left)

/-- Relocation changes placement while abstract allocation identity, content,
    initialization, authority and lifetime remain unchanged. -/
def LegalRelocation (m : Memory) (before after : Placement) : Prop :=
  before.Valid m ∧ after.Valid m

/-- The 64-bit machine address of a reference under a placement. -/
def concreteAddress (p : Placement) (r : Reference) : BitVec 64 :=
  BitVec.ofNat 64 (p r.allocation + r.offset)

/-- Abstract memory paired with a physical placement of its allocations. -/
structure PlacedMemory where
  memory : Memory
  placement : Placement

/-- Moves every allocation to a new placement, keeping the abstract memory. -/
def relocate (m : PlacedMemory) (placement : Placement) : PlacedMemory :=
  { m with placement }

/-- A checked read; the placement plays no part. -/
def PlacedMemory.read (m : PlacedMemory) (r : Reference) (width alignment : Nat) :=
  Safety.read m.memory r width alignment

/-- The checked reference formation; the placement plays no part. -/
def PlacedMemory.form (m : PlacedMemory) (r : Reference) :=
  Safety.form m.memory r

/-- Checked reference arithmetic; the placement plays no part. -/
def PlacedMemory.add (m : PlacedMemory) (r : Reference) (size : Nat) (offset : BitVec 64) :=
  Safety.add m.memory r size offset

theorem relocation_preserves_reference_validity (m : PlacedMemory) (after : Placement)
    (r : Reference) :
    (relocate m after).form r = m.form r := rfl

theorem relocation_preserves_read (m : PlacedMemory) (after : Placement) (r : Reference)
    (width alignment : Nat) :
    (relocate m after).read r width alignment = m.read r width alignment := rfl

theorem relocation_preserves_reference_arithmetic (m : PlacedMemory) (after : Placement)
    (r : Reference) (size : Nat) (offset : BitVec 64) :
    (relocate m after).add r size offset = m.add r size offset := rfl

/-- Only guaranteed allocation alignment and the offset justify an aligned
    access; this remains true at every legal placement. -/
theorem guaranteed_alignment_at_placement (p : Placement) (m : Memory)
    (hp : p.Valid m) (r : Reference) (a : Allocation)
    (ha : m.allocations r.allocation = some a) (hlive : a.live = true)
    (hoffset : r.offset % a.layout.alignment = 0) :
    (p r.allocation + r.offset) % a.layout.alignment = 0 := by
  have hbase := (hp.1 r.allocation a ha hlive).2.2
  simp [Nat.add_mod, hbase, hoffset]

end CIL.Safety
