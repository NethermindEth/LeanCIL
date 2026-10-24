import CIL.Safety.MethodContract
import CIL.Safety.WordSnapshots
import CIL.Safety.LocalSnapshots

/-!
# Snapshots across confined calls

Carries remembered local values (`WordSnapshots` and `LocalSnapshots`) across a call whose
writes are `Confined` to a footprint that misses every remembered slot.
-/

namespace CIL.Safety

/-- Remembered words apart from every footprint entry survive a confined call. -/
theorem WordSnapshots.after_confined {footprint : List (Reference × Nat)} {before after : Memory}
    {slots : List LocalSlot} {known : Nat → Option (BitVec 64)}
    (snapshots : WordSnapshots before slots known) (framed : Confined footprint before after)
    (formed : before.WellFormed)
    (apart : ∀ index value reference, known index = some value →
      slots[index]? = some (.bytes .word64 reference) →
      ∀ entry ∈ footprint, Apart reference 8 entry) :
    WordSnapshots after slots known := by
  intro index value present
  obtain ⟨reference, slot, loaded⟩ := snapshots index value present
  exact ⟨reference, slot,
    framed.read_apart formed loaded (apart index value reference present slot)⟩

#print axioms WordSnapshots.after_confined

/-- Remembered locals of any numeric kind apart from every footprint entry survive a
    confined call. -/
theorem LocalSnapshots.after_confined {footprint : List (Reference × Nat)}
    {before after : Memory} {slots : List LocalSlot} {known : Nat → Option CIL.Value}
    (snapshots : LocalSnapshots before slots known) (framed : Confined footprint before after)
    (formed : before.WellFormed)
    (apart : ∀ index value kind home, known index = some value →
      slots[index]? = some (.bytes kind home) →
      ∀ entry ∈ footprint, Apart home (localWidth kind) entry) :
    LocalSnapshots after slots known := by
  intro index value specified
  obtain ⟨kind, home, stored, number, slot, fits, result, loaded⟩ :=
    snapshots index value specified
  exact ⟨kind, home, stored, number, slot, fits, result,
    framed.read_apart formed loaded (apart index value kind home specified slot)⟩

#print axioms LocalSnapshots.after_confined
end CIL.Safety
