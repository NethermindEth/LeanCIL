import CIL.Safety.MethodContract
import CIL.Safety.WordSnapshots

/-!
# Word snapshots across confined calls

Carries remembered 64-bit local values (`WordSnapshots`) across a call whose writes are
`Confined` to a footprint that misses every remembered slot.
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
end CIL.Safety
