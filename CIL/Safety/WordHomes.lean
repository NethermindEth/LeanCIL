import CIL.Safety.WordMemory
import CIL.Safety.HomeProgress
import CIL.Safety.FrameMemoryBelow

/-!
# Word homes

A local recipe `specs` lists, per local, either `some word` (a 64-bit local starting at
`word`) or `none` (an object reference starting null). `WordHomes` says the frame's slots
realize that recipe: each word local has a fresh, initialized, writable eight-byte home,
in strictly increasing allocation order, and each root slot is null.
-/

namespace CIL.Safety

/-- The local kinds of a recipe: `word64` for a word, `reference` for a root. -/
def wordKinds (specs : List (Option (BitVec 64))) : List CIL.LocalKind :=
  specs.map fun spec => match spec with | none => .reference | some _ => .word64

/-- Initialized word homes in strictly increasing allocation identities, with
    null root slots retained at their actual metadata positions. -/
inductive WordHomes (memory : Memory) :
    Nat → List (Option (BitVec 64)) → List LocalSlot → Prop where
  | nil (lower : Nat) : WordHomes memory lower [] []
  | root {lower specs slots} : WordHomes memory lower specs slots →
      WordHomes memory lower (none :: specs) (.root (some .null) :: slots)
  | word {lower specs slots} (reference : Reference) (value : BitVec 64)
      (fresh : lower ≤ reference.allocation)
      (loaded : read memory reference 8 1 = .ok (numberBytes value.toNat 8))
      (writable : access memory reference 8 1 true = .ok ())
      (tail : WordHomes memory (reference.allocation + 1) specs slots) :
      WordHomes memory lower (some value :: specs) (.bytes .word64 reference :: slots)

theorem WordHomes.weaken {memory : Memory} {lower upper : Nat} {specs slots}
    (homes : WordHomes memory upper specs slots) (bound : lower ≤ upper) :
    WordHomes memory lower specs slots := by
  induction homes generalizing lower with
  | nil => exact .nil lower
  | root _ ih => exact .root (ih bound)
  | word reference value fresh loaded writable tail _ =>
    exact .word reference value (Nat.le_trans bound fresh) loaded writable tail

/-- Each word local of the recipe has a home above `lower` holding its initial value. -/
theorem WordHomes.word_at {memory : Memory} {lower : Nat} {specs slots}
    (homes : WordHomes memory lower specs slots) (index : Nat) (value : BitVec 64)
    (specified : specs[index]? = some (some value)) :
    ∃ reference, slots[index]? = some (.bytes .word64 reference) ∧ lower ≤ reference.allocation ∧
      read memory reference 8 1 = .ok (numberBytes value.toNat 8) ∧
      access memory reference 8 1 true = .ok () := by
  induction homes generalizing index value with
  | nil => simp at specified
  | root tail ih =>
    cases index with
    | zero => simp at specified
    | succ index => simpa using ih index value (by simpa using specified)
  | word reference initial fresh loaded writable tail ih =>
    cases index with
    | zero =>
      have same : initial = value := by simpa using specified
      subst value
      exact ⟨reference, rfl, fresh, loaded, writable⟩
    | succ index =>
      obtain ⟨r, found, bound, reading, writing⟩ := ih index value (by simpa using specified)
      exact ⟨r, by simpa using found,
        Nat.le_trans fresh (Nat.le_trans (Nat.le_succ _) bound), reading, writing⟩

theorem WordHomes.word_bound {memory : Memory} {lower : Nat} {specs slots}
    (homes : WordHomes memory lower specs slots) (index : Nat) (reference : Reference)
    (found : slots[index]? = some (.bytes .word64 reference)) : lower ≤ reference.allocation := by
  induction homes generalizing index with
  | nil => simp at found
  | root tail ih =>
    cases index with
    | zero => simp at found
    | succ index => exact ih index (by simpa using found)
  | word r value fresh loaded writable tail ih =>
    cases index with
    | zero =>
      have same : r = reference := by simpa using found
      simpa only [same] using fresh
    | succ index =>
      exact Nat.le_trans fresh (Nat.le_trans (Nat.le_succ _) (ih index (by simpa using found)))

/-- Earlier word homes have strictly smaller allocation identities, so they are distinct. -/
theorem WordHomes.ordered {memory : Memory} {lower : Nat} {specs slots}
    (homes : WordHomes memory lower specs slots) (i j : Nat) (left right : Reference)
    (order : i < j) (first : slots[i]? = some (.bytes .word64 left))
    (second : slots[j]? = some (.bytes .word64 right)) : left.allocation < right.allocation := by
  induction homes generalizing i j with
  | nil => simp at first
  | root tail ih =>
    cases i with
    | zero => simp at first
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih i j (by omega) (by simpa using first) (by simpa using second)
  | word r value fresh loaded writable tail ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        have same : r = left := by simpa using first
        have bound := tail.word_bound j right (by simpa using second)
        rw [same] at bound
        exact bound
      | succ i => exact ih i j (by omega) (by simpa using first) (by simpa using second)

#print axioms WordHomes.weaken
#print axioms WordHomes.word_at
#print axioms WordHomes.word_bound
#print axioms WordHomes.ordered

end CIL.Safety
