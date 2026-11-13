import Std.Data.TreeMap.Lemmas

/-!
# First-entry index

A pc-keyed association list read many times is indexed once: lookups are logarithmic and the first
entry for a key wins, as in a list scan. The extraction checks use it for static sites and the
embedding diagnostic for link tables. Its lemma depends on a classical axiom through the tree
library, so statements that proofs unfold downstream avoid it where they can.
-/

namespace CIL

/-- The entries as a tree; the first entry of the list for a key wins. -/
def firstEntryIndex {α : Type} : List (Nat × α) → Std.TreeMap Nat α
  | [] => ∅
  | (key, value) :: rest => (firstEntryIndex rest).insert key value

/-- The index answers each key with the first entry of the list for it. -/
theorem firstEntryIndex_get {α : Type} (entries : List (Nat × α)) (key : Nat) :
    (firstEntryIndex entries)[key]? =
      (entries.find? fun entry => entry.1 == key).map Prod.snd := by
  induction entries with
  | nil => simp [firstEntryIndex]
  | cons entry entries ih =>
    rcases entry with ⟨index, value⟩
    simp only [firstEntryIndex, Std.TreeMap.getElem?_insert, List.find?_cons]
    by_cases same : index = key
    · subst index; simp
    · have different : (index == key) = false := beq_eq_false_iff_ne.mpr same
      simp [same, ih, different]

#print axioms firstEntryIndex_get

end CIL
