/-!
# Lockstep list checks

Extraction evidence is mostly per instruction: the raw CIL body, a reachability mask, a
certificate and the emitted code are parallel lists indexed by pc. `all3` checks such
lists together in one pass, and `all3_at` recovers the check at any single pc.
-/

namespace CIL.Extraction

/-- Check three per-instruction lists in lockstep. Generated evidence is decided by
    reduction, where indexed lookups at every site make validation quadratic in
    body length; any length mismatch fails. -/
def all3 (check : α → β → γ → Bool) : List α → List β → List γ → Bool
  | a :: as, b :: bs, c :: cs => check a b c && all3 check as bs cs
  | [], [], [] => true
  | _, _, _ => false

/-- A passing lockstep check holds at every index present in all three lists. -/
theorem all3_at {check : α → β → γ → Bool} :
    ∀ {as : List α} {bs : List β} {cs : List γ} {k : Nat} {a : α} {b : β} {c : γ},
    all3 check as bs cs = true → as[k]? = some a → bs[k]? = some b → cs[k]? = some c →
    check a b c = true
  | [], _, _, _, _, _, _, _, found, _, _ => by simp at found
  | _ :: _, [], _, _, _, _, _, _, _, found, _ => by simp at found
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, found => by simp at found
  | _ :: _, _ :: _, _ :: _, 0, _, _, _, valid, foundA, foundB, foundC => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at foundA foundB foundC
    subst foundA foundB foundC
    simp only [all3, Bool.and_eq_true] at valid
    exact valid.1
  | _ :: _, _ :: _, _ :: _, _ + 1, _, _, _, valid, foundA, foundB, foundC => by
    simp only [all3, Bool.and_eq_true] at valid
    exact all3_at valid.2 (by simpa using foundA) (by simpa using foundB)
      (by simpa using foundC)

#print axioms all3_at

/-- Mapping the middle list changes nothing when the two checks agree on each of its entries. -/
theorem all3_map {check : α → β → γ → Bool} {mapped : α → δ → γ → Bool} (f : β → δ) :
    ∀ (as : List α) (bs : List β) (cs : List γ),
      (∀ a b c, b ∈ bs → check a b c = mapped a (f b) c) →
      all3 check as bs cs = all3 mapped as (bs.map f) cs
  | a :: as, b :: bs, c :: cs, agree => by
    simp only [all3, List.map_cons]
    rw [agree a b c (List.mem_cons_self ..),
      all3_map f as bs cs fun a b c member => agree a b c (List.mem_cons_of_mem _ member)]
  | [], [], [], _ => rfl
  | [], _ :: _, _, _ | _ :: _, [], _, _ | [], [], _ :: _, _ => rfl
  | _ :: _, _ :: _, [], _ => rfl

#print axioms all3_map

/-- A passing lockstep check holds for every entry of the middle list. -/
theorem all3_mem {check : α → β → γ → Bool} :
    ∀ {as : List α} {bs : List β} {cs : List γ} {b : β},
      all3 check as bs cs = true → b ∈ bs → ∃ a c, check a b c = true
  | a :: as, b :: bs, c :: cs, entry, valid, member => by
    simp only [all3, Bool.and_eq_true] at valid
    rcases List.mem_cons.mp member with same | later
    · subst same
      exact ⟨a, c, valid.1⟩
    · exact all3_mem valid.2 later
  | [], [], [], _, _, member => by simp at member
  | [], _ :: _, _, _, valid, _ | _ :: _, [], _, _, valid, _ | [], [], _ :: _, _, valid, _ => by
    simp [all3] at valid
  | _ :: _, _ :: _, [], _, valid, _ => by simp [all3] at valid

#print axioms all3_mem

end CIL.Extraction
