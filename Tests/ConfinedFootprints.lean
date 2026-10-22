import CIL.Safety.MethodContract

/-! Footprint reasoning for `Confined` contracts, checked without an extraction. -/
namespace Tests.ConfinedFootprints

open CIL.Safety

/-- Per-word facts close a word footprint of any arity in one `simp` call. -/
theorem outside_three_words {r q s : Reference} {id offset : Nat} (hr : OutsideWord r id offset)
    (hq : OutsideWord q id offset) (hs : OutsideWord s id offset) :
    Outside [(r, 8), (q, 8), (s, 8)] id offset := by
  simpa using ⟨hr, hq, hs⟩

theorem outside_three_words_term {r q s : Reference} {id offset : Nat} (hr : OutsideWord r id offset)
    (hq : OutsideWord q id offset) (hs : OutsideWord s id offset) :
    Outside [(r, 8), (q, 8), (s, 8)] id offset :=
  Outside.word hr (Outside.word hq (Outside.word hs (Outside.nil _ _)))

/-- A byte of any listed word is inside the footprint, wherever the other words lie. -/
theorem inside_listed_word (r q : Reference) (i : Nat) (bound : i < 8) :
    ¬ Outside [(q, 8), (r, 8)] r.allocation (r.offset + i) := by
  simp only [Outside.cons, Outside.nil, and_true]
  omega

#print axioms outside_three_words
#print axioms outside_three_words_term
#print axioms inside_listed_word

end Tests.ConfinedFootprints
