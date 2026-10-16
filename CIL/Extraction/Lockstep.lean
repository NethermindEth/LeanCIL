namespace CIL.Extraction

/-- Check three per-instruction lists in lockstep. Generated evidence is decided by
    reduction, where indexed lookups at every site make validation quadratic in
    body length; any length mismatch fails. -/
def all3 (check : α → β → γ → Bool) : List α → List β → List γ → Bool
  | a :: as, b :: bs, c :: cs => check a b c && all3 check as bs cs
  | [], [], [] => true
  | _, _, _ => false

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
    exact all3_at valid.2 (by simpa using foundA) (by simpa using foundB) (by simpa using foundC)

#print axioms all3_at

end CIL.Extraction
