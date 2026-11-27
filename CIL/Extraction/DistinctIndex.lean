import CIL.TypeExpr

/-!
# Exact membership in dispatch catalogs

Checked catalogs index selected identities by ordered keys. A key may describe more than one
identity, so duplicate detection and membership compare the complete values in its bucket.
-/

namespace CIL.Extraction

/-- The members of a list, grouped by key, if all members are distinct. -/
def distinctIndex? {α κ : Type} [DecidableEq α] [Ord κ] (key : α → κ) :
    List α → Option (Std.TreeMap κ (List α))
  | [] => some ∅
  | member :: rest => do
    let index ← distinctIndex? key rest
    let bucket := index.getD (key member) []
    if bucket.contains member then none
    else some (index.insert (key member) (member :: bucket))

/-- A successful distinct index contains exactly the input list in the ordinary key buckets. -/
theorem distinctIndex?_eq {α κ : Type} [DecidableEq α] [Ord κ] [Std.TransOrd κ]
    [Std.LawfulEqOrd κ] [BEq κ] [LawfulBEq κ] (key : α → κ) (members : List α) :
    distinctIndex? key members =
      (if members.Nodup then some (groupIndex key members) else none) := by
  induction members with
  | nil => rfl
  | cons member rest ih =>
    by_cases prior : rest.Nodup
    · have bucket : member ∈ (groupIndex key rest).getD (key member) [] ↔ member ∈ rest := by
        rw [groupIndex_get]
        simp
      simp [distinctIndex?, ih, prior, bucket, groupIndex, List.nodup_cons]
    · simp [distinctIndex?, ih, prior]

#print axioms distinctIndex?_eq

/-- An exact membership test for a list with no repeated values. -/
def distinctMembership? {α κ : Type} [DecidableEq α] [Ord κ] (key : α → κ) :
    List α → Option (α → Bool)
  | [] => some fun _ => false
  | [value] => some fun member => member == value
  | members => (distinctIndex? key members).map fun index member =>
      (index.getD (key member) []).contains member

/-- Indexed membership agrees with a full-list check for every query and rejects every repeat. -/
theorem distinctMembership?_eq {α κ : Type} [DecidableEq α] [Ord κ] [Std.TransOrd κ]
    [Std.LawfulEqOrd κ] [BEq κ] [LawfulBEq κ] (key : α → κ) (members : List α) :
    distinctMembership? key members = (if members.Nodup then some members.contains else none) := by
  match members with
  | [] => rfl
  | [value] =>
    simp [distinctMembership?]
    funext member
    by_cases same : member = value <;> simp [same]
  | first :: second :: rest =>
    let members := first :: second :: rest
    change (distinctIndex? key members).map _ = _
    rw [distinctIndex?_eq]
    by_cases clean : members.Nodup
    · change _ = (if members.Nodup then _ else _)
      simp only [clean, ↓reduceIte, Option.map_some, Option.some.injEq]
      funext query
      rw [groupIndex_get]
      simp [members]
    · change _ = (if members.Nodup then _ else _)
      simp [clean]

#print axioms distinctMembership?_eq

end CIL.Extraction
