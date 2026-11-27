import CIL.TypeExpr

/-! A shared, fuel-bounded fold over parent links. -/

namespace CIL.Extraction

/-- One class either ends outside the hierarchy, reaches its root, or extends a parent summary. -/
inductive ParentLink (α σ : Type) where
  | absent
  | root (value : σ)
  | parent (id : α) (extend : σ → σ)

namespace ParentLink

/-- The summary of the first root reached within the fuel limit. -/
def walk (link : α → ParentLink α σ) : Nat → α → Option σ
  | 0, _ => none
  | fuel + 1, id => match link id with
    | .absent => none
    | .root value => some value
    | .parent base extend => (walk link fuel base).map extend

/-- A cached result records how many entries a bounded walk needs to reach the root. -/
private def atFuel (answer : Option (Nat × σ)) (fuel : Nat) : Option σ :=
  answer.bind fun (depth, value) => if depth ≤ fuel then some value else none

/-- Every cached answer agrees with a walk at every fuel limit. -/
private structure Answer (link : α → ParentLink α σ) (id : α) where
  value : Option (Nat × σ)
  correct : ∀ fuel, walk link fuel id = atFuel value fuel

private abbrev Cache (κ : Type) [Ord κ] (link : α → ParentLink α σ) :=
  Std.TreeMap κ (List ((id : α) × Answer link id))

/-- An exact identity lookup refines the ordered cache key. -/
private def lookup [DecidableEq α] [Ord κ] (key : α → κ) (cache : Cache κ link)
    (id : α) : Option (Answer link id) :=
  (cache.getD (key id) []).findSome? fun ⟨stored, answer⟩ =>
    if same : stored = id then some ⟨answer.value, same ▸ answer.correct⟩ else none

/-- Store a verified answer after a cache miss. -/
private def save [Ord κ] (key : α → κ) (cache : Cache κ link)
    (id : α) (answer : Answer link id) : Cache κ link :=
  cache.insert (key id) (⟨id, answer⟩ :: cache.getD (key id) [])

/-- A missing entry ends the walk at any fuel. -/
private def absentAnswer (link : α → ParentLink α σ) (id : α) (h : link id = .absent) :
    Answer link id := ⟨none, fun fuel => by cases fuel <;> simp [walk, atFuel, h]⟩

/-- A root consumes exactly one unit of fuel. -/
private def rootAnswer (link : α → ParentLink α σ) (id : α) (h : link id = .root value) :
    Answer link id := ⟨some (1, value), fun fuel => by cases fuel <;> simp [walk, atFuel, h]⟩

/-- A child consumes one extra fuel unit and extends the parent's summary. -/
private def parentAnswer (link : α → ParentLink α σ) (id : α)
    (h : link id = .parent base extend) (parent : Answer link base) : Answer link id :=
  ⟨parent.value.map (fun (depth, value) => (depth + 1, extend value)), fun fuel => by
    cases hp : parent.value with
    | none => cases fuel <;> simp [walk, h, parent.correct, hp, atFuel]
    | some pair =>
      rcases pair with ⟨depth, value⟩
      cases fuel with
      | zero => simp [walk, atFuel]
      | succ fuel =>
        by_cases enough : depth ≤ fuel <;>
          simp [walk, h, parent.correct, hp, atFuel, enough]⟩

/-- Resolve missing ancestors once. A search that exhausts its fuel leaves no cached answer. -/
private def resolve [DecidableEq α] [Ord κ] (key : α → κ) (link : α → ParentLink α σ) :
    Nat → (id : α) → Cache κ link → Option (Answer link id) × Cache κ link
  | 0, _, cache => (none, cache)
  | fuel + 1, id, cache =>
    match lookup key cache id with
    | some found => (some found, cache)
    | none =>
      match h : link id with
      | .absent =>
        let answer := absentAnswer link id h
        (some answer, save key cache id answer)
      | .root _ =>
        let answer := rootAnswer link id h
        (some answer, save key cache id answer)
      | .parent base _ =>
        let (found, next) := resolve key link fuel base cache
        match found with
        | none => (none, next)
        | some inherited =>
          let answer := parentAnswer link id h inherited
          (some answer, save key next id answer)

/-- A catalog-wide lookup shares ancestor summaries and checks other keys with the same bound. -/
def indexed [DecidableEq α] [Ord κ] (key : α → κ) (link : α → ParentLink α σ)
    (ids : List α) (fuel : Nat) : α → Option σ :=
  let cache := ids.foldl (fun cache id => (resolve key link fuel id cache).2) ∅
  fun id => match lookup key cache id with
    | some answer => atFuel answer.value fuel
    | none => walk link fuel id

/-- The shared fold preserves every bounded parent walk, including cycles and missing entries. -/
theorem indexed_eq [DecidableEq α] [Ord κ] (key : α → κ) (link : α → ParentLink α σ)
    (ids : List α) (fuel : Nat) : indexed key link ids fuel = walk link fuel := by
  funext id
  unfold indexed
  split
  next found _ => exact (found.correct fuel).symm
  next => rfl

#print axioms indexed_eq

end ParentLink
end CIL.Extraction
