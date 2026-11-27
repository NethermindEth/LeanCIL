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

/-- Verified answers grouped by the key of their complete class identity. -/
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

/-- Following the path from the checkpoint leaves at most this much fuel at the current class. -/
private abbrev OnPath (link : α → ParentLink α σ) (checkpoint id : α) : Prop :=
  ∀ fuel, (walk link fuel checkpoint).isSome → ∃ limit ≤ fuel, (walk link limit id).isSome

/-- Each traversed parent link consumes a positive amount of fuel. -/
private theorem parentFuel {id base : α} {link : α → ParentLink α σ}
    (h : link id = ParentLink.parent base extend) (fuel : Nat)
    (present : (walk link fuel id).isSome) :
    ∃ smaller < fuel, (walk link smaller base).isSome := by
  cases fuel with
  | zero => simp [walk] at present
  | succ fuel => exact ⟨fuel, Nat.lt_succ_self _, by simpa [walk, h] using present⟩

#print axioms parentFuel

/-- Move the current class one link farther away from its checkpoint. -/
private theorem nextOnPath {id base : α} {link : α → ParentLink α σ}
    (h : link id = ParentLink.parent base extend) (path : OnPath link checkpoint id) :
    OnPath link checkpoint base := by
  intro fuel present
  obtain ⟨limit, bounded, reached⟩ := path fuel present
  obtain ⟨smaller, less, next⟩ := parentFuel h limit reached
  exact ⟨smaller, Nat.le_trans (Nat.le_of_lt less) bounded, next⟩

#print axioms nextOnPath

/-- Returning to a checkpoint rules out a root at every fuel limit. -/
private def cycleAnswer {id base : α} {link : α → ParentLink α σ}
    (h : link id = ParentLink.parent base extend) (path : OnPath link base id) :
    Answer link base := by
  have noRoot : ∀ fuel, ¬(walk link fuel base).isSome := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro present
      obtain ⟨limit, bounded, reached⟩ := path fuel present
      obtain ⟨smaller, less, next⟩ := parentFuel h limit reached
      exact ih smaller (Nat.lt_of_lt_of_le less bounded) next
  refine ⟨none, fun fuel => ?_⟩
  cases found : walk link fuel base with
  | none => rfl
  | some value => exact False.elim (noRoot fuel (by simp [found]))

/-- The current checkpoint for constant-space cycle detection by successive doubling. -/
private structure Checkpoint (link : α → ParentLink α σ) (id : α) where
  start : α
  interval : Nat
  remaining : Nat
  path : OnPath link start id

/-- A new checkpoint starts at the current class. -/
private def Checkpoint.atId (link : α → ParentLink α σ) (id : α) (interval : Nat) :
    Checkpoint link id := ⟨id, interval, interval, fun fuel x => ⟨fuel, Nat.le_refl _, x⟩⟩

/-- When the interval expires the next class begins a doubled checkpoint interval. -/
private def Checkpoint.advance [DecidableEq α] {id base : α} {link : α → ParentLink α σ}
    (point : Checkpoint link id)
    (h : link id = ParentLink.parent base extend) : Answer link base ⊕ Checkpoint link base :=
  if closed : base = point.start then .inl (cycleAnswer h (closed.symm ▸ point.path))
  else if point.remaining == 1 then .inr (.atId link base (2 * point.interval))
  else .inr ⟨point.start, point.interval, point.remaining - 1, nextOnPath h point.path⟩

/-- Resolve missing ancestors once. A search that exhausts its fuel leaves no cached answer. -/
private def resolve [DecidableEq α] [Ord κ] (key : α → κ) (link : α → ParentLink α σ) :
    Nat → (id : α) → Cache κ link → (Unit → Answer link id ⊕ Checkpoint link id) →
      Option (Answer link id) × Cache κ link
  | 0, _, cache, _ => (none, cache)
  | fuel + 1, id, cache, check =>
    match lookup key cache id with
    | some found => (some found, cache)
    | none =>
      match check () with
      | .inl cycle => (some cycle, save key cache id cycle)
      | .inr point =>
        match h : link id with
        | .absent =>
          let answer := absentAnswer link id h
          (some answer, save key cache id answer)
        | .root _ =>
          let answer := rootAnswer link id h
          (some answer, save key cache id answer)
        | .parent base _ =>
          let (found, next) := resolve key link fuel base cache (fun _ => point.advance h)
          match found with
          | none => (none, next)
          | some inherited =>
            let answer := parentAnswer link id h inherited
            (some answer, save key next id answer)

/-- A catalog-wide lookup shares ancestor summaries and checks other keys with the same bound. -/
def indexed [DecidableEq α] [Ord κ] (key : α → κ) (link : α → ParentLink α σ)
    (ids : List α) (fuel : Nat) : α → Option σ :=
  -- Doubling reaches a checkpoint on a cycle within 2n links and repeats it within n more.
  let searchLimit := 3 * fuel + 1
  let cache := ids.foldl (fun cache id =>
    (resolve key link searchLimit id cache (fun _ => .inr (.atId link id 1))).2) ∅
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
