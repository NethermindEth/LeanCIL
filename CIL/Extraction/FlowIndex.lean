import CIL.Extraction.Lockstep
import Init.Omega

/-!
# Certificate successor lookup

A balanced index serves branch targets, while adjacent successor states are read directly
from the remaining certificate. The lookup theorem preserves the list-based validation rules.
-/

namespace CIL.Extraction

/-- A certificate index with explicit subtree lengths and no implicit default values. -/
inductive FlowIndex (α : Type) where
  | empty
  | leaf (value : α)
  | branch (leftSize : Nat) (left right : FlowIndex α)

/-- Lookup rejects every index outside the indexed certificate. -/
def FlowIndex.get? : FlowIndex α → Nat → Option α
  | .empty, _ => none
  | .leaf value, index => if index = 0 then some value else none
  | .branch size left right, index =>
    if index < size then left.get? index else right.get? (index - size)

/-- Consume a prefix into a balanced index, returning the untouched suffix. Structural
    fuel avoids evaluating well-foundedness proofs during kernel reduction. -/
def FlowIndex.build : Nat → Nat → List α → FlowIndex α × List α
  | 0, _, values => (.empty, values)
  | _ + 1, 0, values => (.empty, values)
  | _ + 1, 1, [] => (.empty, [])
  | _ + 1, 1, value :: values => (.leaf value, values)
  | fuel + 1, count + 2, values =>
    let middle := (count + 2) / 2
    let (left, rest) := FlowIndex.build fuel middle values
    let (right, rest) := FlowIndex.build fuel (count + 2 - middle) rest
    (.branch middle left right, rest)

/-- Building a bounded prefix consumes exactly that prefix and preserves optional lookup. -/
theorem FlowIndex.build_spec (fuel count : Nat) (values : List α)
    (enough : count ≤ fuel) (bounded : count ≤ values.length) :
    (FlowIndex.build fuel count values).2 = values.drop count ∧
      ∀ index, (FlowIndex.build fuel count values).1.get? index = (values.take count)[index]? := by
  induction fuel generalizing count values with
  | zero =>
    have : count = 0 := by omega
    subst count
    simp [FlowIndex.build, FlowIndex.get?]
  | succ fuel ih =>
    cases count with
    | zero => simp [FlowIndex.build, FlowIndex.get?]
    | succ count =>
      cases count with
      | zero =>
        cases values with
        | nil => simp at bounded
        | cons value rest =>
          simp only [FlowIndex.build, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
            List.take_zero, true_and, FlowIndex.get?]
          intro index
          cases index <;> simp
      | succ count =>
        let middle := (count + 2) / 2
        have middleBound : middle ≤ fuel := by dsimp [middle]; omega
        have remainderBound : count + 2 - middle ≤ fuel := by dsimp [middle]; omega
        have leftSpec := ih middle values middleBound (by omega)
        have rightSpec := ih (count + 2 - middle) (values.drop middle) remainderBound (by
          simp only [List.length_drop]
          omega)
        simp only [FlowIndex.build]
        change (FlowIndex.build fuel (count + 2 - middle)
          (FlowIndex.build fuel middle values).2).2 = _ ∧ _
        rw [leftSpec.1]
        constructor
        · rw [rightSpec.1, List.drop_drop]
          congr 1
          dsimp [middle]
          omega
        · intro index
          simp only [FlowIndex.get?]
          change (if index < middle then _ else _) = _
          split
          · rename_i before
            rw [leftSpec.2, List.getElem?_take, List.getElem?_take,
              ite_eq_left before, ite_eq_left (by dsimp [middle] at before; omega)]
          · rename_i after
            rw [rightSpec.2, List.getElem?_take, List.getElem?_take]
            by_cases inside : index < count + 2
            · rw [ite_eq_left (by omega), ite_eq_left inside, List.getElem?_drop]
              congr 1
              omega
            · rw [ite_eq_right (by omega), ite_eq_right inside]

#print axioms FlowIndex.build_spec

/-- Construct a balanced index by consuming every list cell once after measuring its length. -/
def FlowIndex.ofList (values : List α) : FlowIndex α :=
  (FlowIndex.build values.length values.length values).1

/-- Indexing a balanced certificate is exactly optional list indexing, including bounds. -/
theorem FlowIndex.get?_ofList (values : List α) (index : Nat) :
    (FlowIndex.ofList values).get? index = values[index]? := by
  simpa [FlowIndex.ofList] using
    (FlowIndex.build_spec values.length values.length values (Nat.le_refl _) (Nat.le_refl _)).2 index

#print axioms FlowIndex.get?_ofList

/-- Check parallel lists using the next certificate entry for fallthrough edges. -/
def all3Flow (check : (Nat → Option β) → α → β → γ → Bool)
    (index : FlowIndex β) (pc : Nat) : List α → List β → List γ → Bool
  | first :: rest, state :: states, emitted :: code =>
    check (fun target => if target = pc + 1 then states.head? else index.get? target)
      first state emitted && all3Flow check index (pc + 1) rest states code
  | [], [], [] => true
  | _, _, _ => false

/-- Streaming fallthrough and indexed branches preserve every check of the list validator. -/
theorem all3Flow_eq (check : (Nat → Option β) → α → β → γ → Bool)
    (values : List β) (pc : Nat) (raw : List α) (states : List β) (code : List γ)
    (suffix : states = values.drop pc) :
    all3Flow check (.ofList values) pc raw states code =
      all3 (check (fun target => values[target]?)) raw states code := by
  induction raw generalizing pc states code with
  | nil => cases states <;> cases code <;> rfl
  | cons first rest ih =>
    cases states with
    | nil => cases code <;> rfl
    | cons state states =>
      cases code with
      | nil => rfl
      | cons emitted code =>
        have tail : states = values.drop (pc + 1) := by
          simpa using congrArg List.tail suffix
        have next : states.head? = values[pc + 1]? := by
          rw [tail, List.head?_drop]
        simp only [all3Flow, all3]
        have lookup : (fun target =>
            if target = pc + 1 then states.head? else (FlowIndex.ofList values).get? target) =
            (fun target => values[target]?) := by
          funext target
          split <;> simp_all [FlowIndex.get?_ofList]
        rw [lookup, ih (pc + 1) states code tail]

#print axioms all3Flow_eq

/-- Pairing equally long state lists that cover the raw sites changes neither site alignment
    nor mismatch rejection. -/
theorem all3_zip_states (check : α → β → γ → δ → Bool)
    (raw : List α) (features : List β) (states : List γ) (code : List δ)
    (lengths : features.length = states.length) (covered : raw.length ≤ features.length) :
    all3 (fun instruction (feature, state) emitted => check instruction feature state emitted)
        raw (features.zip states) code =
      all3 (fun (instruction, feature) state emitted => check instruction feature state emitted)
        (raw.zip features) states code := by
  induction raw generalizing features states code with
  | nil =>
    cases features with
    | nil =>
      have empty : states = [] := List.length_eq_zero_iff.mp lengths.symm
      subst states
      cases code <;> rfl
    | cons feature features =>
      cases states with
      | nil => simp at lengths
      | cons state states => cases code <;> rfl
  | cons instruction raw ih =>
    cases features with
    | nil => simp at covered
    | cons feature features =>
      cases states with
      | nil => simp at lengths
      | cons state states =>
        cases code with
        | nil => rfl
        | cons emitted code =>
          simp only [List.zip_cons_cons, all3]
          rw [ih features states code (by simpa using lengths) (by simpa using covered)]

#print axioms all3_zip_states

end CIL.Extraction
