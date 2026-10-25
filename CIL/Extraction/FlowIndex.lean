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

/-- Build a balanced index with structural fuel so kernel reduction needs no
    evaluation of well-foundedness proofs. -/
def FlowIndex.build : Nat → List α → FlowIndex α
  | 0, _ => .empty
  | _ + 1, [] => .empty
  | _ + 1, [value] => .leaf value
  | fuel + 1, first :: second :: rest =>
    let values := first :: second :: rest
    let middle := values.length / 2
    .branch middle (.build fuel (values.take middle)) (.build fuel (values.drop middle))

/-- Sufficient fuel makes the balanced index agree with optional list indexing. -/
theorem FlowIndex.get?_build (fuel : Nat) (values : List α) (enough : values.length ≤ fuel)
    (index : Nat) : (FlowIndex.build fuel values).get? index = values[index]? := by
  induction fuel generalizing values index with
  | zero =>
    have empty : values = [] := List.length_eq_zero_iff.mp (by omega)
    subst values
    rfl
  | succ fuel ih =>
    cases values with
    | nil => rfl
    | cons first rest =>
      cases rest with
      | nil => simp [FlowIndex.build, FlowIndex.get?]; split <;> simp_all
      | cons second rest =>
        simp only [FlowIndex.build, FlowIndex.get?]
        have leftBound : ((first :: second :: rest).take
            ((first :: second :: rest).length / 2)).length ≤ fuel := by
          simp only [List.length_take, List.length_cons] at *
          omega
        have rightBound : ((first :: second :: rest).drop
            ((first :: second :: rest).length / 2)).length ≤ fuel := by
          simp only [List.length_drop, List.length_cons] at *
          omega
        split
        · rw [ih _ leftBound, List.getElem?_take]
          simp_all
        · rw [ih _ rightBound, List.getElem?_drop]
          congr 1
          omega

#print axioms FlowIndex.get?_build

/-- Construct a balanced index; each level traverses the certificate only once. -/
def FlowIndex.ofList (values : List α) : FlowIndex α := .build values.length values

/-- Indexing a balanced certificate is exactly optional list indexing, including bounds. -/
theorem FlowIndex.get?_ofList (values : List α) (index : Nat) :
    (FlowIndex.ofList values).get? index = values[index]? :=
  FlowIndex.get?_build _ _ (Nat.le_refl _) _

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
    cases features <;> cases states <;> cases code <;> simp_all [all3]
  | cons instruction raw ih =>
    cases features <;> cases states <;> cases code <;> simp_all [all3]

#print axioms all3_zip_states

end CIL.Extraction
