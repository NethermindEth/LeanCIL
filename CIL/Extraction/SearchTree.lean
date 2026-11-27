/-!
# Numeric search trees

Balanced trees index metadata rows and runtime models by number. A lookup follows one branch
at each key. The extractor can also emit the same constructors directly as a literal.
-/

namespace CIL.Extraction

/-- A binary search tree keyed by number, built balanced from entries in ascending key order, so a
    lookup costs the logarithm of the entry count and the tree can be written out as a literal. -/
inductive SearchTree (α : Type) where
  | leaf
  | node (left : SearchTree α) (key : Nat) (value : α) (right : SearchTree α)
  deriving DecidableEq, Repr

namespace SearchTree

variable {α : Type}

/-- The value stored under `wanted`. -/
def find? : SearchTree α → Nat → Option α
  | .leaf, _ => none
  | .node left key value right, wanted =>
    match compare wanted key with
    | .lt => find? left wanted
    | .gt => find? right wanted
    | .eq => some value

/-- The entry with the least key above `wanted`. -/
def above? : SearchTree α → Nat → Option (Nat × α)
  | .leaf, _ => none
  | .node left key value right, wanted =>
    if wanted < key then
      match above? left wanted with
      | some entry => some entry
      | none => some (key, value)
    else above? right wanted

/-- The entries in ascending key order. -/
def toList : SearchTree α → List (Nat × α)
  | .leaf => []
  | .node left key value right => left.toList ++ (key, value) :: right.toList

/-- The tree of the first `count` entries, taking `count / 2` of them to the left of the root, and
    the entries left over. `fuel` bounds the depth. -/
private def build : Nat → Nat → List (Nat × α) → SearchTree α × List (Nat × α)
  | 0, _, rest => (.leaf, rest)
  | fuel + 1, count, rest =>
    if count == 0 then (.leaf, rest)
    else
      let leftCount := count / 2
      let (left, afterLeft) := build fuel leftCount rest
      match afterLeft with
      | [] => (left, [])
      | (key, value) :: afterRoot =>
        let (right, remaining) := build fuel (count - 1 - leftCount) afterRoot
        (.node left key value right, remaining)

/-- The balanced tree of entries in ascending key order. -/
def ofSorted (entries : List (Nat × α)) : SearchTree α :=
  (build entries.length entries.length entries).1

/-- The in-order entries of a partial build followed by its unused input recover the input. -/
private theorem build_preserves (fuel count : Nat) (entries : List (Nat × α)) :
    (build fuel count entries).1.toList ++ (build fuel count entries).2 = entries := by
  induction fuel generalizing count entries with
  | zero => rfl
  | succ fuel ih =>
    by_cases empty : count == 0
    · simp [build, empty, toList]
    · cases leftBuilt : build fuel (count / 2) entries with
      | mk left afterLeft =>
        have leftRest := ih (count / 2) entries
        rw [leftBuilt] at leftRest
        cases afterLeft with
        | nil => simpa [build, empty, leftBuilt] using leftRest
        | cons entry rest =>
          obtain ⟨key, value⟩ := entry
          cases rightBuilt : build fuel (count - 1 - count / 2) rest with
          | mk right afterRight =>
            have rightRest := ih (count - 1 - count / 2) rest
            rw [rightBuilt] at rightRest
            change right.toList ++ afterRight = rest at rightRest
            simpa [build, empty, leftBuilt, rightBuilt, toList, List.append_assoc, rightRest]
              using leftRest

#print axioms build_preserves

/-- Every entry of the balanced tree comes from the supplied list. -/
theorem mem_ofSorted {entries : List (Nat × α)} {entry : Nat × α}
    (member : entry ∈ (ofSorted entries).toList) : entry ∈ entries := by
  rw [← build_preserves entries.length entries.length entries]
  exact List.mem_append_left _ member

#print axioms mem_ofSorted

/-- The first key that does not ascend strictly from its predecessor. -/
def firstOutOfOrder : Option Nat → List (Nat × α) → Option Nat
  | _, [] => none
  | none, (key, _) :: rest => firstOutOfOrder (some key) rest
  | some previous, (key, _) :: rest =>
    if previous < key then firstOutOfOrder (some key) rest else some key

end SearchTree

end CIL.Extraction
