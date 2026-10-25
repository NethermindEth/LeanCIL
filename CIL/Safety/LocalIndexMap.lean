import CIL.Safety.Frames

/-!
# Order-preserving local deletion maps

A map records each retained or deleted target slot. Retained positions remain in order,
so byte homes can be allocated sequentially while unused target slots occur anywhere.
-/

namespace CIL.Safety

/-- The target slots retained by a source method, in declaration order. -/
inductive LocalIndexMap where
  | nil
  | keep (rest : LocalIndexMap)
  | skip (rest : LocalIndexMap)
  deriving DecidableEq, Repr

namespace LocalIndexMap

/-- Number of declarations retained by the source method. -/
def sourceLength : LocalIndexMap → Nat
  | .nil => 0
  | .keep rest => rest.sourceLength + 1
  | .skip rest => rest.sourceLength

/-- Number of declarations in the target method, including dead slots. -/
def targetLength : LocalIndexMap → Nat
  | .nil => 0
  | .keep rest | .skip rest => rest.targetLength + 1

/-- Relocate a source local operand to its retained target declaration. -/
def index : LocalIndexMap → Nat → Nat
  | .nil, position => position
  | .keep _, 0 => 0
  | .keep rest, position + 1 => rest.index position + 1
  | .skip rest, position => rest.index position + 1

/-- Every retained operand addresses a declared target slot. -/
theorem index_bound (mapping : LocalIndexMap) (position : Nat)
    (bound : position < mapping.sourceLength) : mapping.index position < mapping.targetLength := by
  induction mapping generalizing position with
  | nil => exact False.elim (Nat.not_lt_zero position bound)
  | keep rest induction =>
    cases position with
    | zero => exact Nat.zero_lt_succ _
    | succ position =>
      exact Nat.succ_lt_succ (induction position (Nat.lt_of_succ_lt_succ bound))
  | skip rest induction => exact Nat.succ_lt_succ (induction position bound)
#print axioms index_bound

/-- Retained slots preserve order, including operands after an interleaved dead declaration. -/
theorem index_strict (mapping : LocalIndexMap) (left right : Nat) (ordered : left < right) :
    mapping.index left < mapping.index right := by
  induction mapping generalizing left right with
  | nil => exact ordered
  | skip rest induction => exact Nat.succ_lt_succ (induction left right ordered)
  | keep rest induction =>
    cases left with
    | zero => cases right with
      | zero => exact False.elim (Nat.lt_irrefl _ ordered)
      | succ right => exact Nat.zero_lt_succ _
    | succ left => cases right with
      | zero => exact False.elim (Nat.not_lt_zero _ ordered)
      | succ right =>
        exact Nat.succ_lt_succ (induction left right (Nat.lt_of_succ_lt_succ ordered))
#print axioms index_strict

/-- A retained local operand cannot alias another retained local operand. -/
theorem index_injective (mapping : LocalIndexMap) {left right : Nat}
    (equal : mapping.index left = mapping.index right) : left = right := by
  rcases Nat.lt_trichotomy left right with ordered | equal | ordered
  · exact False.elim (Nat.ne_of_lt (mapping.index_strict _ _ ordered) equal)
  · exact equal
  · exact False.elim (Nat.ne_of_lt (mapping.index_strict _ _ ordered) equal.symm)
#print axioms index_injective

/-- Appended parameter homes shift by the declaration-count difference without being deleted. -/
theorem index_tail (mapping : LocalIndexMap) (position : Nat) :
    mapping.index (mapping.sourceLength + position) = mapping.targetLength + position := by
  induction mapping with
  | nil => rfl
  | keep rest induction =>
    simpa only [sourceLength, targetLength, Nat.add_right_comm, index] using
      congrArg Nat.succ induction
  | skip rest induction =>
    simpa only [sourceLength, targetLength, index, Nat.add_right_comm] using
      congrArg Nat.succ induction
#print axioms index_tail

/-- A target list contains corresponding retained entries and arbitrary deleted entries. -/
inductive Selects (relation : α → β → Prop) : LocalIndexMap → List α → List β → Prop
  | nil : Selects relation .nil [] []
  | keep {mapping source target} {left : α} {right : β}
      (head : relation left right) (rest : Selects relation mapping source target) :
      Selects relation (.keep mapping) (left :: source) (right :: target)
  | skip {mapping source target} (right : β) (rest : Selects relation mapping source target) :
      Selects relation (.skip mapping) source (right :: target)

/-- Selection witnesses bind the exact source and target declaration counts. -/
theorem Selects.lengths {relation : α → β → Prop} {mapping : LocalIndexMap}
    {source : List α} {target : List β} (selected : Selects relation mapping source target) :
    source.length = mapping.sourceLength ∧ target.length = mapping.targetLength := by
  induction selected with
  | nil => exact ⟨rfl, rfl⟩
  | keep head rest induction =>
    exact ⟨congrArg Nat.succ induction.1, congrArg Nat.succ induction.2⟩
  | skip right rest induction => exact ⟨induction.1, congrArg Nat.succ induction.2⟩
#print axioms Selects.lengths

/-- Looking up a retained local yields corresponding entries under its relocated operand. -/
theorem Selects.getElem? {relation : α → β → Prop} {mapping : LocalIndexMap}
    {source : List α} {target : List β} (selected : Selects relation mapping source target)
    (position : Nat) (bound : position < mapping.sourceLength) :
    Option.Rel relation source[position]? target[mapping.index position]? := by
  induction selected generalizing position with
  | nil => exact False.elim (Nat.not_lt_zero position bound)
  | keep head rest induction =>
    cases position with
    | zero => exact .some head
    | succ position => exact induction position (Nat.lt_of_succ_lt_succ bound)
  | skip right rest induction => exact induction position bound
#print axioms Selects.getElem?

/-- Out-of-range operands remain out of range after all retained and dead declarations. -/
theorem Selects.getElem?_all {relation : α → β → Prop} {mapping : LocalIndexMap}
    {source : List α} {target : List β} (selected : Selects relation mapping source target)
    (position : Nat) :
    Option.Rel relation source[position]? target[mapping.index position]? := by
  by_cases bound : position < mapping.sourceLength
  · exact selected.getElem? position bound
  · have sourceOutside : source.length ≤ position := by
      rw [selected.lengths.1]
      omega
    have targetOutside : target.length ≤ mapping.index position := by
      rw [selected.lengths.2]
      have decomposition : position = mapping.sourceLength + (position - mapping.sourceLength) := by
        omega
      rw [decomposition, mapping.index_tail]
      omega
    simp only [List.getElem?_eq_none sourceOutside, List.getElem?_eq_none targetOutside]
    exact .none
#print axioms Selects.getElem?_all

/-- Updating a retained local preserves every other retained slot and all dead positions. -/
theorem Selects.set {relation : α → β → Prop} {mapping : LocalIndexMap}
    {source : List α} {target : List β} (selected : Selects relation mapping source target)
    (position : Nat) (bound : position < mapping.sourceLength) (left : α) (right : β)
    (related : relation left right) :
    Selects relation mapping (source.set position left)
      (target.set (mapping.index position) right) := by
  induction selected generalizing position with
  | nil => exact False.elim (Nat.not_lt_zero position bound)
  | keep head rest induction =>
    cases position with
    | zero => exact .keep related rest
    | succ position =>
      exact .keep head (induction position (Nat.lt_of_succ_lt_succ bound))
  | skip right rest induction => exact .skip right (induction position bound)
#print axioms Selects.set

/-- Strengthening the entry correspondence preserves the same local deletion positions. -/
theorem Selects.imp {before after : α → β → Prop} {mapping : LocalIndexMap}
    {source : List α} {target : List β} (selected : Selects before mapping source target)
    (implies : ∀ left right, before left right → after left right) :
    Selects after mapping source target := by
  induction selected with
  | nil => exact .nil
  | keep head rest induction => exact .keep (implies _ _ head) induction
  | skip right rest induction => exact .skip right induction
#print axioms Selects.imp

end LocalIndexMap
end CIL.Safety
