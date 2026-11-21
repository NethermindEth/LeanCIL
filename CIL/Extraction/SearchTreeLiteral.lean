import CIL.Extraction.MetadataBytes

/-!
# Literal search trees

A table read by many kernel decisions is written out once as a literal `SearchTree` whose
leaves hold its entry terms, grouped by a number key, so a lookup costs the depth of the tree and
the comparison within one group, never the size of the table, and the kernel never sorts or
splits the entries. `SearchTree.groupedLiteral` builds that literal for an elaborator, and
`SearchTree.find?_mem_toList` lets a proof read a found group as one of the tree's entries
whatever order the tree holds.
-/

namespace CIL.Extraction

open Lean Meta in
/-- The literal balanced tree of key-ordered groups of `entryType` terms, split as
    `SearchTree.ofSorted` splits. -/
private partial def literalTree (entryType : Expr) (groups : Array (Nat × Array Expr)) :
    MetaM Expr := do
  let valueType := mkApp (mkConst ``List [0]) entryType
  if groups.isEmpty then return mkApp (mkConst ``SearchTree.leaf) valueType
  let leftCount := groups.size / 2
  let (key, cells) := groups[leftCount]!
  return mkApp5 (mkConst ``SearchTree.node) valueType
    (← literalTree entryType (groups.extract 0 leftCount)) (mkNatLit key)
    (← mkListLit entryType cells.toList)
    (← literalTree entryType (groups.extract (leftCount + 1) groups.size))

open Lean Meta in
/-- The literal `SearchTree (List entryType)` of `cells` grouped under `keys`, one key per cell:
    groups in ascending key order, each group's cells in list order. -/
def SearchTree.groupedLiteral (entryType : Expr) (cells : Array Expr) (keys : Array Nat) :
    MetaM Expr := do
  unless cells.size == keys.size do throwError "search tree: one key is needed per entry"
  let mut groups : Array (Nat × Array Expr) := #[]
  for (key, cell) in (keys.zip cells).toList.mergeSort fun left right => left.1 ≤ right.1 do
    match groups.back? with
    | some (last, group) =>
      groups := if last = key then groups.pop.push (key, group.push cell)
        else groups.push (key, #[cell])
    | none => groups := groups.push (key, #[cell])
  literalTree entryType groups

/-- A value `find?` gives is one of the tree's entries. -/
theorem SearchTree.find?_mem_toList {α : Type} :
    ∀ (tree : SearchTree α) (key : Nat) (value : α), tree.find? key = some value →
      (key, value) ∈ tree.toList
  | .leaf, _, _, found => by simp [SearchTree.find?] at found
  | .node left root stored right, key, value, found => by
    simp only [SearchTree.find?] at found
    simp only [SearchTree.toList, List.mem_append, List.mem_cons]
    split at found
    · exact .inl (SearchTree.find?_mem_toList left key value found)
    · exact .inr (.inr (SearchTree.find?_mem_toList right key value found))
    · rename_i same
      cases found
      exact .inr (.inl (by rw [Nat.compare_eq_eq.mp same]))

#print axioms SearchTree.find?_mem_toList

end CIL.Extraction
