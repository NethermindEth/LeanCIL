import CIL.Extraction.PinnedIndex

/-! Package pin indices retain the complete raw tree produced by left-to-right insertions. -/

namespace Tests.PinnedIndexScaling.Construction
open CIL CIL.Extraction Std.DTreeMap.Internal CIL.Extraction.PinTable

/-- The tree shape with every stored key erased. -/
private def eraseKeys : PinTable.Tree α → PinTable.Tree Unit
  | .leaf => .leaf
  | .inner size _ _ left right => .inner size () () (eraseKeys left) (eraseKeys right)

/-- Erasing keys preserves the stored subtree sizes. -/
@[simp] private theorem size_eraseKeys (tree : PinTable.Tree α) :
    (eraseKeys tree).size = tree.size := by
  cases tree <;> rfl
#print axioms size_eraseKeys

/-- Right rebalancing depends only on subtree sizes and shapes. -/
private theorem erase_balance (nodeKey : α) (left right : PinTable.Tree α) :
    eraseKeys (Impl.balanceR! nodeKey () left right) =
      Impl.balanceR! () () (eraseKeys left) (eraseKeys right) := by
  fun_cases Impl.balanceR! nodeKey () left right <;> simp [Impl.balanceR!, eraseKeys, *] <;> rfl
#print axioms erase_balance

/-- Appending a maximum key changes the shape independently of its value. -/
private theorem erase_insertMax (key : α) (tree : PinTable.Tree α) :
    eraseKeys (tree.insertMax! key ()) = (eraseKeys tree).insertMax! () () := by
  induction tree with
  | leaf => rfl
  | inner size nodeKey value left right leftIH rightIH =>
    cases value
    simp only [Impl.insertMax!, eraseKeys, erase_balance, rightIH]
#print axioms erase_insertMax

/-- The in-order keys of a unit-valued tree. -/
private def keys : PinTable.Tree α → List α
  | .leaf => []
  | .inner _ nodeKey _ left right => keys left ++ nodeKey :: keys right

/-- In-order traversal agrees with Std's model of the tree. -/
private theorem keys_model (tree : PinTable.Tree α) :
    keys tree = tree.toListModel.map Sigma.fst := by
  induction tree <;> simp [keys, Impl.toListModel, *]
#print axioms keys_model

/-- Filling the erased shape consumes exactly the tree's original keys. -/
private theorem fill_erase (tree : PinTable.Tree α) (tail : List α) :
    fill (eraseKeys tree) (keys tree ++ tail) = (tree, tail) := by
  induction tree generalizing tail with
  | leaf => rfl
  | inner size nodeKey value left right leftIH rightIH =>
    cases value
    simp only [eraseKeys, fill, keys, List.append_assoc, List.cons_append, leftIH, rightIH]
#print axioms fill_erase

/-- Adjacent increasing keys are pairwise ordered under a transitive comparison. -/
private theorem sorted_of_ascending [Ord α] [Std.TransOrd α] :
    ∀ (items : List α), ascending items = true →
      items.Pairwise (fun a b => compare a b = .lt)
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: rest, ok => by
    simp only [ascending, Bool.and_eq_true, beq_iff_eq] at ok
    obtain ⟨less, tail⟩ := ok
    have ordered := sorted_of_ascending (b :: rest) tail
    apply List.pairwise_cons.mpr ⟨?_, ordered⟩
    intro x member
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ less
    · exact Std.TransCmp.lt_trans less ((List.pairwise_cons.mp ordered).1 x later)
#print axioms sorted_of_ascending

/-- Inserting a new largest key takes exactly the maximum-insertion path. -/
private theorem insert_max [Ord α] [Std.TransOrd α] (tree : PinTable.Tree α) (key : α)
    (afterKeys : ∀ a ∈ keys tree, compare a key = .lt) :
    tree.insert! key () = tree.insertMax! key () := by
  induction tree with
  | leaf => rfl
  | inner size nodeKey value left right leftIH rightIH =>
    have greater := Std.OrientedCmp.gt_of_lt (afterKeys nodeKey (by simp [keys]))
    have tail := rightIH (fun a member => afterKeys a (by simp [keys, member]))
    simp only [Impl.insert!, Impl.insertMax!, greater, tail]
#print axioms insert_max

/-- The raw tree obtained by inserting each key from left to right. -/
private def inserted [Ord α] (items : List α) : PinTable.Tree α :=
  items.foldl (fun tree a => tree.insert! a ()) .leaf

/-- Increasing insertions preserve balance and yield the count's shape and the original keys. -/
private theorem sorted_inserted [Ord α] [Std.TransOrd α] (reversed : List α)
    (ordered : reversed.reverse.Pairwise (fun a b => compare a b = .lt)) :
    (inserted reversed.reverse).Balanced ∧
      eraseKeys (inserted reversed.reverse) = ascendingShape reversed.length ∧
      keys (inserted reversed.reverse) = reversed.reverse := by
  induction reversed with
  | nil => exact ⟨.leaf, rfl, rfl⟩
  | cons nodeKey rest ih =>
    rw [List.reverse_cons] at ordered ⊢
    have parts := List.pairwise_append.mp ordered
    obtain ⟨balanced, shape, contents⟩ := ih parts.1
    have last : ∀ a ∈ keys (inserted rest.reverse), compare a nodeKey = .lt := by
      rw [contents]
      exact fun a ha => parts.2.2 a ha nodeKey (by simp)
    have step : inserted (rest.reverse ++ [nodeKey]) =
        (inserted rest.reverse).insertMax! nodeKey () := by
      simpa [inserted, List.foldl_append] using insert_max (inserted rest.reverse) nodeKey last
    rw [step]
    let checked := (inserted rest.reverse).insertMax nodeKey () balanced
    have equal := Impl.insertMax_eq_insertMax! (a := nodeKey) (b := ()) balanced
    refine ⟨equal ▸ checked.balanced_impl, ?_, ?_⟩
    · simp [erase_insertMax, shape, ascendingShape, Nat.repeat]
    · rw [keys_model, ← equal, Impl.toListModel_insertMax, List.map_append,
        ← keys_model, contents]
      rfl
#print axioms sorted_inserted

/-- Filling the count's shape produces exactly the original insertion tree. -/
private theorem materialized_eq [Ord α] [Std.TransOrd α] (items : List α)
    (ok : ascending items = true) :
    (fill (ascendingShape items.length) items).1 = inserted items := by
  have spec := sorted_inserted items.reverse (by simpa using sorted_of_ascending items ok)
  simp only [List.reverse_reverse, List.length_reverse] at spec
  have recover := fill_erase (inserted items) []
  rw [spec.2.1, spec.2.2, List.append_nil] at recover
  exact congrArg Prod.fst recover
#print axioms materialized_eq

/-- Raw map insertion uses the same rotations as its underlying tree. -/
private theorem inner_fold [Ord α] (items : List α) (start : Std.TreeMap.Raw α Unit) :
    (items.foldl (fun m a => m.insert a ()) start).inner.inner =
      items.foldl (fun tree a => tree.insert! a ()) start.inner.inner := by
  induction items generalizing start with
  | nil => rfl
  | cons nodeKey rest ih => exact ih _
#print axioms inner_fold

/-- The projected table equals inserting each item's key in the same order. -/
private theorem ofItems_eq [Ord α] [Std.TransOrd α] (key : β → α) (items : List β) :
    ofItems key items = items.foldl (fun entries item => entries.insert (key item) ()) {} := by
  obtain _ | ⟨one, items⟩ := items <;> try rfl
  obtain _ | ⟨two, items⟩ := items <;> try rfl
  obtain _ | ⟨three, items⟩ := items <;> try rfl
  obtain _ | ⟨four, items⟩ := items <;> try rfl
  simp only [ofItems]
  split <;> try rfl
  split <;> try rfl
  rename_i increasing
  have eq := (materialized_eq _ increasing).trans (inner_fold _ {}).symm
  have wrapped := congrArg (fun tree => (⟨⟨tree⟩⟩ : Std.TreeMap.Raw α Unit)) eq
  simp only [List.length_map, List.foldl_map] at wrapped
  exact wrapped
#print axioms ofItems_eq

/-- Metadata names inherit transitivity from the order on their encoded characters. -/
private instance : Std.TransOrd MetadataName := by
  change Std.TransCmp compare
  have same : (compare : MetadataName → MetadataName → Ordering) =
      compareOn MetadataName.code := by
    funext left right
    cases left with | mk left =>
      cases right with | mk right =>
        change (compare left right).then .eq = compare left right
        cases compare left right <;> rfl
  rw [same]
  infer_instance

/-- The simple-name index is structurally equal to inserting every package name in order. -/
theorem names_eq_insertions (identities : List AssemblyName) :
    indexPinNames identities =
      identities.foldl (fun entries pin => entries.insert pin.name ()) {} := by
  exact ofItems_eq AssemblyName.name identities
#print axioms names_eq_insertions

/-- The exact-identity index preserves every node, key, size and child of the insertion tree. -/
theorem exact_eq_insertions (identities : List AssemblyName) :
    indexPins identities = identities.foldl (fun entries pin => entries.insert pin ()) {} :=
  ofItems_eq id identities
#print axioms exact_eq_insertions

end Tests.PinnedIndexScaling.Construction
