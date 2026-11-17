import StrictBinding.Evidence

/-!
# Tables sorted by a key

ECMA-335 requires several metadata tables to be sorted by a primary key, and GenericParam by a
secondary key as well (II.22). A claim names a table of a pinned image and the columns of its
key; `sortedBound` reads the key of every row once and fails at the first row whose key is
below the key of the row before it. `KeysSorted` states the order as reads of the image and
`keysSorted_of_sortedBound` proves that a successful check means it. The audit never reads the
`Sorted` mask of the table stream header, which the standard defines only as a bit vector of
sorted tables. Checks that read a few rows of a table, such as the nesting of a type definition,
conclude facts about the whole table only together with this fact.
-/

namespace StrictBinding

open CIL.Safety (except_bind_ok)

/-- The key of row `row` of `table`: the values of the key columns, in order. -/
def keyAt (image : PreparedImage) (table row : Nat) (key : List Nat) :
    Except AuditError (List Nat) :=
  key.mapM fun column => image.layout.cell image.view (tokenOf table row) column

/-- Whether key `lower` is at most key `upper` in lexicographic order. -/
def keyLe : List Nat → List Nat → Bool
  | first :: rest, other :: others => first < other || (first == other && keyLe rest others)
  | _, _ => true

/-- Every row of `table` in the image has a key at most the key of the row after it. -/
def KeysSorted (image : PreparedImage) (table : Nat) (key : List Nat) : Prop :=
  ∀ row, 1 ≤ row → row < image.layout.rowCount table →
    ∃ lower upper, keyAt image table row key = .ok lower ∧
      keyAt image table (row + 1) key = .ok upper ∧ keyLe lower upper = true

/-- The rows after `row`, at most `fuel` of them, each have a key at least the key of the row
    before; `previous` is the key of `row`. -/
def sortedFrom (image : PreparedImage) (table : Nat) (key : List Nat) :
    Nat → Nat → List Nat → Except AuditError Unit
  | 0, _, _ => pure ()
  | fuel + 1, row, previous => do
    let next ← keyAt image table (row + 1) key
    if keyLe previous next then sortedFrom image table key fuel (row + 1) next
    else throw (.unsortedTable table (row + 1))

/-- The rows of `table` are sorted by `key`. The check reads the key of each row once. -/
def sortedBound (image : PreparedImage) (table : Nat) (key : List Nat) :
    Except AuditError Unit :=
  match image.layout.rowCount table with
  | 0 => pure ()
  | count + 1 => do
    let first ← keyAt image table 1 key
    sortedFrom image table key count 1 first

/-- A claim that `table` of the image pinned under `identity` is sorted by the columns `key`. -/
structure SortedClaim where
  identity : String
  table : Nat
  key : List Nat
  deriving DecidableEq, Repr

/-- The claim holds in the image pinned under the claim's identity. -/
def sortedClaimBound (prepared : List PreparedImage) (claim : SortedClaim) :
    Except AuditError Unit := do
  sortedBound (← located prepared claim.identity) claim.table claim.key

/-- Every claimed table is sorted by its key in the image its identity names, against one
    preparation of the images. -/
def TablesSorted (images : List PinnedImage) (claims : List SortedClaim) : Prop :=
  ClaimsHold sortedClaimBound images claims

instance (images : List PinnedImage) (claims : List SortedClaim) :
    Decidable (TablesSorted images claims) :=
  inferInstanceAs (Decidable (ClaimsHold _ _ _))

/-- A successful walk from `row` means each of the walked rows has a key at least the key of the
    row before it. -/
theorem sortedFrom_ok {image : PreparedImage} {table : Nat} {key : List Nat} :
    ∀ {fuel row : Nat} {previous : List Nat},
      sortedFrom image table key fuel row previous = .ok () →
      keyAt image table row key = .ok previous →
      ∀ at_, row ≤ at_ → at_ < row + fuel →
        ∃ lower upper, keyAt image table at_ key = .ok lower ∧
          keyAt image table (at_ + 1) key = .ok upper ∧ keyLe lower upper = true
  | 0, _, _, _, _, at_, low, high => by omega
  | fuel + 1, row, previous, walked, readPrevious, at_, low, high => by
    unfold sortedFrom at walked
    obtain ⟨next, readNext, walked⟩ := except_bind_ok walked
    split at walked
    · rename_i ordered
      by_cases here : at_ = row
      · subst here
        exact ⟨previous, next, readPrevious, readNext, ordered⟩
      · exact sortedFrom_ok walked readNext at_ (by omega) (by omega)
    · exact absurd walked throw_ne_ok

#print axioms sortedFrom_ok

/-- A table check that succeeds means the table is sorted by the key. -/
theorem keysSorted_of_sortedBound {image : PreparedImage} {table : Nat} {key : List Nat}
    (checked : sortedBound image table key = .ok ()) : KeysSorted image table key := by
  intro row low high
  unfold sortedBound at checked
  split at checked
  · rename_i empty
    omega
  · rename_i count rows
    obtain ⟨first, readFirst, walked⟩ := except_bind_ok checked
    exact sortedFrom_ok walked readFirst row low (by omega)

#print axioms keysSorted_of_sortedBound

/-- Every claimed table of a successful check is sorted in the image its identity selects, from
    one preparation of the pinned images. -/
theorem keysSorted_of_tablesSorted {images : List PinnedImage} {claims : List SortedClaim}
    (bound : TablesSorted images claims) :
    ∃ prepared, prepare images = .ok prepared ∧
      ∀ claim ∈ claims, ∃ image, located prepared claim.identity = .ok image ∧
        KeysSorted image claim.table claim.key := by
  obtain ⟨prepared, decoded, checks⟩ := check_of_claimsHold bound
  refine ⟨prepared, decoded, fun claim member => ?_⟩
  have one := checks claim member
  unfold sortedClaimBound at one
  cases found : located prepared claim.identity with
  | error error => simp [found, bind, Except.bind, ok] at one
  | ok image =>
    refine ⟨image, rfl, keysSorted_of_sortedBound ?_⟩
    cases result : sortedBound image claim.table claim.key with
    | error error => simp [found, result, bind, Except.bind, ok] at one
    | ok value => cases value; rfl

#print axioms keysSorted_of_tablesSorted

/-- A one-column key is the column's value. -/
theorem keyAt_single {image : PreparedImage} {table row column : Nat} {key : List Nat}
    (read : keyAt image table row [column] = .ok key) :
    ∃ value, image.layout.cell image.view (tokenOf table row) column = .ok value ∧
      key = [value] := by
  unfold keyAt at read
  cases cell : image.layout.cell image.view (tokenOf table row) column with
  | error error => simp [cell, List.mapM_cons, bind, Except.bind] at read
  | ok value =>
    simp only [cell, List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at read
    exact ⟨value, rfl, read.symm⟩

#print axioms keyAt_single

/-- One-column keys are ordered as their values. -/
theorem keyLe_single {lower upper : Nat} (ordered : keyLe [lower] [upper] = true) :
    lower ≤ upper := by
  simp only [keyLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    and_true] at ordered
  omega

#print axioms keyLe_single

/-- In a table sorted by one column, a row's value is at most the value of any later row. -/
theorem value_le_of_keysSorted {image : PreparedImage} {table column : Nat}
    (sorted : KeysSorted image table [column]) :
    ∀ {lower upper first last : Nat}, 1 ≤ lower → lower ≤ upper →
      upper ≤ image.layout.rowCount table →
      image.layout.cell image.view (tokenOf table lower) column = .ok first →
      image.layout.cell image.view (tokenOf table upper) column = .ok last → first ≤ last
  | lower, 0, _, _, low, ordered, _, _, _ => by omega
  | lower, upper + 1, first, last, low, ordered, inside, readFirst, readLast => by
    by_cases same : lower = upper + 1
    · subst same
      rw [readFirst] at readLast
      cases readLast
      exact Nat.le_refl _
    · obtain ⟨below, above, readBelow, readAbove, keyed⟩ :=
        sorted upper (by omega) (by omega)
      obtain ⟨middle, readMiddle, rfl⟩ := keyAt_single readBelow
      obtain ⟨value, readValue, rfl⟩ := keyAt_single readAbove
      rw [readLast] at readValue
      cases readValue
      exact Nat.le_trans
        (value_le_of_keysSorted sorted low (by omega) (by omega) readFirst readMiddle)
        (keyLe_single keyed)

#print axioms value_le_of_keysSorted

end StrictBinding
