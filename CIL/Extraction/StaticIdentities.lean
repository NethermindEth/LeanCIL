import CIL.Extraction.BodyDecoding

/-!
# Static identities

The model keys static storage by `StaticDescriptor.identity`, so an identity must stand for
exactly one field. `StaticIdentitiesValid` holds when, over every static site of the program, two
sites share an identity exactly when the tokens of their instructions resolve to the same
`Field` row of the same pinned assembly. A site's token is the one the body decoder records at
its pc (`BodyEvidence.statics`), and only for a field whose binding found its carried row.

Each body's recorded accesses are walked beside its sites once, and two sorts of the S pairs of
identity and field decide the rest: O(S log S) comparisons of numbers.
-/

namespace CIL.Extraction

/-- Metadata tokens are 32-bit, so an assembly's code and a token below this bound pack into one
    number, distinct for distinct pairs. -/
def tokenSpace : Nat := 2 ^ 32

/-- An assembly identity as one number: its bytes in base 256 after a leading 1, so distinct byte
    strings give distinct numbers; `none` when an entry is not a byte. -/
def identityCode (identity : List Nat) : Option Nat :=
  if identity.all (· < 256) then some (identity.foldl (fun code byte => code * 256 + byte) 1)
  else none

/-- The code of the identity of each slice a body carries, in the slices' order. -/
def BodyEvidence.sliceCodes (body : BodyEvidence) : List (Option Nat) :=
  body.identities.map identityCode

/-- The metadata slice and Field token a recorded static operand resolves to. -/
def BodyEvidence.staticFieldRow (body : BodyEvidence) (token : Nat) : Option (Nat × Nat) := do
  if metadataTableOf token == Table.field then return (0, token)
  (← body.tables.head?).link linkDefinition token

/-- The field a recorded static token names, packed as its assembly's code times `tokenSpace`
    plus its `Field` row token: a `Field` token is a row of the body's own assembly, and a
    `MemberRef` names the row its own slice links it to, the link the token's binding checked. -/
def BodyEvidence.staticField (body : BodyEvidence) (codes : List (Option Nat)) (token : Nat) :
    Option Nat := do
  let (position, row) ← body.staticFieldRow token
  let code ← (← codes[position]?)
  if row < tokenSpace then some (code * tokenSpace + row) else none

/-- The recorded token at each of the ascending `pcs`, walking them beside the recorded accesses
    in ascending index order; `none` when a pc records no access. -/
def siteTokens : List (Nat × Nat) → List Nat → Option (List Nat)
  | _, [] => some []
  | [], _ :: _ => none
  | (index, token) :: statics, pc :: pcs =>
    if pc < index then none
    else
      let (here, later) := (pc :: pcs).span (· == index)
      (siteTokens statics later).map (List.replicate here.length token ++ ·)

/-- Each static site of the method as its identity beside the field its pc's recorded token
    names; `none` when a site's pc records no bound static token. -/
def methodStaticPairs (method : Method) (body : BodyEvidence) : Option (List (Nat × Nat)) := do
  let tokens ← siteTokens body.statics (method.staticSites.map Prod.fst)
  let codes := body.sliceCodes
  (method.staticSites.zip tokens).mapM fun ((_, descriptor), token) => do
    pure (descriptor.identity, ← body.staticField codes token)

/-- The static sites of every method, each method read against the body at its position. -/
def programStaticPairs : Program → List BodyEvidence → Option (List (Nat × Nat))
  | method :: program, body :: bodies => do
    pure ((← methodStaticPairs method body) ++ (← programStaticPairs program bodies))
  | _, _ => some []

/-- Whether each pair after the first has a greater first number than the pair before it, or is
    that pair again. -/
def ascendingRuns : List (Nat × Nat) → Bool
  | first :: second :: rest =>
    (first.1 < second.1 || first == second) && ascendingRuns (second :: rest)
  | _ => true

/-- In ascending runs, every later pair has a greater first number than the head or equals it. -/
theorem ascendingRuns_head : ∀ {first : Nat × Nat} {rest : List (Nat × Nat)},
    ascendingRuns (first :: rest) = true → ∀ pair ∈ rest, first.1 < pair.1 ∨ first = pair
  | _, [], _ => by simp
  | first, second :: rest, valid => by
    simp only [ascendingRuns, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq] at valid
    obtain ⟨step, tail⟩ := valid
    have later := ascendingRuns_head tail
    intro pair member
    simp only [List.mem_cons] at member
    rcases member with same | member
    · subst same
      exact step
    · rcases step with less | same
      · rcases later pair member with further | equal
        · exact Or.inl (Nat.lt_trans less further)
        · subst equal
          exact Or.inl less
      · subst same
        exact later pair member

/-- In ascending runs, two pairs with the same first number are the same pair. -/
theorem ascendingRuns_unique : ∀ {pairs : List (Nat × Nat)}, ascendingRuns pairs = true →
    ∀ left ∈ pairs, ∀ right ∈ pairs, left.1 = right.1 → left = right
  | [], _ => by simp
  | first :: rest, valid => by
    have head := ascendingRuns_head valid
    have tail : ascendingRuns rest = true := by
      cases rest with
      | nil => rfl
      | cons second rest =>
        simp only [ascendingRuns, Bool.and_eq_true] at valid
        exact valid.2
    intro left leftMember right rightMember same
    simp only [List.mem_cons] at leftMember rightMember
    rcases leftMember with leftHead | leftMember <;>
      rcases rightMember with rightHead | rightMember
    · rw [leftHead, rightHead]
    · subst leftHead
      rcases head right rightMember with less | equal
      · omega
      · exact equal
    · subst rightHead
      rcases head left leftMember with less | equal
      · omega
      · exact equal.symm
    · exact ascendingRuns_unique tail left leftMember right rightMember same

/-- Whether no first number of the pairs comes with two second numbers. Sorted, the pairs must
    rise in their first number except where a pair repeats; a sort that failed to order them
    refuses them, so only the sort's keeping every pair is relied on. -/
def functional (pairs : List (Nat × Nat)) : Bool :=
  ascendingRuns (sortPairs pairs)

/-- Pairs that pass `functional` with the same first number have the same second number. -/
theorem functional_spec {pairs : List (Nat × Nat)} (valid : functional pairs = true) :
    ∀ left ∈ pairs, ∀ right ∈ pairs, left.1 = right.1 → left.2 = right.2 := by
  intro left leftMember right rightMember same
  have kept := sortBy_perm pairBefore pairs.length pairs
  rw [ascendingRuns_unique (pairs := sortPairs pairs) valid left (kept.mem_iff.mpr leftMember)
    right (kept.mem_iff.mpr rightMember) same]

/-- Whether the pairs relate identities and fields one to one: no identity comes with two fields
    and no field with two identities. Two sorts of the S pairs decide it in O(S log S)
    comparisons. -/
def oneToOne (pairs : List (Nat × Nat)) : Bool :=
  functional pairs && functional (pairs.map fun (identity, field) => (field, identity))

/-- Two pairs that pass `oneToOne` share an identity exactly when they share a field. -/
theorem oneToOne_spec {pairs : List (Nat × Nat)} (valid : oneToOne pairs = true) :
    ∀ left ∈ pairs, ∀ right ∈ pairs, (left.1 = right.1 ↔ left.2 = right.2) := by
  simp only [oneToOne, Bool.and_eq_true] at valid
  intro left leftMember right rightMember
  have swapped {pair : Nat × Nat} (member : pair ∈ pairs) :
      (pair.2, pair.1) ∈ pairs.map fun (identity, field) => (field, identity) :=
    List.mem_map.mpr ⟨pair, member, rfl⟩
  exact ⟨functional_spec valid.1 left leftMember right rightMember,
    functional_spec valid.2 _ (swapped leftMember) _ (swapped rightMember)⟩

#print axioms oneToOne_spec

/-- Over the whole program, two static sites share an identity exactly when their recorded tokens
    name one field, read through the body of each method's evidence. -/
abbrev StaticIdentitiesValid (program : Program) (bodies : List BodyEvidence) : Prop :=
  (programStaticPairs program bodies).any oneToOne = true

/-- A program that passes the check pairs its sites one to one with the fields they name. -/
theorem StaticIdentitiesValid.pairs {program : Program} {bodies : List BodyEvidence}
    (valid : StaticIdentitiesValid program bodies) :
    ∃ pairs, programStaticPairs program bodies = some pairs ∧
      ∀ left ∈ pairs, ∀ right ∈ pairs, (left.1 = right.1 ↔ left.2 = right.2) := by
  unfold StaticIdentitiesValid at valid
  cases found : programStaticPairs program bodies with
  | none => simp [found] at valid
  | some pairs =>
    rw [found] at valid
    exact ⟨pairs, rfl, oneToOne_spec (by simpa using valid)⟩

#print axioms StaticIdentitiesValid.pairs

end CIL.Extraction
