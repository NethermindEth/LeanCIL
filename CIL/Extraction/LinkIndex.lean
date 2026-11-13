import CIL.Extraction.FlowIndex
import CIL.Instructions

/-!
# Link lookups

Two forms keep a read of a method's link table from costing the table's length. The extractor
emits, per method with calls, a balanced index of the table's entries (call sites only) and one
equation checking that literal against the table, so a per-site fact reads its link in
logarithmic time. An embedding reads the link of every live instruction on each side; when the
table keys ascend and the queried pcs do not decrease, which holds for every extracted table and
every embedding whose pc map keeps the order of the blocks, one walk over the table answers all
queries. A hand-written table without ascending keys, or a map that reorders blocks, takes the
scan, which costs the table's length per query.
-/

namespace CIL.Extraction

/-- True when the keys increase strictly and none is below `lower`. -/
def linkKeysAscend : Nat → List (Nat × Link) → Bool
  | _, [] => true
  | lower, (key, _) :: rest => decide (lower ≤ key) && linkKeysAscend (key + 1) rest

/-- Ascending keys are all at least the lower bound. -/
theorem linkKeysAscend_bound (links : List (Nat × Link)) (lower : Nat)
    (ascending : linkKeysAscend lower links = true) : ∀ entry ∈ links, lower ≤ entry.1 := by
  induction links generalizing lower with
  | nil => simp
  | cons head rest ih =>
    simp only [linkKeysAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ascending.1
    · have := ih (head.1 + 1) ascending.2 entry member
      omega

#print axioms linkKeysAscend_bound

/-- The entry at a position of an ascending table is the first entry for its key. -/
theorem find_entry_of_ascending (links : List (Nat × Link)) (lower : Nat)
    (ascending : linkKeysAscend lower links = true) (position : Nat) (entry : Nat × Link)
    (found : links[position]? = some entry) :
    links.find? (fun candidate => candidate.1 == entry.1) = some entry := by
  induction links generalizing lower position with
  | nil => simp at found
  | cons head rest ih =>
    obtain ⟨key, link⟩ := head
    simp only [linkKeysAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending
    cases position with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact List.find?_cons_of_pos (Nat.beq_refl key)
    | succ position =>
      simp only [List.getElem?_cons_succ] at found
      have above := linkKeysAscend_bound rest (key + 1) ascending.2 entry
        (List.mem_of_getElem? found)
      have different : ¬ (key == entry.1) = true := by
        simp only [beq_iff_eq]
        omega
      have skip : (((key, link) :: rest).find? fun candidate => candidate.1 == entry.1) =
          rest.find? fun candidate => candidate.1 == entry.1 := List.find?_cons_of_neg different
      rw [skip]
      exact ih (key + 1) ascending.2 position found

#print axioms find_entry_of_ascending

/-- The literal `index` holds the entries of the ascending table `links`, in order. -/
def LinkIndexValid (links : List (Nat × Link)) (index : FlowIndex (Nat × Link)) : Prop :=
  linkKeysAscend 0 links = true ∧ index = FlowIndex.ofList links

instance (links : List (Nat × Link)) (index : FlowIndex (Nat × Link)) :
    Decidable (LinkIndexValid links index) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- An entry the index holds is the link the method's table gives for its pc. -/
theorem linkAt_of_entry {body : Method} {index : FlowIndex (Nat × Link)}
    (valid : LinkIndexValid body.links index) {position pc : Nat} {link : Link}
    (read : index.get? position = some (pc, link)) : body.linkAt pc = some link := by
  obtain ⟨ascending, rfl⟩ := valid
  rw [FlowIndex.get?_ofList] at read
  have first : body.links.find? (fun entry => entry.1 == pc) = some (pc, link) :=
    find_entry_of_ascending body.links 0 ascending position (pc, link) read
  simp only [Method.linkAt, linkLookup]
  rw [first]
  rfl

#print axioms linkAt_of_entry

/-- The entries from the first whose key is at least `query`. -/
def dropBelow (query : Nat) : List (Nat × Link) → List (Nat × Link)
  | [] => []
  | (key, link) :: rest => if key < query then dropBelow query rest else (key, link) :: rest

/-- One link per query, for ascending queries over an ascending table, in a single pass. -/
def linkWalk : List (Nat × Link) → List Nat → List (Option Link)
  | _, [] => []
  | table, query :: queries =>
    match dropBelow query table with
    | [] => none :: linkWalk [] queries
    | (key, link) :: rest =>
      (if key = query then some link else none) :: linkWalk ((key, link) :: rest) queries

/-- True when the queries do not decrease and none is below `lower`. -/
def queriesAscend : Nat → List Nat → Bool
  | _, [] => true
  | lower, query :: rest => decide (lower ≤ query) && queriesAscend query rest

/-- Ascending queries are all at least the lower bound. -/
theorem queriesAscend_bound (queries : List Nat) (lower : Nat)
    (ascending : queriesAscend lower queries = true) : ∀ query ∈ queries, lower ≤ query := by
  induction queries generalizing lower with
  | nil => simp
  | cons head rest ih =>
    simp only [queriesAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending
    intro query member
    rcases List.mem_cons.mp member with rfl | member
    · exact ascending.1
    · have := ih head ascending.2 query member
      omega

#print axioms queriesAscend_bound

/-- Entries below the query never match it or a later query. -/
theorem linkLookup_dropBelow (query : Nat) (table : List (Nat × Link)) (later : Nat)
    (after : query ≤ later) :
    linkLookup (dropBelow query table) later = linkLookup table later := by
  induction table with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, link⟩ := head
    by_cases below : key < query
    · have different : ¬ (key == later) = true := by
        simp only [beq_iff_eq]
        omega
      have skip : (((key, link) :: rest).find? fun entry => entry.1 == later) =
          rest.find? fun entry => entry.1 == later := List.find?_cons_of_neg different
      have step := ih
      simp only [dropBelow, below, ite_true, linkLookup, skip] at step ⊢
      exact step
    · simp [dropBelow, below]

#print axioms linkLookup_dropBelow

/-- Dropping the entries below a query keeps the table ascending from the query. -/
theorem dropBelow_ascend (query : Nat) (table : List (Nat × Link)) :
    ∀ lower, linkKeysAscend lower table = true →
      linkKeysAscend query (dropBelow query table) = true := by
  induction table with
  | nil => intro _ _; rfl
  | cons head rest ih =>
    obtain ⟨key, link⟩ := head
    intro lower ascending
    simp only [linkKeysAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending
    by_cases below : key < query
    · simp only [dropBelow, below, ite_true]
      exact ih (key + 1) ascending.2
    · simp only [dropBelow, below, ite_false, linkKeysAscend, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨by omega, ascending.2⟩

#print axioms dropBelow_ascend

/-- The walk reads each query as a scan of the table would. -/
theorem linkWalk_eq (queries : List Nat) : ∀ (table : List (Nat × Link)) (lower : Nat),
    linkKeysAscend lower table = true → queriesAscend lower queries = true →
      linkWalk table queries = queries.map (linkLookup table) := by
  induction queries with
  | nil => intros; rfl
  | cons query queries ih =>
    intro table lower tableAscends queriesAscends
    simp only [queriesAscend, Bool.and_eq_true, decide_eq_true_eq] at queriesAscends
    have rest_ascends := dropBelow_ascend query table lower tableAscends
    have later := queriesAscend_bound queries query queriesAscends.2
    have same : queries.map (linkLookup (dropBelow query table)) =
        queries.map (linkLookup table) :=
      List.map_congr_left fun later_query member =>
        linkLookup_dropBelow query table later_query (later later_query member)
    have head_same := linkLookup_dropBelow query table query (Nat.le_refl query)
    unfold linkWalk
    cases remaining : dropBelow query table with
    | nil =>
      rw [remaining] at rest_ascends head_same same
      have tail := ih [] query rfl queriesAscends.2
      refine congr (congrArg List.cons ?_) ?_
      · rw [← head_same]; rfl
      · rw [tail]; exact same
    | cons entry rest =>
      obtain ⟨key, link⟩ := entry
      rw [remaining] at rest_ascends head_same same
      have tail := ih ((key, link) :: rest) query rest_ascends queriesAscends.2
      have bounded : ∀ other ∈ rest, key + 1 ≤ other.1 := by
        simp only [linkKeysAscend, Bool.and_eq_true, decide_eq_true_eq] at rest_ascends
        exact linkKeysAscend_bound rest (key + 1) rest_ascends.2
      have at_least : query ≤ key := by
        simp only [linkKeysAscend, Bool.and_eq_true, decide_eq_true_eq] at rest_ascends
        exact rest_ascends.1
      refine congr (congrArg List.cons ?_) ?_
      · rw [← head_same]
        by_cases hit : key = query
        · subst hit
          have first : (((key, link) :: rest).find? fun entry => entry.1 == key) =
              some (key, link) := List.find?_cons_of_pos (Nat.beq_refl key)
          simp only [linkLookup, ite_true]
          rw [first]
          rfl
        · have different : ¬ (key == query) = true := by
            simp only [beq_iff_eq]
            exact hit
          have none_after : (rest.find? fun entry => entry.1 == query) = none := by
            rw [List.find?_eq_none]
            intro other member
            have := bounded other member
            simp only [beq_iff_eq]
            omega
          have skip : (((key, link) :: rest).find? fun entry => entry.1 == query) =
              rest.find? fun entry => entry.1 == query := List.find?_cons_of_neg different
          simp only [linkLookup, hit, ite_false]
          rw [skip, none_after]
          rfl
      · rw [tail]; exact same

#print axioms linkWalk_eq

/-- The links an embedding reads for the queries: the walk when the table keys ascend and the
    queries do not decrease, the scan otherwise. -/
def linkReads (links : List (Nat × Link)) (queries : List Nat) : List (Option Link) :=
  if linkKeysAscend 0 links && queriesAscend 0 queries then linkWalk links queries
  else queries.map (linkLookup links)

/-- However the table and queries are ordered, the reads are the scans' answers. -/
theorem linkReads_eq (links : List (Nat × Link)) (queries : List Nat) :
    linkReads links queries = queries.map (linkLookup links) := by
  unfold linkReads
  split
  · rename_i ordered
    simp only [Bool.and_eq_true] at ordered
    exact linkWalk_eq queries links 0 ordered.1 ordered.2
  · rfl

#print axioms linkReads_eq

end CIL.Extraction
