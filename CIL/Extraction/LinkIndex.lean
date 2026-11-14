import CIL.Extraction.FlowIndex
import CIL.Instructions

/-!
# Link lookups

Two forms keep a read of a method's link table from costing the table's length. The extractor
emits, per method with calls, a balanced index of the table's entries (call sites only) and one
equation checking that literal against the table, so a per-site fact reads its link in
logarithmic time. An embedding reads the link of every live instruction on each side; when the
table keys ascend, which holds for every extracted table and every table `linksOfCode` builds, a
walk over the table answers all queries. The walk advances while the queried pcs do not
decrease and starts again from the head of the table at each pc below the one before, so a map
that reorders a few blocks costs a few passes. A hand-written table without ascending keys takes
the scan, which costs the table's length per query.
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

/-- The link the first entry gives `query`: its link when its key is `query`, else none. -/
def readHead (query : Nat) : List (Nat × Link) → Option Link
  | [] => none
  | (key, link) :: _ => if key = query then some link else none

/-- One link per query over `full`, whose keys ascend. `table` is `full` from the entry the
    previous query stopped at; a query below the previous one starts again from the head of
    `full`. The queries cost one step each and `full`'s length once per such descent. -/
def linkWalk (full : List (Nat × Link)) :
    List (Nat × Link) → Nat → List Nat → List (Option Link)
  | _, _, [] => []
  | table, previous, query :: queries =>
    let remaining := dropBelow query (if query < previous then full else table)
    readHead query remaining :: linkWalk full remaining query queries

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

/-- Dropping below a query what is left after dropping below an earlier one drops below the
    query. -/
theorem dropBelow_dropBelow (earlier query : Nat) (table : List (Nat × Link))
    (after : earlier ≤ query) :
    dropBelow query (dropBelow earlier table) = dropBelow query table := by
  induction table with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, link⟩ := head
    by_cases below : key < earlier
    · simp only [dropBelow, below, ite_true, show key < query by omega]
      exact ih
    · simp only [dropBelow, below, ite_false]

#print axioms dropBelow_dropBelow

/-- No key is below zero, so dropping below zero keeps the table. -/
theorem dropBelow_zero (table : List (Nat × Link)) : dropBelow 0 table = table := by
  cases table with
  | nil => rfl
  | cons head rest =>
    obtain ⟨key, link⟩ := head
    simp [dropBelow]

#print axioms dropBelow_zero

/-- Over an ascending table, the first entry left after dropping below a query answers it as a
    scan of the table would. -/
theorem readHead_dropBelow (query : Nat) (table : List (Nat × Link)) (lower : Nat)
    (ascending : linkKeysAscend lower table = true) :
    readHead query (dropBelow query table) = linkLookup table query := by
  rw [← linkLookup_dropBelow query table query (Nat.le_refl query)]
  have rest_ascends := dropBelow_ascend query table lower ascending
  cases remaining : dropBelow query table with
  | nil => rfl
  | cons entry rest =>
    obtain ⟨key, link⟩ := entry
    rw [remaining] at rest_ascends
    simp only [linkKeysAscend, Bool.and_eq_true, decide_eq_true_eq] at rest_ascends
    have bounded := linkKeysAscend_bound rest (key + 1) rest_ascends.2
    by_cases hit : key = query
    · subst hit
      have first : (((key, link) :: rest).find? fun entry => entry.1 == key) =
          some (key, link) := List.find?_cons_of_pos (Nat.beq_refl key)
      simp only [readHead, linkLookup, ite_true]
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
      simp only [readHead, linkLookup, hit, ite_false]
      rw [skip, none_after]
      rfl

#print axioms readHead_dropBelow

/-- While `table` is what is left of an ascending `full` after dropping below `previous`, the
    walk reads each query as a scan of `full` would, in whatever order the queries come. -/
theorem linkWalk_eq (full : List (Nat × Link)) (ascending : linkKeysAscend 0 full = true)
    (queries : List Nat) : ∀ (table : List (Nat × Link)) (previous : Nat),
      table = dropBelow previous full →
        linkWalk full table previous queries = queries.map (linkLookup full) := by
  induction queries with
  | nil => intros; rfl
  | cons query queries ih =>
    intro table previous suffix
    have restarted : dropBelow query (if query < previous then full else table) =
        dropBelow query full := by
      split
      · rfl
      · rw [suffix]
        exact dropBelow_dropBelow previous query full (by omega)
    simp only [linkWalk, List.map_cons, restarted]
    rw [readHead_dropBelow query full 0 ascending, ih (dropBelow query full) query rfl]

#print axioms linkWalk_eq

/-- The links an embedding reads for the queries: the walk when the table keys ascend, the scan
    otherwise. -/
def linkReads (links : List (Nat × Link)) (queries : List Nat) : List (Option Link) :=
  if linkKeysAscend 0 links then linkWalk links links 0 queries
  else queries.map (linkLookup links)

/-- However the table and queries are ordered, the reads are the scans' answers. -/
theorem linkReads_eq (links : List (Nat × Link)) (queries : List Nat) :
    linkReads links queries = queries.map (linkLookup links) := by
  unfold linkReads
  split
  · rename_i ascending
    exact linkWalk_eq links ascending queries links 0 (dropBelow_zero links).symm
  · rfl

#print axioms linkReads_eq

end CIL.Extraction
