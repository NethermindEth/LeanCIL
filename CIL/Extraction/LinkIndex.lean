import CIL.Extraction.FlowIndex
import CIL.Instructions

/-!
# Link lookups

Two forms keep a read of a method's link table from costing the table's length. For a table
whose keys ascend, the entry at a position is the first for its key (`linkAt_of_position`), so
`cil_instruction_equations` proves each call site's link from its entry, read through named
suffixes of the table, after checking once that the keys ascend. An embedding reads the link of
every live instruction on each side; when the table keys ascend, which holds for every extracted
table and every table `linksOfCode` builds, a walk over the table answers all queries. The walk
advances while the queried pcs do not decrease and starts again from the head of the table at
each pc below the one before, so a map that reorders a few blocks costs a few passes. A
hand-written table without ascending keys takes the scan, which costs the table's length per
query. The extraction call check reads each pc's link by the walk, and `linkIndex` indexes the
walk once for checks that ask a pc's link out of order.
-/

namespace CIL.Extraction

/-- True when the keys increase strictly and none is below `lower`. -/
def keysAscend {α : Type} : Nat → List (Nat × α) → Bool
  | _, [] => true
  | lower, (key, _) :: rest => decide (lower ≤ key) && keysAscend (key + 1) rest

/-- Ascending keys are all at least the lower bound. -/
theorem keysAscend_bound {α : Type} (entries : List (Nat × α)) (lower : Nat)
    (ascending : keysAscend lower entries = true) : ∀ entry ∈ entries, lower ≤ entry.1 := by
  induction entries generalizing lower with
  | nil => simp
  | cons head rest ih =>
    simp only [keysAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ascending.1
    · have := ih (head.1 + 1) ascending.2 entry member
      omega

#print axioms keysAscend_bound

/-- A table ascending from `lower` ascends from any bound its first key reaches. -/
theorem keysAscend_raise {α : Type} {entries : List (Nat × α)} {lower higher : Nat}
    (ascending : keysAscend lower entries = true)
    (raised : (entries.head?.all fun entry => decide (higher ≤ entry.1)) = true) :
    keysAscend higher entries = true := by
  cases entries with
  | nil => rfl
  | cons head rest =>
    obtain ⟨key, value⟩ := head
    simp only [keysAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending ⊢
    simp only [List.head?_cons, Option.all_some, decide_eq_true_eq] at raised
    exact ⟨raised, ascending.2⟩

#print axioms keysAscend_raise

/-- The entry at a position of an ascending table is the first entry for its key. -/
theorem find_entry_of_ascending (links : List (Nat × Link)) (lower : Nat)
    (ascending : keysAscend lower links = true) (position : Nat) (entry : Nat × Link)
    (found : links[position]? = some entry) :
    links.find? (fun candidate => candidate.1 == entry.1) = some entry := by
  induction links generalizing lower position with
  | nil => simp at found
  | cons head rest ih =>
    obtain ⟨key, link⟩ := head
    simp only [keysAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending
    cases position with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact List.find?_cons_of_pos (Nat.beq_refl key)
    | succ position =>
      simp only [List.getElem?_cons_succ] at found
      have above := keysAscend_bound rest (key + 1) ascending.2 entry
        (List.mem_of_getElem? found)
      have different : ¬ (key == entry.1) = true := by
        simp only [beq_iff_eq]
        omega
      have skip : (((key, link) :: rest).find? fun candidate => candidate.1 == entry.1) =
          rest.find? fun candidate => candidate.1 == entry.1 := List.find?_cons_of_neg different
      rw [skip]
      exact ih (key + 1) ascending.2 position found

#print axioms find_entry_of_ascending

/-- An entry of a table whose keys ascend is the link the method gives its pc. -/
theorem linkAt_of_position {body : Method} (ascending : keysAscend 0 body.links = true)
    {position pc : Nat} {link : Link} (found : body.links[position]? = some (pc, link)) :
    body.linkAt pc = some link := by
  have first : body.links.find? (fun entry => entry.1 == pc) = some (pc, link) :=
    find_entry_of_ascending body.links 0 ascending position (pc, link) found
  simp only [Method.linkAt, linkLookup]
  rw [first]
  rfl

#print axioms linkAt_of_position

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
    ∀ lower, keysAscend lower table = true →
      keysAscend query (dropBelow query table) = true := by
  induction table with
  | nil => intro _ _; rfl
  | cons head rest ih =>
    obtain ⟨key, link⟩ := head
    intro lower ascending
    simp only [keysAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending
    by_cases below : key < query
    · simp only [dropBelow, below, ite_true]
      exact ih (key + 1) ascending.2
    · simp only [dropBelow, below, ite_false, keysAscend, Bool.and_eq_true,
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
    (ascending : keysAscend lower table = true) :
    readHead query (dropBelow query table) = linkLookup table query := by
  rw [← linkLookup_dropBelow query table query (Nat.le_refl query)]
  have rest_ascends := dropBelow_ascend query table lower ascending
  cases remaining : dropBelow query table with
  | nil => rfl
  | cons entry rest =>
    obtain ⟨key, link⟩ := entry
    rw [remaining] at rest_ascends
    simp only [keysAscend, Bool.and_eq_true, decide_eq_true_eq] at rest_ascends
    have bounded := keysAscend_bound rest (key + 1) rest_ascends.2
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

/-- In a table ascending from `lower`, every entry up to position `last` has a key at most that
    entry's. -/
theorem keysAscend_take_le {α : Type} : ∀ (entries : List (Nat × α)) (lower last : Nat)
    (bound : Nat × α), keysAscend lower entries = true → entries[last]? = some bound →
      ∀ entry ∈ entries.take (last + 1), entry.1 ≤ bound.1
  | [], _, _, _, _, found => by simp at found
  | (key, value) :: rest, lower, last, bound, ascending, found => by
    simp only [keysAscend, Bool.and_eq_true, decide_eq_true_eq] at ascending
    cases last with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simp
    | succ last =>
      simp only [List.getElem?_cons_succ] at found
      have later := keysAscend_bound rest (key + 1) ascending.2 bound (List.mem_of_getElem? found)
      intro entry member
      simp only [List.take_succ_cons, List.mem_cons] at member
      rcases member with rfl | member
      · simp only
        omega
      · exact keysAscend_take_le rest (key + 1) last bound ascending.2 found entry member

#print axioms keysAscend_take_le

/-- What is left of an ascending table after any prefix ascends from some bound. -/
theorem keysAscend_drop {α : Type} : ∀ (entries : List (Nat × α)) (lower count : Nat),
    keysAscend lower entries = true → ∃ bound, keysAscend bound (entries.drop count) = true
  | [], _, _, _ => ⟨0, by simp [keysAscend]⟩
  | _ :: _, lower, 0, ascending => ⟨lower, ascending⟩
  | (key, _) :: rest, _, count + 1, ascending => by
    simp only [keysAscend, Bool.and_eq_true] at ascending
    exact keysAscend_drop rest (key + 1) count ascending.2

#print axioms keysAscend_drop

/-- Over an ascending table, the link of `query` is read from the head of the table, so a pc
    before its first block needs no other entry. -/
theorem linkAt_eq_readHead {body : Method} (ascending : keysAscend 0 body.links = true)
    (query : Nat) : body.linkAt query = readHead query (dropBelow query body.links) :=
  (readHead_dropBelow query body.links 0 ascending).symm

#print axioms linkAt_eq_readHead

/-- Over an ascending table, when the entry at `previous` has a key below `query`, the link of
    `query` is read from `suffix`, the table after that entry, so it walks no earlier entry. -/
theorem linkAt_eq_readHead_suffix {body : Method} (ascending : keysAscend 0 body.links = true)
    {previous query : Nat} {last : Nat × Link} {suffix : List (Nat × Link)}
    (placed : body.links.drop (previous + 1) = suffix) (found : body.links[previous]? = some last)
    (below : last.1 < query) : body.linkAt query = readHead query (dropBelow query suffix) := by
  obtain ⟨bound, rest⟩ := keysAscend_drop body.links 0 (previous + 1) ascending
  rw [placed] at rest
  rw [readHead_dropBelow query suffix bound rest, Method.linkAt, ← placed]
  have earlier := keysAscend_take_le body.links 0 previous last ascending found
  conv => lhs; rw [← List.take_append_drop (previous + 1) body.links]
  simp only [linkLookup, List.find?_append]
  rw [show (List.take (previous + 1) body.links).find? (fun entry => entry.1 == query) = none from
    List.find?_eq_none.mpr fun entry member => by
      have := earlier entry member
      simp only [beq_iff_eq]
      omega]
  rfl

#print axioms linkAt_eq_readHead_suffix

/-- While `table` is what is left of an ascending `full` after dropping below `previous`, the
    walk reads each query as a scan of `full` would, in whatever order the queries come. -/
theorem linkWalk_eq (full : List (Nat × Link)) (ascending : keysAscend 0 full = true)
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
  if keysAscend 0 links then linkWalk links links 0 queries
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

/-- The link of each pc of `body`'s code, read by one walk over the table and indexed once, so
    a check that asks every pc pays the table and the code once and a logarithm per query; a pc
    past the code takes the scan. -/
def linkIndex (body : Method) (pc : Nat) : Option Link :=
  match (FlowIndex.ofList (linkReads body.links (List.range body.code.length))).get? pc with
  | some link => link
  | none => body.linkAt pc

/-- The index gives every pc the link a scan of the table gives it. -/
theorem linkIndex_eq (body : Method) : linkIndex body = body.linkAt := by
  funext pc
  rw [linkIndex, FlowIndex.get?_ofList, linkReads_eq]
  by_cases inside : pc < body.code.length <;> simp [inside, Method.linkAt]

#print axioms linkIndex_eq

end CIL.Extraction
