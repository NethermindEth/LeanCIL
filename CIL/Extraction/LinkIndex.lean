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
query. The extraction call check reads each pc's link by the walk; a table with ascending keys at
pcs of the code is the one the code implies exactly when every pc reads its instruction's link
(`eq_linksOfCode_iff`).
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

/-- Lowering the bound keeps the keys ascending. -/
theorem keysAscend_lower {α : Type} (entries : List (Nat × α)) {lower higher : Nat}
    (below : lower ≤ higher) (ascending : keysAscend higher entries = true) :
    keysAscend lower entries = true := by
  refine keysAscend_raise ascending ?_
  cases entries with
  | nil => rfl
  | cons head rest =>
    have := keysAscend_bound _ higher ascending head (List.mem_cons_self ..)
    simp only [List.head?_cons, Option.all_some, decide_eq_true_eq]
    omega

#print axioms keysAscend_lower

/-- The first entry of a table gives its own key its link. -/
theorem linkLookup_cons_self (key : Nat) (link : Link) (rest : List (Nat × Link)) :
    linkLookup ((key, link) :: rest) key = some link := by
  simp [linkLookup]

#print axioms linkLookup_cons_self

/-- A query other than the first key reads the rest of the table. -/
theorem linkLookup_cons_ne {key query : Nat} (link : Link) (rest : List (Nat × Link))
    (different : key ≠ query) :
    linkLookup ((key, link) :: rest) query = linkLookup rest query := by
  simp [linkLookup, different]

#print axioms linkLookup_cons_ne

/-- No pc below the bound of an ascending table has a link. -/
theorem linkLookup_below {links : List (Nat × Link)} {lower query : Nat}
    (ascending : keysAscend lower links = true) (below : query < lower) :
    linkLookup links query = none :=
  linkLookup_of_unlisted fun entry member => by
    have := keysAscend_bound links lower ascending entry member
    omega

#print axioms linkLookup_below

/-- Two tables whose keys ascend from one bound and that give every pc the same link are the same
    table. -/
theorem eq_of_linkLookup {first second : List (Nat × Link)} {lower : Nat}
    (firstAscends : keysAscend lower first = true) (secondAscends : keysAscend lower second = true)
    (same : ∀ query, linkLookup first query = linkLookup second query) : first = second := by
  induction first generalizing second lower with
  | nil =>
    cases second with
    | nil => rfl
    | cons head rest =>
      obtain ⟨key, link⟩ := head
      have := same key
      rw [linkLookup_cons_self] at this
      simp [linkLookup] at this
  | cons head rest ih =>
    obtain ⟨key, link⟩ := head
    cases second with
    | nil =>
      have := same key
      rw [linkLookup_cons_self] at this
      simp [linkLookup] at this
    | cons other others =>
      obtain ⟨otherKey, otherLink⟩ := other
      simp only [keysAscend, Bool.and_eq_true, decide_eq_true_eq] at firstAscends secondAscends
      have keys : key = otherKey := by
        rcases Nat.lt_trichotomy key otherKey with smaller | equal | larger
        · have read := same key
          rw [linkLookup_cons_self, linkLookup_cons_ne _ _ (Nat.ne_of_gt smaller),
            linkLookup_below secondAscends.2 (by omega)] at read
          cases read
        · exact equal
        · have read := same otherKey
          rw [linkLookup_cons_self, linkLookup_cons_ne _ _ (Nat.ne_of_gt larger),
            linkLookup_below firstAscends.2 (by omega)] at read
          cases read
      subst keys
      have links : link = otherLink := by
        have read := same key
        rw [linkLookup_cons_self, linkLookup_cons_self] at read
        exact Option.some.inj read
      subst links
      congr 1
      refine ih firstAscends.2 secondAscends.2 fun query => ?_
      by_cases at_key : key = query
      · subst at_key
        rw [linkLookup_below firstAscends.2 (Nat.lt_succ_self _),
          linkLookup_below secondAscends.2 (Nat.lt_succ_self _)]
      · have read := same query
        rwa [linkLookup_cons_ne _ _ at_key, linkLookup_cons_ne _ _ at_key] at read

#print axioms eq_of_linkLookup

/-- The table implied by code that starts at pc `start` has keys ascending from `start`. -/
theorem keysAscend_implied (code : List Instruction) (start : Nat) :
    keysAscend start ((code.zipIdx start).filterMap fun entry =>
      entry.1.link?.map fun link => (entry.2, link)) = true := by
  induction code generalizing start with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.zipIdx_cons, List.filterMap_cons]
    cases op.link? with
    | none => exact keysAscend_lower _ (Nat.le_succ start) (ih (start + 1))
    | some link =>
      simp only [Option.map_some, keysAscend, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Nat.le_refl _, ih (start + 1)⟩

#print axioms keysAscend_implied

/-- The keys of the table a code list implies ascend. -/
theorem keysAscend_linksOfCode (code : List Instruction) :
    keysAscend 0 (linksOfCode code) = true := by
  rw [linksOfCode_eq_zipIdx]
  exact keysAscend_implied code 0

#print axioms keysAscend_linksOfCode

/-- Every key of the table a code list implies is a pc of that code. -/
theorem linksOfCode_keys (code : List Instruction) :
    (linksOfCode code).all (fun entry => decide (entry.1 < code.length)) = true := by
  rw [List.all_eq_true]
  intro entry member
  simp only [linksOfCode, List.mem_filterMap] at member
  obtain ⟨⟨op, pc⟩, inZip, implied⟩ := member
  have := List.mem_range.mp (List.of_mem_zip inZip).2
  cases found : op.link? with
  | none => simp [found] at implied
  | some link =>
    simp only [found, Option.map_some, Option.some.injEq] at implied
    subst implied
    simpa using this

#print axioms linksOfCode_keys

/-- A table whose keys ascend and are pcs of `code` is the table `code` implies exactly when it
    gives each pc of `code` the link of the instruction there. -/
theorem eq_linksOfCode_iff (links : List (Nat × Link)) (code : List Instruction)
    (ascending : keysAscend 0 links = true)
    (bounded : links.all (fun entry => decide (entry.1 < code.length)) = true) :
    (List.range code.length).map (linkLookup links) = code.map Instruction.link? ↔
      links = linksOfCode code := by
  constructor
  · intro reads
    refine eq_of_linkLookup ascending (keysAscend_linksOfCode code) fun query => ?_
    rw [linkLookup_linksOfCode]
    by_cases inside : query < code.length
    · have read := congrArg (·[query]?) reads
      simp only [List.getElem?_map, List.getElem?_range inside, Option.map_some] at read
      rw [List.getElem?_eq_getElem inside] at read ⊢
      simpa using read
    · rw [List.getElem?_eq_none (by omega)]
      exact linkLookup_of_unlisted fun entry member => by
        have := of_decide_eq_true (List.all_eq_true.mp bounded entry member)
        omega
  · intro implied
    subst implied
    apply List.ext_getElem (by simp)
    intro index _ inCode
    simp only [List.getElem_map, List.getElem_range]
    rw [linkLookup_linksOfCode, List.getElem?_eq_getElem (by simpa using inCode)]
    rfl

#print axioms eq_linksOfCode_iff

/-- A lockstep check that reads a link per pc beside the code, and first compares that link with
    the one the instruction implies, passes exactly when every read is that link and the check
    passes with the implied links. -/
theorem all3_reads_iff {α β : Type} (check : α → β → Option Link → Instruction → Bool)
    (compares : ∀ first second link op,
      check first second link op = (link == op.link? && check first second op.link? op))
    (reads : Nat → Option Link) (start : Nat) (raw : List α) :
    ∀ (states : List β) (code : List Instruction),
      raw.length = states.length → raw.length = code.length →
      (all3 (fun first (second, link) op => check first second link op) raw
          (states.zip ((List.range' start code.length).map reads)) code = true ↔
        (List.range' start code.length).map reads = code.map Instruction.link? ∧
          all3 (fun first second op => check first second op.link? op) raw states code = true) :=
    by
  induction raw generalizing start with
  | nil =>
    intro states code statesLength codeLength
    have noStates : states = [] := List.length_eq_zero_iff.mp statesLength.symm
    have noCode : code = [] := List.length_eq_zero_iff.mp codeLength.symm
    subst noStates noCode
    simp [all3]
  | cons first raw ih =>
    intro states code statesLength codeLength
    cases states with
    | nil => simp at statesLength
    | cons second states =>
      cases code with
      | nil => simp at codeLength
      | cons op code =>
        have tail := ih (start + 1) states code (by simpa using statesLength)
          (by simpa using codeLength)
        simp only [List.length_cons, List.range'_succ, List.map_cons, List.zip_cons_cons, all3,
          Bool.and_eq_true, List.cons.injEq]
        rw [compares first second (reads start) op, Bool.and_eq_true, beq_iff_eq, tail]
        constructor
        · rintro ⟨⟨same, valid⟩, implied, rest⟩
          exact ⟨⟨same, implied⟩, valid, rest⟩
        · rintro ⟨⟨same, implied⟩, valid, rest⟩
          exact ⟨⟨same, valid⟩, implied, rest⟩

#print axioms all3_reads_iff

end CIL.Extraction
