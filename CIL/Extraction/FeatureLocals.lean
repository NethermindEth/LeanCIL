import CIL.Extraction.Generics
import CIL.Extraction.FlowIndex
import CIL.Extraction.Folds
import Std.Data.TreeSet.Lemmas

/-!
# Feature local facts

Indexed local eligibility for feature facts, equivalent to scanning raw metadata, and the
known-fact lists that certificate states keep for locals: the facts known at a pc as
(local index, word) pairs in strictly increasing index order. `expandKnown` gives the full
per-local list such a list stands for, and the lemmas here relate reads, stores, weakening and
eligibility on the two forms.
-/

namespace CIL.Extraction

/-- The local whose address an instruction takes, including both `ldloca` encodings. -/
private def addressedLocal (instruction : RawInstruction) : Option Nat :=
  if instruction.opcode == 18 || instruction.opcode == 65037 then localIndex instruction
  else none

/-- Word locals admit every fact; boolean locals admit only zero or one. -/
inductive FeatureLocalKind where
  | unknown
  | word
  | boolean

/-- Classify the exact runtime identity, rejecting every unsupported or malformed type. -/
def FeatureLocalKind.ofType : TypeExpr → FeatureLocalKind
  | .atom scope name =>
    if scope != runtimeScope then .unknown
    else if name == "System.Int32" || name == "System.UInt32" then .word
    else if name == "System.Boolean" then .boolean else .unknown
  | _ => .unknown

/-- A known fact must respect the local's admitted runtime representation. -/
def FeatureLocalKind.accepts (kind : FeatureLocalKind) (fact : Option W32) : Bool :=
  match kind with
  | .unknown => false
  | .word => true
  | .boolean => fact == some 0 || fact == some 1

/-- The original local rule, independent of any precomputed index. A method with exception
    clauses keeps no local fact, since a handler or a resumed `leave` would otherwise need the
    facts of every pc that reaches it. -/
def featureLocalEligible (raw : RawMethod) (index : Nat) (fact : Option W32) : Bool :=
  if fact.isNone then true
  else if !raw.handlers.isEmpty then false
  else if raw.code.any (fun instruction =>
    (instruction.opcode == 18 || instruction.opcode == 65037) &&
      localIndex instruction == some index) then false
  else match raw.locals[index]? with
    | some (.atom scope name) => scope == runtimeScope &&
        (name == "System.Int32" || name == "System.UInt32" ||
          name == "System.Boolean" && (fact == some 0 || fact == some 1))
    | _ => false

/-- Address exclusions and exact type classifications shared by every certificate state. -/
structure FeatureLocalIndex where
  /-- The method has exception clauses, so no local holds a fact. -/
  guarded : Bool
  addressed : Std.TreeSet Nat
  kinds : FlowIndex FeatureLocalKind

/-- Classify each raw local once and collect addressed slots in one instruction traversal. -/
def FeatureLocalIndex.ofRaw (raw : RawMethod) : FeatureLocalIndex :=
  ⟨!raw.handlers.isEmpty, Std.TreeSet.ofList (raw.code.filterMap addressedLocal),
    FlowIndex.ofList (raw.locals.map FeatureLocalKind.ofType)⟩

/-- Unknown facts remain admissible, including missing or addressed locals. -/
def FeatureLocalIndex.eligible (locals : FeatureLocalIndex) (index : Nat)
    (fact : Option W32) : Bool :=
  if fact.isNone then true else if locals.guarded || locals.addressed.contains index then false
  else ((locals.kinds.get? index).getD .unknown).accepts fact

/-- Collecting addressed slots preserves the raw opcode and local-index checks exactly. -/
private theorem addressedLocal_contains (code : List RawInstruction) (index : Nat) :
    (code.filterMap addressedLocal).contains index = code.any (fun instruction =>
      (instruction.opcode == 18 || instruction.opcode == 65037) &&
        localIndex instruction == some index) := by
  apply Bool.eq_iff_iff.mpr
  simp [List.mem_filterMap, addressedLocal, List.any_eq_true]

#print axioms addressedLocal_contains

/-- Indexed lookup preserves the original rule for every index, type, address and fact. -/
theorem FeatureLocalIndex.eligible_eq (raw : RawMethod) (index : Nat) (fact : Option W32) :
    (FeatureLocalIndex.ofRaw raw).eligible index fact = featureLocalEligible raw index fact := by
  simp only [FeatureLocalIndex.eligible, FeatureLocalIndex.ofRaw,
    Std.TreeSet.contains_ofList, addressedLocal_contains, FlowIndex.get?_ofList,
    List.getElem?_map, featureLocalEligible]
  split <;> rename_i unknown
  · rfl
  by_cases guarded : raw.handlers.isEmpty
  case neg => simp [guarded]
  simp only [guarded, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  split <;> rename_i addressed
  · rfl
  cases found : raw.locals[index]? with
  | none => rfl
  | some type =>
    cases type <;> try rfl
    rename_i scope name
    by_cases scopeValid : scope = runtimeScope
    · by_cases word : name = "System.Int32" ∨ name = "System.UInt32"
      · rcases word with word | word <;>
          simp [FeatureLocalKind.ofType, FeatureLocalKind.accepts, scopeValid, word]
      · simp only [not_or] at word
        by_cases boolean : name = "System.Boolean" <;>
          simp [FeatureLocalKind.ofType, FeatureLocalKind.accepts, scopeValid, word, boolean]
    · simp [FeatureLocalKind.ofType, FeatureLocalKind.accepts, scopeValid]

#print axioms FeatureLocalIndex.eligible_eq

/-- `target` is no more precise than `source`. -/
def factWeakens (source target : Option W32) : Bool := target.isNone || source == target

/-- Pointwise `factWeakens` over lists of equal length. -/
def factsWeaken (source target : List (Option W32)) : Bool :=
  source.length == target.length && (source.zip target).all fun (a, b) => factWeakens a b

/-- Known local facts in strictly increasing local index order, each index at least `next` and
    below `count`. -/
def knownBelow (count : Nat) : Nat → List (Nat × W32) → Bool
  | _, [] => true
  | next, (index, _) :: rest => next ≤ index && index < count && knownBelow count (index + 1) rest

/-- Record a fact for local `index` in an increasing known-fact list: its entry is replaced,
    inserted in order, or removed when the fact is unknown. -/
def storeKnown (index : Nat) (fact : Option W32) : List (Nat × W32) → List (Nat × W32)
  | [] => match fact with | some word => [(index, word)] | none => []
  | (other, word) :: rest =>
    if other < index then (other, word) :: storeKnown index fact rest
    else
      let later := if other = index then rest else (other, word) :: rest
      match fact with | some value => (index, value) :: later | none => later

/-- The full per-local list over `count` locals that a known-fact list stands for. -/
def expandKnown (count : Nat) (locals : List (Nat × W32)) : List (Option W32) :=
  (List.range count).map fun index => locals.lookup index

/-- The known facts of a full per-local list whose first entry is the local the first argument
    numbers. -/
def compressKnown : Nat → List (Option W32) → List (Nat × W32)
  | _, [] => []
  | index, none :: rest => compressKnown (index + 1) rest
  | index, some word :: rest => (index, word) :: compressKnown (index + 1) rest

/-- An entry heads a known-fact list exactly when it is in range and the rest follows it. -/
theorem knownBelow_cons {count next index : Nat} {word : W32} {rest : List (Nat × W32)} :
    knownBelow count next ((index, word) :: rest) = true ↔
      next ≤ index ∧ index < count ∧ knownBelow count (index + 1) rest = true := by
  simp [knownBelow, Bool.and_eq_true, and_assoc]
#print axioms knownBelow_cons

/-- A lower starting bound admits every list a higher one admits. -/
theorem knownBelow_mono {count next lower : Nat} {locals : List (Nat × W32)}
    (known : knownBelow count next locals = true) (below : lower ≤ next) :
    knownBelow count lower locals = true := by
  cases locals with
  | nil => rfl
  | cons entry rest =>
    obtain ⟨index, word⟩ := entry
    rw [knownBelow_cons] at known ⊢
    exact ⟨Nat.le_trans below known.1, known.2⟩
#print axioms knownBelow_mono

/-- Every entry of a known-fact list lies between its bounds. -/
theorem knownBelow_mem {count next : Nat} {locals : List (Nat × W32)}
    (known : knownBelow count next locals = true) {entry : Nat × W32} (member : entry ∈ locals) :
    next ≤ entry.1 ∧ entry.1 < count := by
  induction locals generalizing next with
  | nil => simp at member
  | cons head rest ih =>
    obtain ⟨index, word⟩ := head
    rw [knownBelow_cons] at known
    rcases List.mem_cons.mp member with same | later
    · subst same
      exact ⟨known.1, known.2.1⟩
    · have bounds := ih known.2.2 later
      exact ⟨by omega, bounds.2⟩
#print axioms knownBelow_mem

/-- A known-fact list has no fact for an index outside its bounds. -/
theorem knownBelow_lookup_none {count next : Nat} {locals : List (Nat × W32)}
    (known : knownBelow count next locals = true) {key : Nat}
    (outside : key < next ∨ count ≤ key) :
    locals.lookup key = none := by
  rw [List.lookup_eq_none_iff]
  intro entry member
  have bounds := knownBelow_mem known member
  simp only [bne_iff_ne, ne_eq]
  omega
#print axioms knownBelow_lookup_none

/-- In a known-fact list an entry is present exactly when lookup finds its word. -/
theorem knownBelow_mem_iff {count next : Nat} {locals : List (Nat × W32)}
    (known : knownBelow count next locals = true) {key : Nat} {word : W32} :
    (key, word) ∈ locals ↔ locals.lookup key = some word := by
  induction locals generalizing next with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨index, value⟩ := head
    rw [knownBelow_cons] at known
    by_cases same : key = index
    · subst same
      have absent : (key, word) ∉ rest := fun member => by
        have := (knownBelow_mem known.2.2 member).1
        simp only at this
        omega
      simp [absent, eq_comm]
    · have differs : (key == index) = false := by simpa using same
      simp [List.lookup_cons, differs, same, ih known.2.2]
#print axioms knownBelow_mem_iff

/-- Storing keeps the list increasing and in range, and changes the fact of one local only. -/
theorem storeKnown_spec {count next index : Nat} {fact : Option W32} {locals : List (Nat × W32)}
    (known : knownBelow count next locals = true) (low : next ≤ index) (high : index < count) :
    knownBelow count next (storeKnown index fact locals) = true ∧
      ∀ key, (storeKnown index fact locals).lookup key =
        if key = index then fact else locals.lookup key := by
  induction locals generalizing next with
  | nil =>
    cases fact with
    | none => simp [storeKnown, knownBelow]
    | some word =>
      refine ⟨by simp [storeKnown, knownBelow, low, high], fun key => ?_⟩
      by_cases same : key = index
      · simp [storeKnown, same]
      · have differs : (key == index) = false := by simpa using same
        simp [storeKnown, List.lookup_cons, differs, same]
  | cons head rest ih =>
    obtain ⟨other, word⟩ := head
    obtain ⟨otherLow, otherHigh, tail⟩ := knownBelow_cons.mp known
    by_cases before : other < index
    · have inner := ih tail (by omega)
      simp only [storeKnown, before, ↓reduceIte]
      refine ⟨knownBelow_cons.mpr ⟨otherLow, otherHigh, inner.1⟩, fun key => ?_⟩
      by_cases same : key = other
      · subst same
        have differs : key ≠ index := by omega
        simp [differs]
      · have differs : (key == other) = false := by simpa using same
        simp only [List.lookup_cons, differs, inner.2]
    · by_cases equal : other = index
      · subst equal
        have absent : rest.lookup other = none := knownBelow_lookup_none tail (by omega)
        cases fact with
        | none =>
          simp only [storeKnown, before, ↓reduceIte, ↓reduceIte]
          refine ⟨knownBelow_mono tail (by omega), fun key => ?_⟩
          by_cases same : key = other
          · subst same; simp [absent]
          · have differs : (key == other) = false := by simpa using same
            simp [List.lookup_cons, differs, same]
        | some value =>
          simp only [storeKnown, before, ↓reduceIte, ↓reduceIte]
          refine ⟨knownBelow_cons.mpr ⟨low, high, tail⟩, fun key => ?_⟩
          by_cases same : key = other
          · subst same; simp
          · have differs : (key == other) = false := by simpa using same
            simp [List.lookup_cons, differs, same]
      · have after : index < other := by omega
        have absent : ((other, word) :: rest).lookup index = none :=
          knownBelow_lookup_none (knownBelow_cons.mpr ⟨Nat.le_refl other, otherHigh, tail⟩)
            (Or.inl after)
        cases fact with
        | none =>
          simp only [storeKnown, before, equal, ↓reduceIte]
          refine ⟨known, fun key => ?_⟩
          by_cases same : key = index
          · subst same; simp [absent]
          · simp [same]
        | some value =>
          simp only [storeKnown, before, equal, ↓reduceIte]
          refine ⟨knownBelow_cons.mpr ⟨low, high, knownBelow_cons.mpr ⟨after, otherHigh, tail⟩⟩,
            fun key => ?_⟩
          by_cases same : key = index
          · subst same; simp
          · have differs : (key == index) = false := by simpa using same
            simp [List.lookup_cons, differs, same]
#print axioms storeKnown_spec

/-- The expansion holds each local's looked-up fact and nothing past the last local. -/
theorem expandKnown_getElem? {count : Nat} {locals : List (Nat × W32)} {key : Nat} :
    (expandKnown count locals)[key]? = if key < count then some (locals.lookup key) else none := by
  unfold expandKnown
  rw [List.getElem?_map]
  by_cases inside : key < count
  · simp [inside]
  · simp [inside]
#print axioms expandKnown_getElem?

/-- The expansion has one fact per local. -/
@[simp] theorem expandKnown_length {count : Nat} {locals : List (Nat × W32)} :
    (expandKnown count locals).length = count := by
  simp [expandKnown]
#print axioms expandKnown_length

/-- Storing into known facts is setting the fact in the full per-local list. -/
theorem expandKnown_storeKnown {count index : Nat} {fact : Option W32} {locals : List (Nat × W32)}
    (known : knownBelow count 0 locals = true) (high : index < count) :
    expandKnown count (storeKnown index fact locals) =
      (expandKnown count locals).set index fact := by
  apply List.ext_getElem?
  intro key
  rw [List.getElem?_set, expandKnown_getElem?, expandKnown_getElem?,
    (storeKnown_spec known (Nat.zero_le _) high).2, expandKnown_length]
  by_cases same : index = key
  · subst same; simp [high]
  · simp [same, Ne.symm same]
#print axioms expandKnown_storeKnown

/-- Between known-fact lists, containment of entries is the sublist order. -/
theorem knownBelow_sublist {count : Nat} :
    ∀ {source target : List (Nat × W32)} {sourceNext targetNext : Nat},
    knownBelow count sourceNext source = true → knownBelow count targetNext target = true →
      target ⊆ source → target.Sublist source
  | [], target, _, _, _, _, subset => by
    cases target with
    | nil => exact List.Sublist.slnil
    | cons head rest => exact absurd (subset (List.mem_cons_self ..)) (by simp)
  | (index, word) :: source, [], _, _, _, _, _ => List.nil_sublist _
  | (index, word) :: source, (other, value) :: target, sourceNext, targetNext,
      sourceKnown, targetKnown, subset => by
    have sourceSplit := knownBelow_cons.mp sourceKnown
    have targetSplit := knownBelow_cons.mp targetKnown
    have head := subset (List.mem_cons_self ..)
    by_cases same : (other, value) = (index, word)
    · cases same
      apply List.Sublist.cons_cons
      refine knownBelow_sublist sourceSplit.2.2 targetSplit.2.2 fun entry member => ?_
      have bound := (knownBelow_mem targetSplit.2.2 member).1
      rcases List.mem_cons.mp (subset (List.mem_cons_of_mem _ member)) with equal | later
      · subst equal; omega
      · exact later
    · have later : (other, value) ∈ source := by
        rcases List.mem_cons.mp head with equal | later
        · exact absurd equal same
        · exact later
      have above := (knownBelow_mem sourceSplit.2.2 later).1
      apply List.Sublist.cons
      refine knownBelow_sublist sourceSplit.2.2 targetKnown fun entry member => ?_
      have bound := (knownBelow_mem targetKnown member).1
      rcases List.mem_cons.mp (subset member) with equal | inner
      · rcases List.mem_cons.mp member with first | rest
        · subst first; exact absurd equal same
        · have := (knownBelow_mem targetSplit.2.2 rest).1
          subst equal; simp only at above this; omega
      · exact inner
#print axioms knownBelow_sublist

/-- Known-fact lists with the same lookups are equal. -/
theorem knownBelow_eq {count : Nat} {source target : List (Nat × W32)}
    {sourceNext targetNext : Nat}
    (sourceKnown : knownBelow count sourceNext source = true)
    (targetKnown : knownBelow count targetNext target = true)
    (lookups : ∀ key, source.lookup key = target.lookup key) : source = target := by
  have members : ∀ entry, entry ∈ source ↔ entry ∈ target := by
    intro ⟨key, word⟩
    rw [knownBelow_mem_iff sourceKnown, knownBelow_mem_iff targetKnown, lookups]
  have inward := knownBelow_sublist sourceKnown targetKnown fun entry => (members entry).mpr
  have outward := knownBelow_sublist targetKnown sourceKnown fun entry => (members entry).mp
  exact outward.eq_of_length (Nat.le_antisymm outward.length_le inward.length_le)
#print axioms knownBelow_eq

/-- Pointwise weakening: equal lengths, and every known fact of the target is the source's. -/
theorem factsWeaken_iff {source target : List (Option W32)} :
    factsWeaken source target = true ↔ source.length = target.length ∧
      ∀ (key : Nat) (word : W32), target[key]? = some (some word) →
        source[key]? = some (some word) := by
  induction source generalizing target with
  | nil =>
    cases target with
    | nil => simp [factsWeaken]
    | cons head rest => simp [factsWeaken]
  | cons first source ih =>
    cases target with
    | nil => simp [factsWeaken]
    | cons head rest =>
      have step : factsWeaken (first :: source) (head :: rest) =
          (factWeakens first head && factsWeaken source rest) := by
        simp only [factsWeaken, List.length_cons, List.zip_cons_cons, List.all_cons]
        cases factWeakens first head <;> simp [Bool.and_comm]
      rw [step, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨weakens, length, later⟩
        refine ⟨by simp [length], fun key word found => ?_⟩
        cases key with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found ⊢
          subst found
          simpa [factWeakens] using weakens
        | succ key => simpa using later key word (by simpa using found)
      · rintro ⟨length, later⟩
        refine ⟨?_, by simpa using length, fun key word found => by
          simpa using later (key + 1) word (by simpa using found)⟩
        cases head with
        | none => rfl
        | some word =>
          have := later 0 word rfl
          simp only [List.getElem?_cons_zero, Option.some.injEq] at this
          simp [factWeakens, this]
#print axioms factsWeaken_iff

/-- A local holds a known fact in the expansion exactly when the list has that entry. -/
theorem expandKnown_some {count : Nat} {locals : List (Nat × W32)}
    (known : knownBelow count 0 locals = true) {key : Nat} {word : W32} :
    (expandKnown count locals)[key]? = some (some word) ↔ (key, word) ∈ locals := by
  rw [expandKnown_getElem?, knownBelow_mem_iff known]
  by_cases inside : key < count
  · simp [inside]
  · simp only [inside, ↓reduceIte, reduceCtorEq, false_iff]
    rw [knownBelow_lookup_none known (Or.inr (Nat.le_of_not_lt inside))]
    simp
#print axioms expandKnown_some

/-- The sublist test on known facts is pointwise weakening of their expansions. -/
theorem isSublist_eq_factsWeaken {count : Nat} {source target : List (Nat × W32)}
    (sourceKnown : knownBelow count 0 source = true)
    (targetKnown : knownBelow count 0 target = true) :
    target.isSublist source =
      factsWeaken (expandKnown count source) (expandKnown count target) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.isSublist_iff_sublist, factsWeaken_iff]
  simp only [expandKnown_length, true_and, expandKnown_some sourceKnown,
    expandKnown_some targetKnown]
  constructor
  · intro sublist key word member
    exact sublist.subset member
  · intro subset
    exact knownBelow_sublist sourceKnown targetKnown fun ⟨key, word⟩ member =>
      subset key word member
#print axioms isSublist_eq_factsWeaken

/-- Different known-fact lists over the same locals expand to different full lists. -/
theorem expandKnown_inj {count : Nat} {source target : List (Nat × W32)}
    (sourceKnown : knownBelow count 0 source = true)
    (targetKnown : knownBelow count 0 target = true)
    (expanded : expandKnown count source = expandKnown count target) : source = target := by
  refine knownBelow_eq sourceKnown targetKnown fun key => ?_
  by_cases inside : key < count
  · have := congrArg (·[key]?) expanded
    simp only [expandKnown_getElem?, inside, ↓reduceIte, Option.some.injEq] at this
    exact this
  · rw [knownBelow_lookup_none sourceKnown (Or.inr (Nat.le_of_not_lt inside)),
      knownBelow_lookup_none targetKnown (Or.inr (Nat.le_of_not_lt inside))]
#print axioms expandKnown_inj

/-- With unknown always eligible, the expansion is eligible exactly when every known fact is. -/
theorem expandKnown_all {count : Nat} {locals : List (Nat × W32)}
    {eligible : Nat → Option W32 → Bool}
    (unknown : ∀ index, eligible index none = true) (known : knownBelow count 0 locals = true) :
    ((expandKnown count locals).zipIdx.all fun (fact, index) => eligible index fact) =
      locals.all fun entry => eligible entry.1 (some entry.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, Prod.forall, List.mem_zipIdx_iff_getElem?, expandKnown_getElem?]
  constructor
  · intro all index word member
    have inside := (knownBelow_mem known member).2
    have := all (some word) index
    rw [(knownBelow_mem_iff known).mp member] at this
    exact this (by simp [inside])
  · intro all fact index found
    by_cases inside : index < count
    · simp only [inside, ↓reduceIte, Option.some.injEq] at found
      subst found
      cases looked : locals.lookup index with
      | none => exact unknown index
      | some word => exact all index word ((knownBelow_mem_iff known).mpr looked)
    · simp [inside] at found
#print axioms expandKnown_all

/-- Compressing a full list keeps its known facts in order, numbered from the start index. -/
theorem compressKnown_spec (facts : List (Option W32)) :
    ∀ (start count : Nat), start + facts.length ≤ count →
      knownBelow count start (compressKnown start facts) = true ∧
      ∀ key, (compressKnown start facts).lookup key =
        if start ≤ key then facts[key - start]?.join else none := by
  induction facts with
  | nil => intro start count _; simp [compressKnown, knownBelow]
  | cons fact rest ih =>
    intro start count bound
    have inner := ih (start + 1) count (by simp at bound; omega)
    cases fact with
    | none =>
      refine ⟨knownBelow_mono inner.1 (by omega), fun key => ?_⟩
      simp only [compressKnown, inner.2]
      by_cases same : key = start
      · subst same
        rw [ite_eq_right (by omega), ite_eq_left (Nat.le_refl _)]
        simp
      · by_cases above : start + 1 ≤ key
        · have shifted : key - start = (key - (start + 1)) + 1 := by omega
          simp [above, show start ≤ key by omega, shifted]
        · simp [above, show ¬ start ≤ key by omega]
    | some word =>
      simp only [compressKnown]
      refine ⟨knownBelow_cons.mpr ⟨Nat.le_refl _, by simp at bound; omega, inner.1⟩,
        fun key => ?_⟩
      by_cases same : key = start
      · subst same; simp
      · have differs : (key == start) = false := by simpa using same
        simp only [List.lookup_cons, differs, inner.2]
        by_cases above : start + 1 ≤ key
        · have shifted : key - start = (key - (start + 1)) + 1 := by omega
          simp [above, show start ≤ key by omega, shifted]
        · simp [above, show ¬ start ≤ key by omega]
#print axioms compressKnown_spec

/-- Compressing a full list gives a known-fact list over its locals. -/
theorem compressKnown_known (facts : List (Option W32)) :
    knownBelow facts.length 0 (compressKnown 0 facts) = true :=
  (compressKnown_spec facts 0 facts.length (by simp)).1
#print axioms compressKnown_known

/-- Expanding the compression of a full list over its own length gives it back. -/
theorem expandKnown_compressKnown (facts : List (Option W32)) :
    expandKnown facts.length (compressKnown 0 facts) = facts := by
  apply List.ext_getElem?
  intro key
  rw [expandKnown_getElem?, (compressKnown_spec facts 0 facts.length (by simp)).2]
  by_cases inside : key < facts.length
  · simp [inside]
  · simp [inside]
#print axioms expandKnown_compressKnown

end CIL.Extraction
