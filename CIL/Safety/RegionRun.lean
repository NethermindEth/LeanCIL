import CIL.Safety.StepFlow
import Std.Data.TreeMap.Lemmas

/-!
# Runs confined to a code region

A run that starts inside a region closed under control flow never reads code outside it, so
two programs that agree on that region run identically from it (`run_congr_region`).
`regionClosedCheck` decides closure for regions given as method suffixes.
-/

namespace CIL.Safety

/-- Fallthroughs and code targets of every region instruction stay in the region, and every
    method a region pc's link table entry may enter is in the region from its entry. -/
def RegionClosed (program : CIL.Program) (region : Nat → Nat → Prop) : Prop :=
  (∀ method pc body op, region method pc → program[method]? = some body →
    body.code[pc]? = some op →
    (op.continues = true → region method (pc + 1)) ∧ ∀ target ∈ op.targets, region method target) ∧
  ∀ method body, program[method]? = some body → ∀ entry ∈ body.links, region method entry.1 →
    ∀ callee ∈ entry.2.callees, region callee 0

/-- `other` has `program`'s methods with the same metadata and the same instruction at every
    region pc. -/
def AgreesOn (program other : CIL.Program) (region : Nat → Nat → Prop) : Prop :=
  other.length = program.length ∧
    ∀ method pc body, region method pc → program[method]? = some body →
      ∃ body', other[method]? = some body' ∧ body' = { body with code := body'.code } ∧
        body'.code[pc]? = body.code[pc]?

/-- An instruction that reads its link, other than a tail call, falls through to the next pc. -/
theorem Instruction.continues_of_linked {op : CIL.Instruction}
    (linked : op.readsLink = true)
    (notTail : ∀ method prefixes, op = .call method prefixes → prefixes.tail = false)
    (notManagedTail : ∀ signature, op ≠ .calli signature true) :
    op.continues = true := by
  cases op <;> simp_all [CIL.Instruction.readsLink, CIL.Instruction.continues]

#print axioms Instruction.continues_of_linked

private theorem AgreesOn.found {program other : CIL.Program} {region : Nat → Nat → Prop}
    (agrees : AgreesOn program other region) {method pc : Nat} (inside : region method pc) :
    (program[method]? = none ∧ other[method]? = none) ∨
      ∃ body body', program[method]? = some body ∧
        other[method]? = some body' ∧ body' = { body with code := body'.code } ∧
        body'.code[pc]? = body.code[pc]? := by
  cases found : program[method]? with
  | none =>
    refine .inl ⟨rfl, ?_⟩
    simp only [List.getElem?_eq_none_iff] at found ⊢
    exact agrees.1 ▸ found
  | some body =>
    obtain ⟨body', other', same, code⟩ := agrees.2 method pc body inside found
    exact .inr ⟨body, body', rfl, other', same, code⟩

/-- Programs that agree on a closed region run identically from any of its pcs, faults
    included. -/
theorem run_congr_region {program other : CIL.Program} {region : Nat → Nat → Prop}
    (closed : RegionClosed program region) (agrees : AgreesOn program other region)
    (fuel method pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (inside : region method pc) (free : HandlerFree program := by handler_free) :
    run other fuel method pc args frame stack m =
      run program fuel method pc args frame stack m := by
  induction fuel generalizing method pc args frame stack m with
  | zero => rfl
  | succ fuel ih =>
    rcases agrees.found inside with ⟨hb, hb'⟩ | ⟨body, body', hb, hb', same, code⟩
    · simp only [run_succ _ _ _ _ _ _ _ _ (unprotected_of_none hb pc),
        run_succ _ _ _ _ _ _ _ _ (unprotected_of_none hb' pc), hb, hb']
    have freeBody : body.handlers = [] := free body (List.mem_of_getElem? hb)
    rw [same] at hb'
    rw [run_succ _ _ _ _ _ _ _ _ (unprotected_of_handlers_nil hb freeBody pc),
      run_succ _ _ _ _ _ _ _ _ (unprotected_of_handlers_nil hb' freeBody pc)]
    cases ho : body.code[pc]? with
    | none => simp only [hb, hb', ← same, code, ho]
    | some op =>
      obtain ⟨continues, targets⟩ := closed.1 method pc body op inside hb ho
      -- A method the step enters is listed by a link entry at this region pc.
      have callees : ∀ callee ∈ body.calleesAt pc, region callee 0 := fun callee member => by
        obtain ⟨entry, listed, located, member⟩ := CIL.Method.calleesAt_mem member
        exact closed.2 method body hb entry listed (located ▸ inside) callee member
      simp only [hb, hb', ← same, code, ho]
      rw [same, show step { body with code := body'.code } op pc args frame stack m =
        step body op pc args frame stack m from rfl]
      cases hs : step body op pc args frame stack m with
      | error fault => simp only [Bind.bind, Except.bind, Except.mapError]
      | ok action =>
        simp only [Bind.bind, Except.bind, Except.mapError]
        cases action with
        | next target stack' frame' m' =>
          rcases step_next_target hs (fun _ => freeBody) with ⟨go, rfl⟩ | member
          · exact ih method _ args frame' stack' m' (continues go)
          · exact ih method _ args frame' stack' m' (targets target member)
        | returned result m' => rfl
        | raise _ _ _ _ => exact (step_ne_raise freeBody hs).elim
        | call callee arguments rest m' =>
          obtain ⟨linked, entered⟩ := step_callee hs rfl
          have child := callees callee entered
          have resume := continues (Instruction.continues_of_linked linked (by
            intro method prefixes equal
            subst op
            rcases step_call_action hs with ⟨_, _, chosen⟩ | ⟨_, _, _, _, _, impossible, _⟩
            · cases tail : prefixes.tail
              · rfl
              · simp only [tail, ite_true] at chosen
                obtain ⟨_, _, impossible⟩ := chosen
                cases impossible
            · cases impossible) (by
            intro signature equal
            subst op
            obtain ⟨_, _, _, impossible⟩ := step_managed_tail_action hs
            cases impossible))
          rcases agrees.found child with ⟨cb, cb'⟩ | ⟨cbody, cbody', cb, cb', csame, _⟩
          · simp only [cb, cb']
          rw [csame] at cb'
          simp only [cb, cb', show enterFrame { cbody with code := cbody'.code } arguments m' =
            enterFrame cbody arguments m' from rfl]
          cases he : enterFrame cbody arguments m' with
          | error fault => rfl
          | ok entered' =>
            simp only [ih callee 0 _ _ _ _ child]
            cases run program fuel callee 0 arguments entered'.1 [] entered'.2 with
            | error fault => rfl
            | ok result => exact ih method (pc + 1) args frame _ _ resume
        | tailCall callee arguments updated =>
          have entered := (step_callee hs rfl).2
          have child := callees callee entered
          rcases agrees.found child with ⟨cb, cb'⟩ | ⟨cbody, cbody', cb, cb', csame, _⟩
          · simp only [cb, cb']
          rw [csame] at cb'
          simp only [cb, cb']
          split <;> try rfl
          cases checked : arguments.mapM (checkedValue (leaveFrame frame updated)) with
          | error fault => rfl
          | ok values =>
            simp only [Except.mapError, Bind.bind, Except.bind]
            change (show Except LocatedFault (Memory × List Value) from do
              let (childFrame, childMemory) ← (enterFrame cbody values
                (leaveFrame frame updated)).mapError (fun fault => ⟨method, pc, fault⟩)
              run other fuel callee 0 values childFrame [] childMemory) = _
            cases enterFrame cbody values (leaveFrame frame updated) with
            | error fault => rfl
            | ok result => exact ih callee 0 values result.1 [] result.2 child
        | construct callee arguments rest frame' temporary kind m' =>
          obtain ⟨linked, entered⟩ := step_callee hs rfl
          have child := callees callee entered
          have resume := continues (Instruction.continues_of_linked linked (by
            intro method prefixes equal
            subst op
            rcases step_call_action hs with ⟨_, _, chosen⟩ | ⟨_, _, _, _, _, impossible, _⟩
            · cases tail : prefixes.tail
              · rfl
              · simp only [tail, ite_true] at chosen
                obtain ⟨_, _, impossible⟩ := chosen
                cases impossible
            · cases impossible) (by
            intro signature equal
            subst op
            obtain ⟨_, _, _, impossible⟩ := step_managed_tail_action hs
            cases impossible))
          rcases agrees.found child with ⟨cb, cb'⟩ | ⟨cbody, cbody', cb, cb', csame, _⟩
          · simp only [cb, cb']
          rw [csame] at cb'
          simp only [cb, cb', show enterFrame { cbody with code := cbody'.code } arguments m' =
            enterFrame cbody arguments m' from rfl]
          cases he : enterFrame cbody arguments m' with
          | error fault => rfl
          | ok entered' =>
            simp only [ih callee 0 _ _ _ _ child]
            cases run program fuel callee 0 arguments entered'.1 [] entered'.2 with
            | error fault => rfl
            | ok result =>
              simp only
              split
              · rfl
              · cases loadLocal result.1 (.bytes kind temporary) with
                | error fault => rfl
                | ok value => exact ih method (pc + 1) args frame' _ _ resume

/-- Replacing one method's code keeps agreement where the new code matches the old. -/
theorem AgreesOn.set {program : CIL.Program} {region : Nat → Nat → Prop} {index : Nat}
    {body : CIL.Method}
    (found : program[index]? = some body) (code : List CIL.Instruction)
    (agree : ∀ pc, region index pc → code[pc]? = body.code[pc]?) :
    AgreesOn program (program.set index { body with code := code }) region := by
  refine ⟨List.length_set .., fun method pc candidate inside fetched => ?_⟩
  by_cases same : method = index
  · subst same
    rw [found] at fetched
    cases fetched
    have bound : method < program.length := (List.getElem?_eq_some_iff.mp found).1
    exact ⟨{ body with code := code }, List.getElem?_set_self bound, rfl, agree pc inside⟩
  · exact ⟨candidate, by rw [List.getElem?_set_ne (Ne.symm same), fetched], rfl, rfl⟩

/-- Code that agrees from `lower` on agrees at every pc at or after it. -/
theorem code_agrees_of_drop {a b : List CIL.Instruction} {lower pc : Nat}
    (same : a.drop lower = b.drop lower) (after : lower ≤ pc) : a[pc]? = b[pc]? := by
  have := congrArg (·[pc - lower]?) same
  simpa only [List.getElem?_drop, Nat.add_sub_cancel' after] using this

/-- Method `method` from pc `lower` on, for each `(method, lower)`; a callee entry needs
    `lower = 0`. -/
def inStarts (starts : List (Nat × Nat)) (method pc : Nat) : Bool :=
  starts.any fun start => start.1 == method && start.2 ≤ pc

/-- Earliest included pc for each method, including methods absent from the program. -/
def regionStartsIndex : List (Nat × Nat) → Std.TreeMap Nat Nat
  | [] => ∅
  | (method, lower) :: rest =>
    let index := regionStartsIndex rest
    index.insert method (match index[method]? with
      | none => lower
      | some previous => min lower previous)
/-- Membership in the union of indexed method suffixes. -/
def indexedInStarts (index : Std.TreeMap Nat Nat) (method pc : Nat) : Bool :=
  match index[method]? with
  | none => false
  | some lower => lower ≤ pc
/-- The minimum start preserves the union of suffixes, including duplicate starts. -/
theorem indexedInStarts_eq (starts : List (Nat × Nat)) (method pc : Nat) :
    indexedInStarts (regionStartsIndex starts) method pc = inStarts starts method pc := by
  induction starts with
  | nil => simp [regionStartsIndex, indexedInStarts, inStarts]
  | cons start rest ih =>
    rcases start with ⟨owner, lower⟩
    simp only [inStarts, List.any_cons] at ih ⊢
    simp only [indexedInStarts] at ih
    simp only [regionStartsIndex, indexedInStarts, Std.TreeMap.getElem?_insert, Nat.compare_eq_eq]
    by_cases same : owner = method
    · subst owner
      simp only [ite_true, beq_self_eq_true, Bool.true_and]
      cases found : (regionStartsIndex rest)[method]? with
      | none =>
        simp only [found] at ih
        simp [← ih]
      | some previous =>
        simp only [found] at ih
        rw [← ih]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, Bool.or_eq_true]
        omega
    · simpa [same, beq_eq_false_iff_ne.mpr same] using ih

#print axioms indexedInStarts_eq

/-- Skip absent methods; check each instruction and each link entry against the earliest included
    pc. -/
def regionBodyCheck (index : Std.TreeMap Nat Nat) (method : Nat) (body : CIL.Method) : Bool :=
  match index[method]? with
  | none => true
  | some lower =>
    (body.code.zipIdx.all fun (op, pc) =>
      !(lower ≤ pc) || op.targets.all (indexedInStarts index method)) &&
    body.links.all fun (pc, link) =>
      !(lower ≤ pc) || link.callees.all (indexedInStarts index · 0)

/-- Skipping absent methods agrees with testing membership at each instruction and entry. -/
theorem regionBodyCheck_eq (index : Std.TreeMap Nat Nat) (method : Nat) (body : CIL.Method) :
    regionBodyCheck index method body =
      ((body.code.zipIdx.all fun (op, pc) =>
        !indexedInStarts index method pc ||
          ((!op.continues || indexedInStarts index method (pc + 1)) &&
            op.targets.all (indexedInStarts index method))) &&
        body.links.all fun (pc, link) =>
          !indexedInStarts index method pc || link.callees.all (indexedInStarts index · 0)) := by
  cases found : index[method]? with
  | none => simp [regionBodyCheck, indexedInStarts, found]
  | some lower =>
    simp only [regionBodyCheck, found]
    congr 1
    · congr 1
      funext (op, pc)
      by_cases inside : lower ≤ pc
      · have next : lower ≤ pc + 1 := by omega
        simp [indexedInStarts, found, inside, next]
      · simp [indexedInStarts, found, inside]
    · congr 1
      funext (pc, link)
      simp [indexedInStarts, found]

#print axioms regionBodyCheck_eq

/-- Check each included method once, even when several starts describe overlapping suffixes. -/
def regionClosedCheck (program : CIL.Program) (starts : List (Nat × Nat)) : Bool :=
  if starts.isEmpty then true else
  let index := regionStartsIndex starts
  program.zipIdx.all fun (body, method) => regionBodyCheck index method body
/-- The executable check is exactly closure of the union of supplied method suffixes. -/
theorem regionClosedCheck_iff (program : CIL.Program) (starts : List (Nat × Nat)) :
    regionClosedCheck program starts = true ↔
      RegionClosed program (fun method pc => inStarts starts method pc = true) := by
  by_cases empty : starts = []
  · subst starts
    simp [regionClosedCheck, RegionClosed, inStarts]
  have nonempty : starts.isEmpty = false := by cases starts <;> simp_all
  simp only [regionClosedCheck, nonempty, Bool.false_eq_true, ↓reduceIte,
    regionBodyCheck_eq, indexedInStarts_eq, List.all_eq_true]
  constructor
  · intro checked
    refine ⟨fun method pc body op inside found fetched => ?_,
      fun method body found entry listed inside => ?_⟩
    · have bodyCheck := checked (body, method) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
      simp only [Bool.and_eq_true, List.all_eq_true] at bodyCheck
      have opCheck := bodyCheck.1 (op, pc) (List.mk_mem_zipIdx_iff_getElem?.mpr fetched)
      simp only [inside, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, indexedInStarts_eq] at opCheck
      refine ⟨?_, opCheck.2⟩
      intro continues
      rcases opCheck.1 with stopped | next
      · simp_all
      · exact next
    · have bodyCheck := checked (body, method) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
      simp only [Bool.and_eq_true, List.all_eq_true] at bodyCheck
      rcases entry with ⟨pc, link⟩
      have entryCheck := bodyCheck.2 (pc, link) listed
      simp only [inside, Bool.not_true, Bool.false_or, List.all_eq_true,
        indexedInStarts_eq] at entryCheck
      exact entryCheck
  · intro closed entry present
    rcases entry with ⟨body, method⟩
    have found := List.mk_mem_zipIdx_iff_getElem?.mp present
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun instruction fetched => ?_, fun entry listed => ?_⟩
    · rcases instruction with ⟨op, pc⟩
      have code := List.mk_mem_zipIdx_iff_getElem?.mp fetched
      by_cases inside : inStarts starts method pc = true
      · obtain ⟨next, targets⟩ := closed.1 method pc body op inside found code
        simp only [inside, Bool.not_true, Bool.false_or, Bool.and_eq_true,
          Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, indexedInStarts_eq]
        exact ⟨by cases continues : op.continues <;> simp_all, targets⟩
      · simp [inside]
    · rcases entry with ⟨pc, link⟩
      by_cases inside : inStarts starts method pc = true
      · simp only [inside, Bool.not_true, Bool.false_or, List.all_eq_true, indexedInStarts_eq]
        exact closed.2 method body found (pc, link) listed inside
      · simp [inside]

#print axioms regionClosedCheck_iff

/-- Indexed closure accepts exactly the per-start check that scans every position and every link
    entry. -/
theorem regionClosedCheck_eq_original (program : CIL.Program) (starts : List (Nat × Nat)) :
    regionClosedCheck program starts = (starts.all fun start => match program[start.1]? with
      | none => true
      | some body => ((List.range body.code.length).all fun pc =>
        !(start.2 ≤ pc) || match body.code[pc]? with
        | none => true
        | some op => (!op.continues || inStarts starts start.1 (pc + 1)) &&
          op.targets.all (inStarts starts start.1)) &&
        body.links.all fun entry =>
          !(start.2 ≤ entry.1) || entry.2.callees.all (inStarts starts · 0)) := by
  apply Bool.eq_iff_iff.mpr
  rw [regionClosedCheck_iff]
  constructor
  · intro closed
    simp only [List.all_eq_true]
    intro start member
    have startInside : ∀ pc, start.2 ≤ pc → inStarts starts start.1 pc = true := fun pc below => by
      simp only [inStarts, List.any_eq_true]
      exact ⟨start, member, by simp [below]⟩
    cases found : program[start.1]? with
    | none => rfl
    | some body =>
      simp only [Bool.and_eq_true, List.all_eq_true]
      refine ⟨fun pc bound => ?_, fun entry listed => ?_⟩
      · by_cases below : start.2 ≤ pc
        · cases fetched : body.code[pc]? with
          | none => simp
          | some op =>
            obtain ⟨next, targets⟩ := closed.1 _ _ _ _ (startInside pc below) found fetched
            simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
              List.all_eq_true]
            right
            exact ⟨by cases continues : op.continues <;> simp_all, targets⟩
        · simp [below]
      · by_cases below : start.2 ≤ entry.1
        · simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
          exact .inr (closed.2 _ _ found entry listed (startInside entry.1 below))
        · simp [below]
  · intro checked
    simp only [List.all_eq_true] at checked
    refine ⟨fun method pc body op inside found fetched => ?_,
      fun method body found entry listed inside => ?_⟩
    · simp only [inStarts, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at inside
      obtain ⟨⟨start, lower⟩, member, rfl, below⟩ := inside
      have bound : pc < body.code.length := (List.getElem?_eq_some_iff.mp fetched).1
      have scanned := checked _ member
      simp only [found, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at scanned
      rcases scanned.1 pc bound with early | late
      · omega
      · simp only [fetched, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          List.all_eq_true] at late
        obtain ⟨go, targets⟩ := late
        refine ⟨fun continues => ?_, targets⟩
        rcases go with stop | next
        · simp_all
        · exact next
    · simp only [inStarts, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at inside
      obtain ⟨⟨start, lower⟩, member, rfl, below⟩ := inside
      have scanned := checked _ member
      simp only [found, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at scanned
      rcases scanned.2 entry listed with early | late
      · omega
      · exact late

#print axioms regionClosedCheck_eq_original
/-- `regionClosedCheck` is sound for `RegionClosed`. -/
theorem RegionClosed.of_check {program : CIL.Program} {starts : List (Nat × Nat)}
    (checked : regionClosedCheck program starts = true) :
    RegionClosed program fun method pc => inStarts starts method pc = true :=
  (regionClosedCheck_iff program starts).mp checked

#print axioms RegionClosed.of_check

end CIL.Safety
