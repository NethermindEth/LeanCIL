import CIL.Safety.StepFlow
import Std.Data.TreeMap.Lemmas

/-!
# Runs confined to a code region

A run that starts inside a region closed under control flow never reads code outside it, so
two programs that agree on that region run identically from it (`run_congr_region`).
`regionClosedCheck` decides closure for regions given as method suffixes.
-/

namespace CIL.Safety

/-- Fallthroughs, code targets and callee entries of every region instruction stay in the
    region. -/
def RegionClosed (program : CIL.Program) (region : Nat → Nat → Prop) : Prop :=
  ∀ method pc body op, region method pc → program[method]? = some body →
    body.code[pc]? = some op →
    (op.continues = true → region method (pc + 1)) ∧
    (∀ target ∈ op.targets, region method target) ∧
    ∀ callee ∈ op.callees, region callee 0

/-- `other` has `program`'s methods with the same metadata and the same instruction at every
    region pc. -/
def AgreesOn (program other : CIL.Program) (region : Nat → Nat → Prop) : Prop :=
  other.length = program.length ∧
    ∀ method pc body, region method pc → program[method]? = some body →
      ∃ body', other[method]? = some body' ∧ body' = { body with code := body'.code } ∧
        body'.code[pc]? = body.code[pc]?

/-- A non-tail instruction that calls a method falls through to the next pc. -/
theorem Op.continues_of_callee {op : CIL.Op} {callee : Nat}
    (h : op.callees.head? = some callee)
    (notTail : ∀ argc, op ≠ .tailCall callee argc) :
    op.continues = true := by
  cases op <;> simp_all [CIL.Op.callees, CIL.Op.continues]

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
    (inside : region method pc) :
    run other fuel method pc args frame stack m =
      run program fuel method pc args frame stack m := by
  induction fuel generalizing method pc args frame stack m with
  | zero => rfl
  | succ fuel ih =>
    rcases agrees.found inside with ⟨hb, hb'⟩ | ⟨body, body', hb, hb', same, code⟩
    · simp only [run, hb, hb']
    rw [same] at hb'
    cases ho : body.code[pc]? with
    | none => simp only [run, hb, hb', ← same, code, ho]
    | some op =>
      obtain ⟨continues, targets, callees⟩ := closed method pc body op inside hb ho
      simp only [run, hb, hb', ← same, code, ho]
      rw [same, show step { body with code := body'.code } op pc args frame stack m =
        step body op pc args frame stack m from rfl]
      cases hs : step body op pc args frame stack m with
      | error fault => simp only [Bind.bind, Except.bind, Except.mapError]
      | ok action =>
        simp only [Bind.bind, Except.bind, Except.mapError]
        cases action with
        | next target stack' frame' m' =>
          rcases step_next_target hs with ⟨go, rfl⟩ | member
          · exact ih method _ args frame' stack' m' (continues go)
          · exact ih method _ args frame' stack' m' (targets target member)
        | returned result m' => rfl
        | call callee arguments rest m' =>
          have entered := step_callee hs
          have child := callees callee (List.mem_of_head? entered.symm)
          have resume := continues (Op.continues_of_callee entered.symm (by
            intro argc equal
            subst op
            obtain ⟨_, _, impossible⟩ := step_tailCall_action hs
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
          have entered := step_callee hs
          have child := callees callee (List.mem_of_head? entered.symm)
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
          have entered := step_callee hs
          have child := callees callee (List.mem_of_head? entered.symm)
          have resume := continues (Op.continues_of_callee entered.symm (by
            intro argc equal
            subst op
            obtain ⟨_, _, impossible⟩ := step_tailCall_action hs
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
    (found : program[index]? = some body) (code : List CIL.Op)
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
theorem code_agrees_of_drop {a b : List CIL.Op} {lower pc : Nat}
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

/-- Skip absent methods and check each instruction using the earliest included pc. -/
def regionBodyCheck (index : Std.TreeMap Nat Nat) (method : Nat) (code : List CIL.Op) : Bool :=
  match index[method]? with
  | none => true
  | some lower => code.zipIdx.all fun (op, pc) =>
    !(lower ≤ pc) || (op.targets.all (indexedInStarts index method) &&
      op.callees.all (indexedInStarts index · 0))

/-- Skipping absent methods agrees with testing membership at each instruction. -/
theorem regionBodyCheck_eq (index : Std.TreeMap Nat Nat) (method : Nat) (code : List CIL.Op) :
    regionBodyCheck index method code = (code.zipIdx.all fun (op, pc) =>
      !indexedInStarts index method pc ||
        ((!op.continues || indexedInStarts index method (pc + 1)) &&
          op.targets.all (indexedInStarts index method) &&
          op.callees.all (indexedInStarts index · 0))) := by
  cases found : index[method]? with
  | none => simp [regionBodyCheck, indexedInStarts, found]
  | some lower =>
    simp only [regionBodyCheck, found]
    congr 1
    funext (op, pc)
    by_cases inside : lower ≤ pc
    · have next : lower ≤ pc + 1 := by omega
      simp [indexedInStarts, found, inside, next]
    · simp [indexedInStarts, found, inside]

#print axioms regionBodyCheck_eq

/-- Check each included method once, even when several starts describe overlapping suffixes. -/
def regionClosedCheck (program : CIL.Program) (starts : List (Nat × Nat)) : Bool :=
  if starts.isEmpty then true else
  let index := regionStartsIndex starts
  program.zipIdx.all fun (body, method) => regionBodyCheck index method body.code
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
  · intro checked method pc body op inside found fetched
    have bodyCheck := checked (body, method) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    have opCheck := bodyCheck (op, pc) (List.mk_mem_zipIdx_iff_getElem?.mpr fetched)
    simp only [inside, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, indexedInStarts_eq] at opCheck
    refine ⟨?_, opCheck.1.2, opCheck.2⟩
    intro continues
    rcases opCheck.1.1 with stopped | next
    · simp_all
    · exact next
  · intro closed entry present instruction fetched
    rcases entry with ⟨body, method⟩
    rcases instruction with ⟨op, pc⟩
    have found := List.mk_mem_zipIdx_iff_getElem?.mp present
    have code := List.mk_mem_zipIdx_iff_getElem?.mp fetched
    by_cases inside : inStarts starts method pc = true
    · obtain ⟨next, targets, callees⟩ := closed method pc body op inside found code
      simp only [inside, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, indexedInStarts_eq]
      exact ⟨⟨by cases continues : op.continues <;> simp_all, targets⟩, callees⟩
    · simp [inside]

#print axioms regionClosedCheck_iff

/-- Indexed closure accepts exactly the former per-start, per-position check. -/
theorem regionClosedCheck_eq_original (program : CIL.Program) (starts : List (Nat × Nat)) :
    regionClosedCheck program starts = (starts.all fun start => match program[start.1]? with
      | none => true
      | some body => (List.range body.code.length).all fun pc =>
        !(start.2 ≤ pc) || match body.code[pc]? with
        | none => true
        | some op => (!op.continues || inStarts starts start.1 (pc + 1)) &&
          op.targets.all (inStarts starts start.1) && op.callees.all (inStarts starts · 0)) := by
  apply Bool.eq_iff_iff.mpr
  rw [regionClosedCheck_iff]
  constructor
  · intro closed
    simp only [List.all_eq_true]
    intro start member
    cases found : program[start.1]? with
    | none => rfl
    | some body =>
      simp only [List.all_eq_true]
      intro pc bound
      by_cases below : start.2 ≤ pc
      · cases fetched : body.code[pc]? with
        | none => simp
        | some op =>
          have inside : inStarts starts start.1 pc = true := by
            simp only [inStarts, List.any_eq_true]
            exact ⟨start, member, by simp [below]⟩
          obtain ⟨next, targets, callees⟩ := closed _ _ _ _ inside found fetched
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
            List.all_eq_true]
          right
          exact ⟨⟨by cases continues : op.continues <;> simp_all, targets⟩, callees⟩
      · simp [below]
  · intro checked method pc body op inside found fetched
    simp only [inStarts, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at inside
    obtain ⟨⟨start, lower⟩, member, rfl, below⟩ := inside
    simp only [List.all_eq_true] at checked
    have bound : pc < body.code.length := (List.getElem?_eq_some_iff.mp fetched).1
    have scanned := checked _ member
    simp only [found, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at scanned
    rcases scanned pc bound with early | late
    · omega
    · simp only [fetched, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        List.all_eq_true] at late
      obtain ⟨⟨go, targets⟩, callees⟩ := late
      refine ⟨fun continues => ?_, targets, callees⟩
      rcases go with stop | next
      · simp_all
      · exact next

#print axioms regionClosedCheck_eq_original
/-- `regionClosedCheck` is sound for `RegionClosed`. -/
theorem RegionClosed.of_check {program : CIL.Program} {starts : List (Nat × Nat)}
    (checked : regionClosedCheck program starts = true) :
    RegionClosed program fun method pc => inStarts starts method pc = true :=
  (regionClosedCheck_iff program starts).mp checked

#print axioms RegionClosed.of_check

end CIL.Safety
