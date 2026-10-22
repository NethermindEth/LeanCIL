import CIL.Safety.StepFlow

/-! A run that starts inside a region closed under control flow never reads code outside it. -/

namespace CIL.Safety

/-- Fallthroughs, code targets and callee entries of every region instruction stay in the region. -/
def RegionClosed (program : CIL.Program) (region : Nat → Nat → Prop) : Prop :=
  ∀ method pc body op, region method pc → program[method]? = some body → body.code[pc]? = some op →
    (op.continues = true → region method (pc + 1)) ∧ (∀ target ∈ op.targets, region method target) ∧
    ∀ callee ∈ op.callees, region callee 0

/-- `other` has `program`'s methods with the same metadata and the same instruction at every region pc. -/
def AgreesOn (program other : CIL.Program) (region : Nat → Nat → Prop) : Prop :=
  other.length = program.length ∧
    ∀ method pc body, region method pc → program[method]? = some body →
      ∃ body', other[method]? = some body' ∧ body' = { body with code := body'.code } ∧ body'.code[pc]? = body.code[pc]?

theorem Op.continues_of_callee {op : CIL.Op} {callee : Nat} (h : op.callees.head? = some callee) :
    op.continues = true := by
  cases op <;> simp_all [CIL.Op.callees, CIL.Op.continues]

private theorem AgreesOn.found {program other : CIL.Program} {region : Nat → Nat → Prop}
    (agrees : AgreesOn program other region) {method pc : Nat} (inside : region method pc) :
    (program[method]? = none ∧ other[method]? = none) ∨ ∃ body body', program[method]? = some body ∧
      other[method]? = some body' ∧ body' = { body with code := body'.code } ∧ body'.code[pc]? = body.code[pc]? := by
  cases found : program[method]? with
  | none =>
    refine .inl ⟨rfl, ?_⟩
    simp only [List.getElem?_eq_none_iff] at found ⊢
    exact agrees.1 ▸ found
  | some body =>
    obtain ⟨body', other', same, code⟩ := agrees.2 method pc body inside found
    exact .inr ⟨body, body', rfl, other', same, code⟩

/-- Programs that agree on a closed region run identically from any of its pcs, faults included. -/
theorem run_congr_region {program other : CIL.Program} {region : Nat → Nat → Prop}
    (closed : RegionClosed program region) (agrees : AgreesOn program other region)
    (fuel method pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (inside : region method pc) :
    run other fuel method pc args frame stack m = run program fuel method pc args frame stack m := by
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
          have resume := continues (Op.continues_of_callee entered.symm)
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
        | construct callee arguments rest frame' temporary kind m' =>
          have entered := step_callee hs
          have child := callees callee (List.mem_of_head? entered.symm)
          have resume := continues (Op.continues_of_callee entered.symm)
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
theorem AgreesOn.set {program : CIL.Program} {region : Nat → Nat → Prop} {index : Nat} {body : CIL.Method}
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
theorem code_agrees_of_drop {a b : List CIL.Op} {lower pc : Nat} (same : a.drop lower = b.drop lower)
    (after : lower ≤ pc) : a[pc]? = b[pc]? := by
  have := congrArg (·[pc - lower]?) same
  simpa only [List.getElem?_drop, Nat.add_sub_cancel' after] using this

/-- Method `method` from pc `lower` on, for each `(method, lower)`; a callee entry needs `lower = 0`. -/
def inStarts (starts : List (Nat × Nat)) (method pc : Nat) : Bool :=
  starts.any fun start => start.1 == method && start.2 ≤ pc

/-- Decides `RegionClosed` for the region `inStarts starts` by scanning each listed suffix once. -/
def regionClosedCheck (program : CIL.Program) (starts : List (Nat × Nat)) : Bool :=
  starts.all fun start => match program[start.1]? with
    | none => true
    | some body => (List.range body.code.length).all fun pc => !(start.2 ≤ pc) || match body.code[pc]? with
      | none => true
      | some op => (!op.continues || inStarts starts start.1 (pc + 1)) &&
          op.targets.all (inStarts starts start.1) && op.callees.all (inStarts starts · 0)

theorem RegionClosed.of_check {program : CIL.Program} {starts : List (Nat × Nat)}
    (checked : regionClosedCheck program starts = true) :
    RegionClosed program fun method pc => inStarts starts method pc = true := by
  intro method pc body op inside found fetched
  simp only [inStarts, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at inside
  obtain ⟨⟨start, lower⟩, member, rfl, below⟩ := inside
  simp only [regionClosedCheck, List.all_eq_true] at checked
  have bound : pc < body.code.length := (List.getElem?_eq_some_iff.mp fetched).1
  have scanned := checked _ member
  simp only [found, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_le] at scanned
  rcases scanned pc bound with early | late
  · omega
  · simp only [fetched, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at late
    obtain ⟨⟨go, targets⟩, callees⟩ := late
    refine ⟨fun continues => ?_, targets, callees⟩
    rcases go with stop | next
    · simp_all
    · exact next

end CIL.Safety
