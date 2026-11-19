import CIL.Safety.Embedding.Step

/-!
# Step control flow

Where one checked step of `CIL.Safety.step` can go: the pc it resumes at and the method it
enters. These bound the control-flow graph of a method from its code alone, so region and
loop proofs can enumerate successors without stepping.
-/

namespace CIL

/-- Every method index the call site at `pc` may enter: the callees of its link, none when the
    link table gives the pc no entry. -/
def Method.calleesAt (body : Method) (pc : Nat) : List Nat :=
  ((body.linkAt pc).map Link.callees).getD []

/-- A method a call site may enter is a callee of an entry of the link table at that pc. -/
theorem Method.calleesAt_mem {body : Method} {pc callee : Nat}
    (member : callee ∈ body.calleesAt pc) :
    ∃ entry ∈ body.links, entry.1 = pc ∧ callee ∈ entry.2.callees := by
  simp only [Method.calleesAt, Method.linkAt, linkLookup] at member
  cases found : body.links.find? (fun entry => entry.1 == pc) with
  | none => simp [found] at member
  | some entry =>
    simp only [found, Option.map_some, Option.getD_some] at member
    exact ⟨entry, List.mem_of_find?_eq_some found, by simpa using List.find?_some found, member⟩

#print axioms Method.calleesAt_mem

end CIL

namespace CIL.Safety

/-- The method an action enters, if any. -/
def FrameAction.callee : FrameAction → Option Nat
  | .call callee .. | .tailCall callee .. | .construct callee .. => some callee
  | _ => none

/-- An indirect call can enter only a body named in the authenticated catalog of its link. -/
theorem managedStep_callee {operation : CIL.ManagedOp} {link : Option CIL.Link} {pc : Nat}
    {frame : Frame} {stack : List Value} {memory : Memory} {action : FrameAction} {callee : Nat}
    (executed : managedStep operation link pc frame stack memory = .ok action)
    (enters : action.callee = some callee) :
      (CIL.Instruction.managed operation).readsLink = true ∧
        callee ∈ (link.map CIL.Link.callees).getD [] := by
  unfold managedStep at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first
    | solve |
      cases executed
      simp only [FrameAction.callee, Option.some.injEq] at enters
      subst callee
      refine ⟨rfl, ?_⟩
      simp only [Option.map_some, Option.getD_some, CIL.Link.callees]
      exact indirectTarget_mem (by assumption)
    | solve | cases executed; cases enters
    | cases executed
    | split at executed
#print axioms managedStep_callee

set_option maxHeartbeats 800000 in
/-- A successful call or construction is a step of an instruction that reads its link, and enters
    a method its link at the step's pc lists. -/
theorem step_callee {body : CIL.Method} {op : CIL.Instruction} {pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction} {callee : Nat}
    (h : step body op pc args frame stack m = .ok action)
    (enters : action.callee = some callee) :
    op.readsLink = true ∧ callee ∈ body.calleesAt pc := by
  unfold step observedCall intrinsicCall referenceCompareCall referenceSubtractCall newobjStep
    constructAggregate constructObject at h
  dsimp only at h
  split at h
  all_goals repeat' first
    | exact managedStep_callee h enters
    | unfold returnFrom at h
    | unfold localAllocation at h
    | unfold initializeSpanHome at h
    | solve | cases h; cases enters
    | solve |
      cases h
      simp only [FrameAction.callee, Option.some.injEq] at enters
      subst callee
      refine ⟨rfl, ?_⟩
      rw [CIL.Method.calleesAt, ‹body.linkAt pc = _›]
      first
      | (simp only [Option.map_some, Option.getD_some, CIL.Link.callees, List.mem_singleton]; done)
      | (simp only [Option.map_some, Option.getD_some, CIL.Link.callees]
         exact virtualTarget_mem ‹_›)
    | contradiction
    | solve | (obtain ⟨_, _, _, rfl, _⟩ := modelStep_frame h; cases enters)
    | (obtain ⟨_, _, h⟩ := except_bind_ok h)
    | split at h
#print axioms step_callee

/-- An indirect tail call cannot leave a caller continuation behind. -/
theorem step_managed_tail_action {body : CIL.Method} {signature : CIL.ManagedSignature}
    {pc : Nat} {args : List Value} {frame : Frame}
    {stack : List Value} {memory : Memory} {action : FrameAction}
    (executed : step body (.managed (.call signature true)) pc args frame stack memory =
      .ok action) :
    ∃ callee arguments result, action = .tailCall callee arguments result := by
  simp only [step, managedStep, Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first
    | solve | cases executed; exact ⟨_, _, _, rfl⟩
    | cases executed
    | split at executed
  all_goals simp_all
#print axioms step_managed_tail_action

/-- A step that stays in the frame resumes at the fallthrough of a continuing instruction or
    at one of its targets. -/
theorem step_next_target {body : CIL.Method} {op : CIL.Instruction} {pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {target : Nat} {stack' : List Value}
    {frame' : Frame} {m' : Memory}
    (h : step body op pc args frame stack m = .ok (.next target stack' frame' m')) :
    (op.continues = true ∧ target = pc + 1) ∨ target ∈ op.targets := by
  refine Decidable.byContradiction fun outside => ?_
  -- Moving only `target` fixes `op` and its fallthrough, so the same step would also resume
  -- at `target + 1`.
  let r : Nat → Nat := fun t => if t = target then target + 1 else t
  have same : op.relabel r = op := op.relabel_eq_self r fun t member =>
    ite_eq_right fun e => outside (.inr (by rw [← e]; exact member))
  have moved := step_relabel op body body r pc pc args frame stack m _
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun continues => ite_eq_right fun e => outside (.inl ⟨continues, e.symm⟩)⟩ h
  rw [same, h] at moved
  simp only [FrameAction.relabel, Except.ok.injEq, FrameAction.next.injEq] at moved
  have : r target = target + 1 := ite_eq_left rfl
  omega

/-- A `call` only ever enters the method its link names, never as a construction: under a `tail.`
    prefix it retires the frame, and otherwise it calls and continues. A call whose pc states no
    link runs its runtime model, which continues at the next pc; only a span constructor run in
    place changes the frame. -/
theorem step_call_action {body : CIL.Method} {method : CIL.Extraction.MethodRef}
    {prefixes : CIL.CallPrefixes} {pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body (.call method prefixes) pc args frame stack m = .ok action) :
    (∃ callee, body.linkAt pc = some (.direct callee) ∧
      if prefixes.tail then ∃ arguments updated, action = .tailCall callee arguments updated
      else ∃ arguments rest m', action = .call callee arguments rest m') ∨
    (body.linkAt pc = none ∧ prefixes.tail = false ∧
      ∃ values final changed, action = .next (pc + 1) values changed final) := by
  unfold step observedCall at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' (first | contradiction | split at h)
  all_goals first
    | (cases h; exact .inl ⟨_, by assumption, by simp_all⟩)
    | (obtain ⟨_, _, _, rfl, _⟩ := modelStep_frame (model := Extraction.runtimeModel
          body.environment .call method) (body := body) (pc := pc) (frame := frame)
          (stack := stack) (memory := m) h
       exact .inr ⟨by assumption, by simp_all, _, _, _, rfl⟩)
#print axioms step_call_action

/-- A construction under an `.aggregate` link enters the constructor the link names with a
    temporary, never as a plain call. -/
theorem step_newobj_aggregate_action {body : CIL.Method} {constructor : CIL.Extraction.MethodRef}
    {callee pc : Nat} {size : Fin (2^64)} {args : List Value} {frame : Frame}
    {stack : List Value} {m : Memory} {action : FrameAction}
    (linked : body.linkAt pc = some (.aggregate callee size))
    (h : step body (.newobj constructor) pc args frame stack m = .ok action) :
    ∃ arguments rest frame' temporary kind m',
      action = .construct callee arguments rest frame' temporary kind m' := by
  unfold step newobjStep constructAggregate at h
  simp only [linked, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' (first | contradiction | split at h)
  all_goals (cases h; exact ⟨_, _, _, _, _, _, rfl⟩)
#print axioms step_newobj_aggregate_action

end CIL.Safety
