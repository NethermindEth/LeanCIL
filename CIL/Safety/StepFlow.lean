import CIL.Safety.Embedding.Step

/-!
# Step control flow

Where one checked step of `CIL.Safety.step` can go: the pc it resumes at and the method it
enters. These bound the control-flow graph of a method from its code alone, so region and
loop proofs can enumerate successors without stepping.
-/

namespace CIL

/-- Every method index an instruction calls or constructs with. -/
def Op.callees : Op → List Nat
  | .managed (.call _ catalog _) => catalog.map ManagedTarget.method
  | .call method _ | .tailCall method _ | .newVector256 method _
  | .newAggregate method _ _ => [method]
  | _ => []

end CIL

namespace CIL.Safety

/-- The method an action enters, if any. -/
def FrameAction.callee : FrameAction → Option Nat
  | .call callee .. | .tailCall callee .. | .construct callee .. => some callee
  | _ => none

/-- An indirect call can enter only a body named in its authenticated catalog. -/
theorem managedStep_callee {operation : CIL.ManagedOp} {pc : Nat} {frame : Frame}
    {stack : List Value} {memory : Memory} {action : FrameAction} {callee : Nat}
    (executed : managedStep operation pc frame stack memory = .ok action)
    (enters : action.callee = some callee) : callee ∈ (CIL.Op.managed operation).callees := by
  unfold managedStep at executed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  repeat' first
    | solve |
      cases executed
      simp only [FrameAction.callee, Option.some.injEq] at enters
      subst callee
      exact List.mem_map.mpr ⟨_, List.mem_of_find?_eq_some (by assumption), rfl⟩
    | solve | cases executed; cases enters
    | cases executed
    | split at executed
#print axioms managedStep_callee

set_option maxHeartbeats 800000 in
/-- A successful call or construction enters a method listed by its instruction. -/
theorem step_callee {body : CIL.Method} {op : CIL.Op} {pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction} {callee : Nat}
    (h : step body op pc args frame stack m = .ok action)
    (enters : action.callee = some callee) : callee ∈ op.callees := by
  cases op <;> unfold step at h
  all_goals dsimp only at h
  all_goals split at h
  all_goals repeat' first
    | exact managedStep_callee h enters
    | solve | cases h; cases enters
    | solve |
      cases h
      simp only [FrameAction.callee, Option.some.injEq] at enters
      subst callee
      simp only [Op.callees, List.mem_singleton]
    | contradiction
    | (obtain ⟨_, _, h⟩ := except_bind_ok h)
    | split at h
#print axioms step_callee

/-- An indirect tail call cannot leave a caller continuation behind. -/
theorem step_managed_tail_action {body : CIL.Method} {signature : CIL.ManagedSignature}
    {catalog : List CIL.ManagedTarget} {pc : Nat} {args : List Value} {frame : Frame}
    {stack : List Value} {memory : Memory} {action : FrameAction}
    (executed : step body (.managed (.call signature catalog true)) pc args frame stack memory =
      .ok action) :
    ∃ callee arguments result, action = .tailCall callee arguments result := by
  simp only [step, managedStep, observerCount, Bool.or_false,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Bool.true_eq, ite_true] at executed
  repeat' first
    | solve | cases executed; exact ⟨_, _, _, rfl⟩
    | cases executed
    | split at executed
  all_goals simp_all
#print axioms step_managed_tail_action

/-- A step that stays in the frame resumes at the fallthrough of a continuing instruction or
    at one of its targets. -/
theorem step_next_target {body : CIL.Method} {op : CIL.Op} {pc : Nat} {args : List Value}
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
    ⟨rfl, rfl, rfl, fun continues => ite_eq_right fun e => outside (.inl ⟨continues, e.symm⟩)⟩ h
  rw [same, h] at moved
  simp only [FrameAction.relabel, Except.ok.injEq, FrameAction.next.injEq] at moved
  have : r target = target + 1 := ite_eq_left rfl
  omega

/-- A call instruction only ever enters the method it names as a call, never as a
    construction. -/
theorem step_call_action {body : CIL.Method} {callee argc pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body (.call callee argc) pc args frame stack m = .ok action) :
    ∃ arguments rest m', action = .call callee arguments rest m' := by
  unfold step at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' (first | contradiction | split at h)
  all_goals (cases h; exact ⟨_, _, _, rfl⟩)

/-- A tail-call instruction requests frame retirement and exactly its named callee. -/
theorem step_tailCall_action {body : CIL.Method} {callee argc pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body (.tailCall callee argc) pc args frame stack m = .ok action) :
    ∃ arguments updated, action = .tailCall callee arguments updated := by
  unfold step at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' (first | contradiction | split at h)
  all_goals (cases h; exact ⟨_, _, rfl⟩)
#print axioms step_tailCall_action

/-- Vector and aggregate construction enter the constructor they name with a temporary, never
    as a plain call. -/
theorem step_newVector256_action {body : CIL.Method} {callee argc pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body (.newVector256 callee argc) pc args frame stack m = .ok action) :
    ∃ arguments rest frame' temporary kind m',
      action = .construct callee arguments rest frame' temporary kind m' := by
  unfold step at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' (first | contradiction | split at h)
  all_goals (cases h; exact ⟨_, _, _, _, _, _, rfl⟩)

theorem step_newAggregate_action {body : CIL.Method} {callee argc pc : Nat} {size}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body (.newAggregate callee argc size) pc args frame stack m = .ok action) :
    ∃ arguments rest frame' temporary kind m',
      action = .construct callee arguments rest frame' temporary kind m' := by
  unfold step at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' (first | contradiction | split at h)
  all_goals (cases h; exact ⟨_, _, _, _, _, _, rfl⟩)

end CIL.Safety
