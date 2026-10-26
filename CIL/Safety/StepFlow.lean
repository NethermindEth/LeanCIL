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
  | .call method _ | .newVector256 method _ | .newAggregate method _ _ => [method]
  | _ => []

end CIL

namespace CIL.Safety

/-- The method an action enters, if any. -/
def FrameAction.callee : FrameAction → Option Nat
  | .call callee .. | .construct callee .. => some callee
  | _ => none

set_option maxHeartbeats 800000 in
/-- Only `.call`, `.newVector256` and `.newAggregate` enter a method, and each enters the
    one it names. -/
theorem step_callee {body : CIL.Method} {op : CIL.Op} {pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body op pc args frame stack m = .ok action) : action.callee = op.callees.head? := by
  cases op <;> unfold step at h
  all_goals dsimp only at h
  all_goals split at h
  all_goals
    (try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.mapError] at h)
    repeat' (first | contradiction | split at h)
  all_goals (try (cases h; first | rfl | (cases op <;>
    simp_all [Op.callees, FrameAction.callee]); done))
  all_goals done

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
