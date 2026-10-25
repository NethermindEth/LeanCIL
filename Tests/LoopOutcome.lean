import CIL.Safety.LoopOutcome

namespace Tests.LoopOutcome

open CIL.Safety

/-! The normal-only loop rules are the `none` instances of the outcome rules. -/

example {α : Type} (program : CIL.Program) (method : Nat) (args : List Value)
    (configuration : α → LoopState) (invariant : α → Prop) (measure : α → Nat)
    (post : Memory → List Value → Prop)
    (progress : ∀ state, invariant state →
      (∀ next, invariant next → measure next < measure state →
        LoopTerminates program method args post (configuration next)) →
      LoopTerminates program method args post (configuration state))
    (state : α) (valid : invariant state) :
    LoopTerminates program method args post (configuration state) :=
  loop_outcome_induction program method args configuration invariant measure post none progress state valid

example {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value} {frame : Frame} {memory updated : Memory}
    {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      LoopTerminates program method args post ⟨pc + 1, frame, values ++ rest, final⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  loop_outcome_call (raises := none) holds.outcomes input methodFound instructionFound stepped encoded permitted rfl
    continuation

example (program : CIL.Program) (method : Nat) (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Memory → List Value → Prop) :
    EnsuresOutcome program method pre post (fun _ _ => none) ↔ Ensures program method pre post := .rfl

/-! Unsupported execution, invalid state, fuel exhaustion, normal return and another exception never discharge an expected one. -/

@[cil_code] def stuck : CIL.Method := { returnsValue := false, locals := [], code := [.unsupported "fixture"] }
@[cil_code] def spin : CIL.Method := { returnsValue := false, locals := [], code := [.branch 0] }
@[cil_code] def done : CIL.Method := { returnsValue := false, locals := [], code := [.ret] }
@[cil_code] def other : CIL.Method := { returnsValue := false, locals := [], code := [.throw "System.ArgumentException"] }

variable (post : Memory → List Value → Prop) (frame : Frame) (m : Memory)

example : ¬ LoopOutcome [stuck] 0 [] post (some "System.InvalidOperationException") ⟨0, frame, [], m⟩ :=
  loop_outcome_some_refuted (fuel := 1)
    (outcome := .error ⟨0, 0, .unsupported "Not a memory instruction"⟩) rfl
    (by simp [Settled]) (by rintro _ ⟨⟩; simp)

/-- A pc past the body is invalid state. -/
example : ¬ LoopOutcome [stuck] 0 [] post (some "System.InvalidOperationException") ⟨1, frame, [], m⟩ :=
  loop_outcome_some_refuted (fuel := 1) (outcome := .error ⟨0, 1, .invalidState⟩) rfl (by simp [Settled]) (by rintro _ ⟨⟩; simp)

/-- A method index outside the program is invalid state. -/
example : ¬ LoopOutcome [] 0 [] post (some "System.InvalidOperationException") ⟨0, frame, [], m⟩ :=
  loop_outcome_some_refuted (fuel := 1) (outcome := .error ⟨0, 0, .invalidState⟩) rfl (by simp [Settled]) (by rintro _ ⟨⟩; simp)

example : ¬ LoopOutcome [other] 0 [] post (some "System.InvalidOperationException") ⟨0, frame, [], m⟩ :=
  loop_outcome_some_refuted (fuel := 1) (outcome := .error ⟨0, 0, .thrown "System.ArgumentException"⟩) rfl (by simp [Settled]) (by rintro _ ⟨⟩; simp)

example : ¬ LoopOutcome [done] 0 [] post (some "System.InvalidOperationException") ⟨0, frame, [], m⟩ :=
  loop_outcome_some_refuted (fuel := 1) (outcome := .ok (leaveFrame frame m, [])) rfl trivial (by rintro _ ⟨⟩)

theorem spin_exhausts (fuel : Nat) :
    run [spin] fuel 0 0 [] frame [] m = .error ⟨0, 0, .fuelExhausted⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact (show run [spin] (fuel + 1) 0 0 [] frame [] m = run [spin] fuel 0 0 [] frame [] m from rfl).trans ih

example : ¬ LoopOutcome [spin] 0 [] post (some "System.InvalidOperationException") ⟨0, frame, [], m⟩ := by
  rintro ⟨fuel, fault, ran, thrown⟩
  change run [spin] fuel 0 0 [] frame [] m = _ at ran
  rw [spin_exhausts] at ran
  cases ran
  simp at thrown

/-- The method-level outcome inherits the same exactness. -/
example : ¬ EnsuresOutcome [spin] 0 (fun args initial => args = [] ∧ initial = m) (fun _ _ _ _ => True)
    (fun _ _ => some "System.InvalidOperationException") := by
  intro holds
  obtain ⟨fuel, fault, ran, thrown⟩ := holds [] m ⟨rfl, rfl⟩
  change run [spin] fuel 0 0 [] _ [] m = _ at ran
  rw [spin_exhausts] at ran
  cases ran
  simp at thrown

end Tests.LoopOutcome
