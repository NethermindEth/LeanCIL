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
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Instruction}
    {args stack arguments rest : List Value} {frame : Frame} {memory updated : Memory}
    {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (continuation : ∀ final output, CallResult c program callee input updated final output →
      LoopTerminates program method args post ⟨pc + 1, frame, c.results output ++ rest, final⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  loop_outcome_call (raises := none) holds.outcomes input methodFound instructionFound stepped encoded permitted rfl
    continuation

example (program : CIL.Program) (method : Nat) (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Memory → List Value → Prop) :
    EnsuresOutcome program method pre post (fun _ _ => none) ↔ Ensures program method pre post := .rfl

/-! Unsupported execution, invalid state, fuel exhaustion, normal return and another exception
    never discharge an expected one. All but unsupported execution also refute it; the model
    does not cover a run that reaches a hole. -/

@[cil_code] def stuck : CIL.Method :=
  { returnsValue := false, locals := [], code := [.unadmitted 0] }
@[cil_code] def spin : CIL.Method := { returnsValue := false, locals := [], code := [.br 0] }
@[cil_code] def done : CIL.Method := { returnsValue := false, locals := [], code := [.ret] }
@[cil_code] def other : CIL.Method :=
  { returnsValue := false, locals := [], code := [.throw (some .argument)] }

variable (post : Memory → List Value → Prop) (frame : Frame) (m : Memory)

/-- The hole's fault is not settled, so `loop_outcome_some_refuted` takes no run that reaches
    it. -/
theorem stuck_not_settled :
    run [stuck] 1 0 0 [] frame [] m = .error ⟨0, 0, .unsupported "Opcode not admitted"⟩ ∧
      ¬ Settled (.error ⟨0, 0, .unsupported "Opcode not admitted"⟩ :
        Except LocatedFault (Memory × List Value)) :=
  ⟨rfl, by decide⟩
#print axioms stuck_not_settled

/-- A pc past the body is invalid state. -/
example : ¬ LoopOutcome [stuck] 0 [] post (some .invalidOperation) ⟨1, frame, [], m⟩ :=
  loop_outcome_some_refuted (fuel := 1) (outcome := .error ⟨0, 1, .invalidState⟩) rfl (by simp [Settled]) (by rintro _ ⟨⟩; simp)

/-- A method index outside the program is invalid state. -/
example : ¬ LoopOutcome [] 0 [] post (some .invalidOperation) ⟨0, frame, [], m⟩ :=
  loop_outcome_some_refuted (fuel := 1) (outcome := .error ⟨0, 0, .invalidState⟩) rfl (by simp [Settled]) (by rintro _ ⟨⟩; simp)

example : ¬ LoopOutcome [other] 0 [] post (some .invalidOperation) ⟨0, frame, [], m⟩ :=
  loop_outcome_some_refuted (fuel := 1) (outcome := .error ⟨0, 0, .thrown .argument⟩) rfl
    (by simp [Settled]) (by rintro _ ⟨⟩; simp)

example : ¬ LoopOutcome [done] 0 [] post (some .invalidOperation) ⟨0, frame, [], m⟩ :=
  loop_outcome_some_refuted (fuel := 1) (outcome := .ok (leaveFrame frame m, [])) rfl trivial (by rintro _ ⟨⟩)

theorem spin_exhausts (fuel : Nat) :
    run [spin] fuel 0 0 [] frame [] m = .error ⟨0, 0, .fuelExhausted⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact (show run [spin] (fuel + 1) 0 0 [] frame [] m = run [spin] fuel 0 0 [] frame [] m from rfl).trans ih

example : ¬ LoopOutcome [spin] 0 [] post (some .invalidOperation) ⟨0, frame, [], m⟩ := by
  rintro ⟨fuel, fault, ran, thrown⟩
  change run [spin] fuel 0 0 [] frame [] m = _ at ran
  rw [spin_exhausts] at ran
  cases ran
  simp at thrown

/-- The method-level outcome inherits the same exactness. -/
example : ¬ EnsuresOutcome [spin] 0 (fun args initial => args = [] ∧ initial = m) (fun _ _ _ _ => True)
    (fun _ _ => some .invalidOperation) := by
  intro holds
  obtain ⟨fuel, fault, ran, thrown⟩ := holds [] m ⟨rfl, rfl⟩
  change run [spin] fuel 0 0 [] _ [] m = _ at ran
  rw [spin_exhausts] at ran
  cases ran
  simp at thrown

/-! A loop that never exits refutes a contract that promises a return. A run that exhausts one
    budget and returns from a larger one does not diverge, and neither does a run that reaches a
    hole. -/

/-- Promises a return from any memory, which `done` meets and `spin` does not. -/
def returns : MethodContract Unit :=
  { args := fun _ => [], pre := fun _ _ => True, footprint := fun _ => [],
    post := fun _ _ _ _ => True }

/-- Every budget exhausts `spin` from any memory. -/
theorem spin_diverges : Diverges [spin] 0 [] m := fun fuel =>
  ⟨⟨0, 0, .fuelExhausted⟩,
    by change run [spin] fuel 0 0 [] _ [] m = _; exact spin_exhausts _ m fuel, rfl⟩
#print axioms spin_diverges

/-- Divergence refutes the contract, and so its negation holds. -/
theorem spin_refuted : returns.Refuted [spin] 0 ∧ ¬ returns.Holds [spin] 0 :=
  let refuted : returns.Refuted [spin] 0 :=
    .of_diverges (input := ()) (initial := Memory.empty) trivial (spin_diverges Memory.empty)
  ⟨refuted, refuted.not_holds⟩
#print axioms spin_refuted

/-- `done` exhausts the empty budget and returns from one step, so it does not diverge. -/
theorem done_not_diverges :
    invoke [done] 0 0 [] Memory.empty = .error ⟨0, 0, .fuelExhausted⟩ ∧
      ¬ Diverges [done] 0 [] Memory.empty := by
  refine ⟨rfl, fun diverges => ?_⟩
  obtain ⟨fault, ran, -⟩ := diverges 1
  rw [(rfl : invoke [done] 1 0 [] Memory.empty = .ok _)] at ran
  cases ran
#print axioms done_not_diverges

/-- The hole's fault is stable, so no budget beyond it exhausts `stuck`. -/
theorem stuck_not_diverges : ¬ Diverges [stuck] 0 [] Memory.empty := by
  intro diverges
  obtain ⟨fault, ran, exhausted⟩ := diverges 1
  rw [(rfl : invoke [stuck] 1 0 [] Memory.empty = .error _)] at ran
  cases ran
  simp at exhausted
#print axioms stuck_not_diverges

end Tests.LoopOutcome
