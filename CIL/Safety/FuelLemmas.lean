import CIL.Safety.Execution

/-!
# More fuel never changes a stable outcome

Fuel only bounds how long the checked interpreter may run. Once a run succeeds or fails with any
fault other than `fuelExhausted`, giving it more fuel yields the same outcome (`run_mono`,
`invoke_mono`). Consequently a definite fault found at one fuel budget refutes success at every
budget (`invoke_fault_refutes_success`). Fuel exhaustion and `unsupported` faults are not
definite: the first stops a run early and the second marks an operation the model does not cover,
so neither is evidence about the method and no refutation lemma takes one (`Settled`).
`Counterexample` is the evidence a contract refutation carries: a settled outcome at some budget,
or exhaustion at every budget (`Diverges`).
-/

namespace CIL.Safety

/-- Whether a fault is an outcome of the method itself. Running out of fuel and an operation the
    model does not cover (`unsupported`) are not: a longer or a more complete run could go on. -/
@[simp] def ExecutionFault.definite : ExecutionFault → Bool
  | .arithmetic _ => true
  | .memory .. => true
  | .invalidState => true
  | .unsupported .. => false
  | .thrown _ => true
  | .fuelExhausted => false
  | .stackAllocationFailure .. => true
  | .allocationFailure .. => true

/-- An outcome that more fuel cannot change: a success, or any fault except running out of
    fuel. An `unsupported` fault is stable but not settled. -/
def Stable (outcome : Except LocatedFault α) : Prop :=
  match outcome with
  | .ok _ => True
  | .error fault => fault.fault ≠ .fuelExhausted

/-- An outcome that stands as evidence about the method: a success, or a definite fault. Every
    refutation lemma takes it, so none of them refutes anything from a run that reaches an
    `unsupported` operation. -/
def Settled (outcome : Except LocatedFault α) : Prop :=
  match outcome with
  | .ok _ => True
  | .error fault => fault.fault.definite ≠ false

instance (outcome : Except LocatedFault α) : Decidable (Settled outcome) :=
  match outcome with
  | .ok _ => isTrue trivial
  | .error fault => inferInstanceAs (Decidable (fault.fault.definite ≠ false))

/-- A settled outcome is stable: a definite fault is never fuel exhaustion. -/
theorem Settled.stable {outcome : Except LocatedFault α} (settled : Settled outcome) :
    Stable outcome := by
  cases outcome with
  | ok _ => trivial
  | error fault => exact fun exhausted => settled (by rw [exhausted]; rfl)

section

-- Every `run` case unfolds through these monad steps.
attribute [local simp] Bind.bind Except.bind Except.mapError

/-- Adding fuel to a run with a stable outcome gives the same outcome. -/
theorem run_mono (program : CIL.Program) (fuel extra method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (outcome : Except LocatedFault (Memory × List Value))
    (ready : Stable outcome)
    (h : run program fuel method pc args frame stack memory = outcome) :
    run program (fuel + extra) method pc args frame stack memory = outcome := by
  induction fuel generalizing method pc args frame stack memory outcome with
  | zero =>
    simp only [run] at h
    subst outcome
    simp [Stable] at ready
  | succ fuel ih =>
    cases hb : program[method]? with
    | none => simpa [Nat.succ_add, run, hb] using h
    | some body =>
      cases ho : body.code[pc]? with
      | none => simpa [Nat.succ_add, run, hb, ho] using h
      | some op =>
        cases hs : step body op pc args frame stack memory with
        | error fault =>
          simpa [Nat.succ_add, run, hb, ho, hs] using h
        | ok action =>
          cases action with
          | next target values nextFrame updated =>
            simp [run, hb, ho, hs] at h
            simpa [Nat.succ_add, run, hb, ho, hs] using
              ih method target args nextFrame values updated outcome ready h
          | returned values updated =>
            simpa [Nat.succ_add, run, hb, ho, hs] using h
          | tailCall callee arguments updated =>
            cases hc : program[callee]? with
            | none => simpa [Nat.succ_add, run, hb, ho, hs, hc] using h
            | some child =>
              cases returns : child.returnsValue != body.returnsValue with
              | true => simpa [Nat.succ_add, run, hb, ho, hs, hc, returns] using h
              | false =>
                cases check : arguments.mapM (checkedValue (leaveFrame frame updated)) with
                | error fault =>
                  simpa [Nat.succ_add, run, hb, ho, hs, hc, returns, check] using h
                | ok checked =>
                  cases enter : enterFrame child checked (leaveFrame frame updated) with
                  | error fault =>
                    simpa [Nat.succ_add, run, hb, ho, hs, hc, returns, check, enter] using h
                  | ok entered =>
                    obtain ⟨childFrame, childMemory⟩ := entered
                    simp [run, hb, ho, hs, hc, returns, check, enter] at h
                    simpa [Nat.succ_add, run, hb, ho, hs, hc, returns, check, enter] using
                      ih callee 0 checked childFrame [] childMemory outcome ready h
          | call callee arguments rest updated =>
            cases hc : program[callee]? with
            | none =>
              simpa [Nat.succ_add, run, hb, ho, hs, hc] using h
            | some child =>
              cases he : enterFrame child arguments updated with
              | error fault =>
                simpa [Nat.succ_add, run, hb, ho, hs, hc, he] using h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault =>
                  simp [run, hb, ho, hs, hc, he, hr] at h
                  have settled :
                      Stable (.error fault : Except LocatedFault (Memory × List Value)) := by
                    simpa [← h] using ready
                  have more :=
                    ih callee 0 arguments childFrame [] childMemory (.error fault) settled hr
                  simpa [Nat.succ_add, run, hb, ho, hs, hc, he, more] using h
                | ok childResult =>
                  obtain ⟨final, values⟩ := childResult
                  have more :=
                    ih callee 0 arguments childFrame [] childMemory (.ok (final, values)) trivial hr
                  simp [run, hb, ho, hs, hc, he, hr] at h
                  have parent :=
                    ih method (pc + 1) args frame (values ++ rest) final outcome ready h
                  simpa [Nat.succ_add, run, hb, ho, hs, hc, he, more] using parent
          | construct callee arguments rest parentFrame temporary kind updated =>
            cases hc : program[callee]? with
            | none =>
              simpa [Nat.succ_add, run, hb, ho, hs, hc] using h
            | some child =>
              cases he : enterFrame child arguments updated with
              | error fault =>
                simpa [Nat.succ_add, run, hb, ho, hs, hc, he] using h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases hr : run program fuel callee 0 arguments childFrame [] childMemory with
                | error fault =>
                  simp [run, hb, ho, hs, hc, he, hr] at h
                  have settled :
                      Stable (.error fault : Except LocatedFault (Memory × List Value)) := by
                    simpa [← h] using ready
                  have more :=
                    ih callee 0 arguments childFrame [] childMemory (.error fault) settled hr
                  simpa [Nat.succ_add, run, hb, ho, hs, hc, he, more] using h
                | ok childResult =>
                  obtain ⟨final, values⟩ := childResult
                  have more :=
                    ih callee 0 arguments childFrame [] childMemory (.ok (final, values)) trivial hr
                  cases values with
                  | cons value tail =>
                    simpa [Nat.succ_add, run, hb, ho, hs, hc, he, hr, more] using h
                  | nil =>
                    cases hv : loadLocal final (.bytes kind temporary) with
                    | error fault =>
                      simpa [Nat.succ_add, run, hb, ho, hs, hc, he, hr, more, hv] using h
                    | ok value =>
                      simp [run, hb, ho, hs, hc, he, hr, hv] at h
                      have parent :=
                        ih method (pc + 1) args parentFrame (value :: rest) final outcome ready h
                      simpa [Nat.succ_add, run, hb, ho, hs, hc, he, more, hv] using parent
#print axioms run_mono

end

theorem invoke_mono (program : CIL.Program) (fuel extra method : Nat)
    (args : List Value) (memory : Memory) (outcome : Except LocatedFault (Memory × List Value))
    (ready : Stable outcome) (h : invoke program fuel method args memory = outcome) :
    invoke program (fuel + extra) method args memory = outcome := by
  cases hb : program[method]? with
  | none => simpa [invoke, hb] using h
  | some body =>
    cases ha : args.mapM (checkedValue memory) with
    | error fault => simpa [invoke, hb, ha, Bind.bind, Except.bind, Except.mapError] using h
    | ok arguments =>
      cases he : enterFrame body arguments memory with
      | error fault => simpa [invoke, hb, ha, he, Bind.bind, Except.bind, Except.mapError] using h
      | ok entered =>
        obtain ⟨frame, updated⟩ := entered
        simp [invoke, hb, ha, he, Bind.bind, Except.bind, Except.mapError] at h
        simpa [invoke, hb, ha, he, Bind.bind, Except.bind, Except.mapError] using
          run_mono program fuel extra method 0 arguments frame [] updated outcome ready h

/-- A definite fault refutes successful execution for every fuel, not merely the concrete
    budget used to exhibit the fault. -/
theorem invoke_fault_refutes_success (program : CIL.Program) (observed method : Nat)
    (args : List Value) (memory : Memory) (fault : LocatedFault)
    (definite : fault.fault.definite ≠ false)
    (witness : invoke program observed method args memory = .error fault)
    (fuel : Nat) (result : Memory × List Value) :
    invoke program fuel method args memory ≠ .ok result := by
  intro success
  have failure :=
    invoke_mono program observed fuel method args memory (.error fault) (Settled.stable definite)
      witness
  have returned := invoke_mono program fuel observed method args memory (.ok result) trivial success
  rw [Nat.add_comm] at returned
  rw [failure] at returned
  cases returned

/-- Settled invocations agree at every fuel, so a computed settled run refutes a contract; a run
    that ends in fuel exhaustion or an `unsupported` fault is not settled, so this lemma takes
    none. -/
theorem invoke_unique {program : CIL.Program} {method left right : Nat} {args : List Value}
    {memory : Memory} {first second : Except LocatedFault (Memory × List Value)}
    (firstSettled : Settled first) (secondSettled : Settled second)
    (one : invoke program left method args memory = first)
    (other : invoke program right method args memory = second) :
    first = second := by
  have up := invoke_mono program left right method args memory first firstSettled.stable one
  have down := invoke_mono program right left method args memory second secondSettled.stable other
  rw [Nat.add_comm] at down
  exact up.symm.trans down

/-- Every fuel budget ends the run in fuel exhaustion: the method never terminates. One exhausted
    budget is no evidence of this, and a run that reaches an `unsupported` operation does not
    diverge, since that fault stays at every larger budget. -/
def Diverges (program : CIL.Program) (method : Nat) (args : List Value) (memory : Memory) :
    Prop :=
  ∀ fuel, ∃ fault, invoke program fuel method args memory = .error fault ∧
    fault.fault = .fuelExhausted

/-- Evidence that the run of `method` on `args` from `memory` ends as `violates` describes: a
    settled outcome at some fuel that `violates` holds of, or divergence. A run that reaches an
    operation the model does not cover, or one exhausted budget, is neither. -/
def Counterexample (program : CIL.Program) (method : Nat) (args : List Value) (memory : Memory)
    (violates : Except LocatedFault (Memory × List Value) → Prop) : Prop :=
  (∃ fuel outcome, invoke program fuel method args memory = outcome ∧ Settled outcome ∧
    violates outcome) ∨ Diverges program method args memory

/-- Every settled outcome of a counterexample's run is one `violates` holds of. -/
theorem Counterexample.violates {program : CIL.Program} {method fuel : Nat}
    {args : List Value} {memory : Memory}
    {violates : Except LocatedFault (Memory × List Value) → Prop}
    {outcome : Except LocatedFault (Memory × List Value)}
    (counter : Counterexample program method args memory violates)
    (settled : Settled outcome) (ran : invoke program fuel method args memory = outcome) :
    violates outcome := by
  rcases counter with ⟨observed, witness, invoked, witnessSettled, bad⟩ | diverges
  · rw [← invoke_unique witnessSettled settled invoked ran]
    exact bad
  · obtain ⟨fault, exhausted, kind⟩ := diverges fuel
    rw [ran] at exhausted
    subst exhausted
    simp [Settled, kind] at settled

#print axioms Settled.stable
#print axioms invoke_mono
#print axioms invoke_fault_refutes_success
#print axioms invoke_unique
#print axioms Counterexample.violates

end CIL.Safety
