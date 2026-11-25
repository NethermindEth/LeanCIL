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

/-- A stopped state or success that more fuel cannot change: anything but fuel exhaustion. -/
def StableState (outcome : Except FaultState α) : Prop :=
  match outcome with
  | .ok _ => True
  | .error state => state.location.fault ≠ .fuelExhausted

/-- A resumption that agrees on every resumed state gives the same outcome. -/
private theorem resume_mono {x : Except FaultState β} {k k' : β → Except FaultState γ}
    {outcome : Except FaultState γ} (ran : x >>= k = outcome)
    (resumed : ∀ value, k value = outcome → k' value = outcome) : x >>= k' = outcome := by
  cases x with
  | error state => exact ran
  | ok value => exact resumed value ran

/-- Handlers never take a run out of fuel. -/
theorem recover_exhausted {method : Nat} {body : CIL.Method} {pc : Nat} {frame : Frame}
    {memory : Memory} {state : FaultState} (exhausted : state.location.fault = .fuelExhausted) :
    recover method body pc frame memory state = .error state := by
  unfold recover
  split
  · rfl
  · split <;> simp_all

/-- Adding fuel to a run with a stable outcome gives the same stopped state or success. -/
theorem runFaulting_mono (lookup : Nat → Option CIL.Method) (fuel extra method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (outcome : Except FaultState (Memory × List Value)) (ready : StableState outcome)
    (h : runFaulting lookup fuel method pc args frame stack memory = outcome) :
    runFaulting lookup (fuel + extra) method pc args frame stack memory = outcome := by
  induction fuel generalizing method pc args frame stack memory outcome with
  | zero =>
    subst outcome
    simp [runFaulting, StableState] at ready
  | succ fuel ih =>
    rw [Nat.succ_add]
    rw [runFaulting] at h ⊢
    cases hb : lookup method with
    | none => simpa [hb] using h
    | some body =>
      simp only [hb] at h ⊢
      cases ho : body.code[pc]? with
      | none => simpa [ho] using h
      | some op =>
        simp only [ho] at h ⊢
        cases hs : step body op pc args frame stack memory with
        | error fault =>
          simp only [hs] at h ⊢
          exact resume_mono h fun ⟨_, _, _, _⟩ resumed => ih _ _ _ _ _ _ _ ready resumed
        | ok action =>
          simp only [hs] at h ⊢
          cases action with
          | next target values nextFrame updated => exact ih _ _ _ _ _ _ _ ready h
          | raise location object nextFrame updated =>
            exact resume_mono h fun ⟨_, _, _, _⟩ resumed => ih _ _ _ _ _ _ _ ready resumed
          | returned values updated => exact h
          | tailCall callee arguments updated =>
            cases hc : lookup callee with
            | none => simpa [hc] using h
            | some child =>
              simp only [hc] at h ⊢
              split
              · simpa [*] using h
              · rename_i differs
                simp only [differs] at h
                exact resume_mono h fun _ checked =>
                  resume_mono checked fun ⟨_, _⟩ entered => ih _ _ _ _ _ _ _ ready entered
          | call callee arguments rest updated =>
            cases hc : lookup callee with
            | none => simpa [hc] using h
            | some child =>
              simp only [hc] at h ⊢
              refine resume_mono h fun ⟨childFrame, childMemory⟩ entered => ?_
              cases hr : runFaulting lookup fuel callee 0 arguments childFrame [] childMemory with
              | ok childResult =>
                obtain ⟨final, values⟩ := childResult
                rw [ih callee 0 arguments childFrame [] childMemory (.ok (final, values)) trivial hr]
                simp only [hr] at entered
                exact ih _ _ _ _ _ _ _ ready entered
              | error state =>
                simp only [hr] at entered
                by_cases exhausted : state.location.fault = .fuelExhausted
                · rw [recover_exhausted (by simpa [FaultState.unwind] using exhausted)] at entered
                  rw [← entered] at ready
                  exact absurd exhausted ready
                · rw [ih callee 0 arguments childFrame [] childMemory (.error state) exhausted hr]
                  exact resume_mono entered fun ⟨_, _, _, _⟩ resumed =>
                    ih _ _ _ _ _ _ _ ready resumed
          | construct callee arguments rest parentFrame temporary kind updated =>
            cases hc : lookup callee with
            | none => simpa [hc] using h
            | some child =>
              simp only [hc] at h ⊢
              refine resume_mono h fun ⟨childFrame, childMemory⟩ entered => ?_
              cases hr : runFaulting lookup fuel callee 0 arguments childFrame [] childMemory with
              | ok childResult =>
                obtain ⟨final, values⟩ := childResult
                rw [ih callee 0 arguments childFrame [] childMemory (.ok (final, values)) trivial hr]
                simp only [hr] at entered ⊢
                split
                · simpa [*] using entered
                · rename_i empty
                  simp only [empty] at entered
                  exact resume_mono entered fun _ loaded => ih _ _ _ _ _ _ _ ready loaded
              | error state =>
                simp only [hr] at entered
                by_cases exhausted : state.location.fault = .fuelExhausted
                · rw [recover_exhausted (by simpa [FaultState.unwind] using exhausted)] at entered
                  rw [← entered] at ready
                  exact absurd exhausted ready
                · rw [ih callee 0 arguments childFrame [] childMemory (.error state) exhausted hr]
                  exact resume_mono entered fun ⟨_, _, _, _⟩ resumed =>
                    ih _ _ _ _ _ _ _ ready resumed
#print axioms runFaulting_mono

/-- Adding fuel to a run with a stable outcome gives the same outcome. -/
theorem run_mono (program : CIL.Program) (fuel extra method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (outcome : Except LocatedFault (Memory × List Value))
    (ready : Stable outcome)
    (h : run program fuel method pc args frame stack memory = outcome) :
    run program (fuel + extra) method pc args frame stack memory = outcome := by
  unfold run runWith at h ⊢
  cases ran : runFaulting (program[·]?) fuel method pc args frame stack memory with
  | ok result =>
    rw [runFaulting_mono _ _ _ _ _ _ _ _ _ (.ok result) trivial ran]
    simpa [ran] using h
  | error state =>
    rw [ran] at h
    subst outcome
    rw [runFaulting_mono _ _ _ _ _ _ _ _ _ (.error state) ready ran]
#print axioms run_mono


theorem invoke_mono (program : CIL.Program) (fuel extra method : Nat)
    (args : List Value) (memory : Memory) (outcome : Except LocatedFault (Memory × List Value))
    (ready : Stable outcome) (h : invoke program fuel method args memory = outcome) :
    invoke program (fuel + extra) method args memory = outcome := by
  cases hb : program[method]? with
  | none => simpa [invoke_eq, hb] using h
  | some body =>
    cases ha : args.mapM (checkedValue memory) with
    | error fault => simpa [invoke_eq, hb, ha, Bind.bind, Except.bind, Except.mapError] using h
    | ok arguments =>
      cases he : enterFrame body arguments memory with
      | error fault => simpa [invoke_eq, hb, ha, he, Bind.bind, Except.bind,
                         Except.mapError] using h
      | ok entered =>
        obtain ⟨frame, updated⟩ := entered
        simp [invoke_eq, hb, ha, he, Bind.bind, Except.bind, Except.mapError] at h
        simpa [invoke_eq, hb, ha, he, Bind.bind, Except.bind, Except.mapError] using
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

/-- Two stable outcomes of the same invocation agree at any fuel budgets. This includes the
    interpreter stopping at an unsupported operation. -/
theorem invoke_unique {program : CIL.Program} {method left right : Nat} {args : List Value}
    {memory : Memory} {first second : Except LocatedFault (Memory × List Value)}
    (firstStable : Stable first) (secondStable : Stable second)
    (one : invoke program left method args memory = first)
    (other : invoke program right method args memory = second) :
    first = second := by
  have up := invoke_mono program left right method args memory first firstStable one
  have down := invoke_mono program right left method args memory second secondStable other
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
  · rw [← invoke_unique witnessSettled.stable settled.stable invoked ran]
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
