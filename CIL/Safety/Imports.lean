import CIL.Safety.OutcomeContract

/-!
# Imported callees

A caller proved over every program that links its own depends on an imported callee only
through the callee's contract. `Links base linked` says `linked` appends methods after
`base`; any run of the checked interpreter that never faults `invalidState` (the fault a
missing method gives) has the same result in every linked program, so method and outcome
contracts transfer. `HoldsGiven` states a claim that needs the imports' contracts.
-/

namespace CIL.Safety

/-- Import slot `j` of `base`: past every extracted method, so `base` has no body there. -/
def importIndex (base : CIL.Program) (j : Nat) : Nat := base.length + j

/-- An import slot has no body in the program that declares it. -/
theorem importIndex_unlinked (base : CIL.Program) (j : Nat) : base[importIndex base j]? = none :=
  List.getElem?_eq_none_iff.mpr (by simp [importIndex])

/-- `linked` keeps every method of `base` at its index and may append more after them. -/
def Links (base linked : CIL.Program) : Prop := ∃ rest, linked = base ++ rest

theorem Links.refl (base : CIL.Program) : Links base base := ⟨[], (List.append_nil base).symm⟩

theorem Links.trans {first middle last : CIL.Program} :
    Links first middle → Links middle last → Links first last
  | ⟨left, hl⟩, ⟨right, hr⟩ => ⟨left ++ right, by rw [hr, hl, List.append_assoc]⟩

/-- A method of `base` is found at the same index in every program that links it. -/
theorem Links.found {base linked : CIL.Program} {index : Nat} {body : CIL.Method}
    (links : Links base linked)
    (found : base[index]? = some body) : linked[index]? = some body := by
  obtain ⟨rest, rfl⟩ := links
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  rw [List.getElem?_append_left bound]
  exact found

/-- No `invalidState` fault, the only fault a missing method produces. -/
def NoInvalidState (outcome : Except LocatedFault α) : Prop :=
  ∀ fault, outcome = .error fault → fault.fault ≠ .invalidState

/-- A stopped state other than `invalidState`, the only fault a missing method produces. -/
def ResolvedState (outcome : Except FaultState α) : Prop :=
  ∀ state, outcome = .error state → state.location.fault ≠ .invalidState

/-- A resumption that agrees on every resumed state gives the same outcome. -/
private theorem resume_extend {x : Except FaultState β} {k k' : β → Except FaultState γ}
    {outcome : Except FaultState γ} (ran : x >>= k = outcome)
    (resumed : ∀ value, k value = outcome → k' value = outcome) : x >>= k' = outcome := by
  cases x with
  | error state => exact ran
  | ok value => exact resumed value ran

/-- Handlers pass an invalid state. -/
private theorem recover_invalid {method : Nat} {body : CIL.Method} {pc : Nat} {frame : Frame}
    {memory : Memory} {state : FaultState} (invalid : state.location.fault = .invalidState) :
    recover method body pc frame memory state = .error state := by
  unfold recover
  split
  · rfl
  · split <;> simp_all

/-- A run that never stops `invalidState` stops in the same state or returns the same result in
    every linked program. -/
theorem runFaulting_extend {base linked : CIL.Program} (links : Links base linked)
    (fuel method pc : Nat) (args : List Value) (frame : Frame) (stack : List Value)
    (memory : Memory) (outcome : Except FaultState (Memory × List Value))
    (resolved : ResolvedState outcome)
    (h : runFaulting (base[·]?) fuel method pc args frame stack memory = outcome) :
    runFaulting (linked[·]?) fuel method pc args frame stack memory = outcome := by
  induction fuel generalizing method pc args frame stack memory outcome with
  | zero => exact h
  | succ fuel ih =>
    rw [runFaulting] at h ⊢
    cases hb : base[method]? with
    | none =>
      simp only [hb] at h
      exact absurd rfl (resolved _ h.symm)
    | some body =>
      simp only [hb, links.found hb] at h ⊢
      cases ho : body.code[pc]? with
      | none =>
        simp only [ho] at h
        exact absurd rfl (resolved _ h.symm)
      | some op =>
        simp only [ho] at h ⊢
        cases hs : step body op pc args frame stack memory with
        | error fault =>
          simp only [hs] at h ⊢
          exact resume_extend h fun ⟨_, _, _, _⟩ resumed => ih _ _ _ _ _ _ _ resolved resumed
        | ok action =>
          simp only [hs] at h ⊢
          cases action with
          | next target values nextFrame updated => exact ih _ _ _ _ _ _ _ resolved h
          | raise location object nextFrame updated =>
            exact resume_extend h fun ⟨_, _, _, _⟩ resumed => ih _ _ _ _ _ _ _ resolved resumed
          | returned values updated => exact h
          | tailCall callee arguments updated =>
            cases hc : base[callee]? with
            | none =>
              simp only [hc] at h
              exact absurd rfl (resolved _ h.symm)
            | some child =>
              simp only [hc, links.found hc] at h ⊢
              split
              · simpa [*] using h
              · rename_i differs
                simp only [differs] at h
                exact resume_extend h fun _ checked =>
                  resume_extend checked fun ⟨_, _⟩ entered => ih _ _ _ _ _ _ _ resolved entered
          | call callee arguments rest updated =>
            cases hc : base[callee]? with
            | none =>
              simp only [hc] at h
              exact absurd rfl (resolved _ h.symm)
            | some child =>
              simp only [hc, links.found hc] at h ⊢
              refine resume_extend h fun ⟨childFrame, childMemory⟩ entered => ?_
              cases hr :
                  runFaulting (base[·]?) fuel callee 0 arguments childFrame [] childMemory with
              | ok childResult =>
                obtain ⟨final, values⟩ := childResult
                rw [ih callee 0 arguments childFrame [] childMemory (.ok (final, values))
                  (fun _ h => nomatch h) hr]
                simp only [hr] at entered
                exact ih _ _ _ _ _ _ _ resolved entered
              | error state =>
                simp only [hr] at entered
                by_cases invalid : state.location.fault = .invalidState
                · rw [recover_invalid (by simpa [FaultState.unwind] using invalid)] at entered
                  simp only [Bind.bind, Except.bind] at entered
                  exact absurd (by simpa [FaultState.unwind] using invalid)
                    (resolved _ entered.symm)
                · rw [ih callee 0 arguments childFrame [] childMemory (.error state)
                    (fun _ same => by cases same; exact invalid) hr]
                  exact resume_extend entered fun ⟨_, _, _, _⟩ resumed =>
                    ih _ _ _ _ _ _ _ resolved resumed
          | construct callee arguments rest parentFrame temporary kind updated =>
            cases hc : base[callee]? with
            | none =>
              simp only [hc] at h
              exact absurd rfl (resolved _ h.symm)
            | some child =>
              simp only [hc, links.found hc] at h ⊢
              refine resume_extend h fun ⟨childFrame, childMemory⟩ entered => ?_
              cases hr :
                  runFaulting (base[·]?) fuel callee 0 arguments childFrame [] childMemory with
              | ok childResult =>
                obtain ⟨final, values⟩ := childResult
                rw [ih callee 0 arguments childFrame [] childMemory (.ok (final, values))
                  (fun _ h => nomatch h) hr]
                simp only [hr] at entered ⊢
                split
                · simpa [*] using entered
                · rename_i empty
                  simp only [empty] at entered
                  exact resume_extend entered fun _ loaded => ih _ _ _ _ _ _ _ resolved loaded
              | error state =>
                simp only [hr] at entered
                by_cases invalid : state.location.fault = .invalidState
                · rw [recover_invalid (by simpa [FaultState.unwind] using invalid)] at entered
                  simp only [Bind.bind, Except.bind] at entered
                  exact absurd (by simpa [FaultState.unwind] using invalid)
                    (resolved _ entered.symm)
                · rw [ih callee 0 arguments childFrame [] childMemory (.error state)
                    (fun _ same => by cases same; exact invalid) hr]
                  exact resume_extend entered fun ⟨_, _, _, _⟩ resumed =>
                    ih _ _ _ _ _ _ _ resolved resumed

#print axioms runFaulting_extend

/-- A run that never faults `invalidState` gives the same result in every linked program. -/
theorem run_extend {base linked : CIL.Program} (links : Links base linked) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (outcome : Except LocatedFault (Memory × List Value)) (resolved : NoInvalidState outcome)
    (h : run base fuel method pc args frame stack memory = outcome) :
    run linked fuel method pc args frame stack memory = outcome := by
  unfold run runWith at h ⊢
  cases ran : runFaulting (base[·]?) fuel method pc args frame stack memory with
  | ok result =>
    rw [runFaulting_extend links _ _ _ _ _ _ _ (.ok result) (fun _ h => nomatch h) ran]
    simpa [ran] using h
  | error state =>
    rw [ran] at h
    subst outcome
    rw [runFaulting_extend links _ _ _ _ _ _ _ (.error state)
      (fun _ same => by cases same; exact resolved _ rfl) ran]

/-- `run_extend` from a method entry. -/
theorem invoke_extend {base linked : CIL.Program} (links : Links base linked) (fuel method : Nat)
    (args : List Value) (memory : Memory) (outcome : Except LocatedFault (Memory × List Value))
    (resolved : NoInvalidState outcome) (h : invoke base fuel method args memory = outcome) :
    invoke linked fuel method args memory = outcome := by
  cases hb : base[method]? with
  | none =>
    simp only [invoke_eq, hb] at h
    exact absurd rfl (resolved _ h.symm)
  | some body =>
    have hl := links.found hb
    cases hc : (args.mapM (checkedValue memory)).mapError
        (fun fault => (⟨method, 0, fault⟩ : LocatedFault)) with
    | error fault =>
      simp only [invoke_eq, hb, hl, hc, Bind.bind, Except.bind] at h ⊢
      exact h
    | ok checked =>
      cases he : (enterFrame body checked memory).mapError
          (fun fault => (⟨method, 0, fault⟩ : LocatedFault)) with
      | error fault =>
        simp only [invoke_eq, hb, hl, hc, he, Bind.bind, Except.bind] at h ⊢
        exact h
      | ok entered =>
        obtain ⟨frame, entered⟩ := entered
        simp only [invoke_eq, hb, hl, hc, he, Bind.bind, Except.bind] at h ⊢
        exact run_extend links fuel method 0 checked frame [] entered outcome resolved h

/-- A raised exception is not `invalidState`, so it is raised in every linked program. -/
theorem Raises.extend {base linked : CIL.Program} {method : Nat} {args : List Value}
    {memory : Memory} {exception : ExceptionType}
    (raised : Raises base method args memory exception)
    (links : Links base linked) :
    Raises linked method args memory exception := by
  obtain ⟨fuel, fault, invoked, thrown⟩ := raised
  refine ⟨fuel, fault, invoke_extend links fuel method args memory _ ?_ invoked, thrown⟩
  intro located same
  cases same
  rw [thrown]
  exact nofun

/-- A contract proved on `base` holds at the same index in every program that links it. -/
theorem MethodContract.Holds.extend {Input Output : Type} {c : MethodContract Input Output}
    {base linked : CIL.Program} {method : Nat} (holds : c.Holds base method)
    (links : Links base linked) :
    c.Holds linked method := fun input initial permitted =>
  let ⟨fuel, result, invoked, framed, returns⟩ := holds input initial permitted
  ⟨fuel, result, invoke_extend links _ _ _ _ _ (fun _ h => nomatch h) invoked,
    framed, returns⟩

/-- Both outcomes transfer: a normal return as for `MethodContract`, a raise by `Raises.extend`. -/
theorem OutcomeContract.Holds.extend {Input Output : Type} {c : OutcomeContract Input Output}
    {base linked : CIL.Program} {method : Nat} (holds : c.Holds base method)
    (links : Links base linked) :
    c.Holds linked method := by
  intro input initial permitted
  have outcome := holds input initial permitted
  revert outcome
  cases c.raises input initial with
  | some exception => exact fun raised => raised.extend links
  | none =>
    exact fun ⟨fuel, final, values, invoked, framed, returns⟩ =>
      ⟨fuel, final, values, invoke_extend links _ _ _ _ _ (fun _ h => nomatch h) invoked,
        framed, returns⟩

/-- A call to a method the program lacks, such as an unlinked import, faults `invalidState`
    at the call. -/
theorem run_call_unlinked {program : CIL.Program} {fuel method pc callee : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (missing : program[callee]? = none) :
    run program (fuel + 1) method pc args frame stack memory =
      .error ⟨method, pc, .invalidState⟩ := by
  simp only [run, runWith, runFaulting, methodFound, instructionFound, stepped, missing,
    Except.mapError]

/-- Invoking a method the program lacks faults `invalidState` at its entry. -/
theorem invoke_unlinked {program : CIL.Program} {fuel method : Nat} {args : List Value}
    {memory : Memory}
    (missing : program[method]? = none) :
    invoke program fuel method args memory = .error ⟨method, 0, .invalidState⟩ := by
  simp only [invoke_eq, missing]

/-- `claim` holds in every program that links `base` and whose imports meet `imports`. -/
def HoldsGiven (base : CIL.Program) (imports claim : CIL.Program → Prop) : Prop :=
  ∀ linked, Links base linked → imports linked → claim linked

/-- A concrete linked program whose imports meet their contracts satisfies the claim. -/
theorem HoldsGiven.discharge {base linked : CIL.Program} {imports claim : CIL.Program → Prop}
    (given : HoldsGiven base imports claim) (links : Links base linked) (met : imports linked) :
    claim linked :=
  given linked links met

/-- A claim that holds in every linked program needs no import. -/
theorem HoldsGiven.closed {base : CIL.Program} {imports claim : CIL.Program → Prop}
    (proved : ∀ linked, Links base linked → claim linked) : HoldsGiven base imports claim :=
  fun linked links _ => proved linked links

#print axioms run_extend
#print axioms invoke_extend
#print axioms Raises.extend
#print axioms MethodContract.Holds.extend
#print axioms OutcomeContract.Holds.extend
#print axioms run_call_unlinked
#print axioms invoke_unlinked

end CIL.Safety
