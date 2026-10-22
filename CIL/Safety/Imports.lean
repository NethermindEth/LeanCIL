import CIL.Safety.OutcomeContract

/-! A caller proved over every program linking its own depends on an imported callee only through its contract. -/

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
    (links : Links base linked) (found : base[index]? = some body) : linked[index]? = some body := by
  obtain ⟨rest, rfl⟩ := links
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  rw [List.getElem?_append_left bound]
  exact found

/-- No `invalidState` fault, the only fault a missing method produces. -/
def NoInvalidState (outcome : Except LocatedFault α) : Prop :=
  ∀ fault, outcome = .error fault → fault.fault ≠ .invalidState

/-- A run that never faults `invalidState` gives the same result in every linked program. -/
theorem run_extend {base linked : CIL.Program} (links : Links base linked) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (outcome : Except LocatedFault (Memory × List Value)) (resolved : NoInvalidState outcome)
    (h : run base fuel method pc args frame stack memory = outcome) :
    run linked fuel method pc args frame stack memory = outcome := by
  induction fuel generalizing method pc args frame stack memory outcome with
  | zero => simpa only [run] using h
  | succ fuel ih =>
    cases hb : base[method]? with
    | none =>
      simp only [run, hb] at h
      exact absurd rfl (resolved _ h.symm)
    | some body =>
      have hl := links.found hb
      cases ho : body.code[pc]? with
      | none =>
        simp only [run, hb, ho] at h
        exact absurd rfl (resolved _ h.symm)
      | some op =>
        cases hs : step body op pc args frame stack memory with
        | error fault =>
          simp only [run, hb, hl, ho, hs, Bind.bind, Except.bind, Except.mapError] at h ⊢
          exact h
        | ok action =>
          cases action with
          | next target values nextFrame updated =>
            simp only [run, hb, hl, ho, hs, Bind.bind, Except.bind, Except.mapError] at h ⊢
            exact ih method target args nextFrame values updated outcome resolved h
          | returned values updated =>
            simp only [run, hb, hl, ho, hs, Bind.bind, Except.bind, Except.mapError] at h ⊢
            exact h
          | call callee arguments rest updated =>
            cases hc : base[callee]? with
            | none =>
              simp only [run, hb, ho, hs, hc, Bind.bind, Except.bind, Except.mapError] at h
              exact absurd rfl (resolved _ h.symm)
            | some child =>
              have hlc := links.found hc
              cases he : enterFrame child arguments updated with
              | error fault =>
                simp only [run, hb, hl, ho, hs, hc, hlc, he, Bind.bind, Except.bind, Except.mapError] at h ⊢
                exact h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases hr : run base fuel callee 0 arguments childFrame [] childMemory with
                | error fault =>
                  simp only [run, hb, ho, hs, hc, he, hr, Bind.bind, Except.bind, Except.mapError] at h
                  subst h
                  have more := ih callee 0 arguments childFrame [] childMemory _ resolved hr
                  simp only [run, hl, ho, hs, hlc, he, more, Bind.bind, Except.bind, Except.mapError]
                | ok childResult =>
                  obtain ⟨final, values⟩ := childResult
                  have more := ih callee 0 arguments childFrame [] childMemory (.ok (final, values)) (by intro _ h; cases h) hr
                  simp only [run, hb, ho, hs, hc, he, hr, Bind.bind, Except.bind, Except.mapError] at h
                  simp only [run, hl, ho, hs, hlc, he, more, Bind.bind, Except.bind, Except.mapError]
                  exact ih method (pc + 1) args frame (values ++ rest) final outcome resolved h
          | construct callee arguments rest parentFrame temporary kind updated =>
            cases hc : base[callee]? with
            | none =>
              simp only [run, hb, ho, hs, hc, Bind.bind, Except.bind, Except.mapError] at h
              exact absurd rfl (resolved _ h.symm)
            | some child =>
              have hlc := links.found hc
              cases he : enterFrame child arguments updated with
              | error fault =>
                simp only [run, hb, hl, ho, hs, hc, hlc, he, Bind.bind, Except.bind, Except.mapError] at h ⊢
                exact h
              | ok entered =>
                obtain ⟨childFrame, childMemory⟩ := entered
                cases hr : run base fuel callee 0 arguments childFrame [] childMemory with
                | error fault =>
                  simp only [run, hb, ho, hs, hc, he, hr, Bind.bind, Except.bind, Except.mapError] at h
                  subst h
                  have more := ih callee 0 arguments childFrame [] childMemory _ resolved hr
                  simp only [run, hl, ho, hs, hlc, he, more, Bind.bind, Except.bind, Except.mapError]
                | ok childResult =>
                  obtain ⟨final, values⟩ := childResult
                  have more := ih callee 0 arguments childFrame [] childMemory (.ok (final, values)) (by intro _ h; cases h) hr
                  simp only [run, hb, ho, hs, hc, he, hr, Bind.bind, Except.bind, Except.mapError] at h
                  simp only [run, hl, ho, hs, hlc, he, more, Bind.bind, Except.bind, Except.mapError]
                  cases hn : !values.isEmpty with
                  | true =>
                    simp only [hn, ite_true] at h
                    exact absurd rfl (resolved _ h.symm)
                  | false =>
                    simp only [hn] at h ⊢
                    cases hv : loadLocal final (.bytes kind temporary) with
                    | error fault =>
                      simp only [hv] at h ⊢
                      exact h
                    | ok value =>
                      simp only [hv] at h ⊢
                      exact ih method (pc + 1) args parentFrame (value :: rest) final outcome resolved h

/-- `run_extend` from a method entry. -/
theorem invoke_extend {base linked : CIL.Program} (links : Links base linked) (fuel method : Nat)
    (args : List Value) (memory : Memory) (outcome : Except LocatedFault (Memory × List Value))
    (resolved : NoInvalidState outcome) (h : invoke base fuel method args memory = outcome) :
    invoke linked fuel method args memory = outcome := by
  cases hb : base[method]? with
  | none =>
    simp only [invoke, hb] at h
    exact absurd rfl (resolved _ h.symm)
  | some body =>
    have hl := links.found hb
    cases hc : (args.mapM (checkedValue memory)).mapError
        (fun fault => (⟨method, 0, fault⟩ : LocatedFault)) with
    | error fault =>
      simp only [invoke, hb, hl, hc, Bind.bind, Except.bind] at h ⊢
      exact h
    | ok checked =>
      cases he : (enterFrame body checked memory).mapError
          (fun fault => (⟨method, 0, fault⟩ : LocatedFault)) with
      | error fault =>
        simp only [invoke, hb, hl, hc, he, Bind.bind, Except.bind] at h ⊢
        exact h
      | ok entered =>
        obtain ⟨frame, entered⟩ := entered
        simp only [invoke, hb, hl, hc, he, Bind.bind, Except.bind] at h ⊢
        exact run_extend links fuel method 0 checked frame [] entered outcome resolved h

/-- A raised exception is not `invalidState`, so it is raised in every linked program. -/
theorem Raises.extend {base linked : CIL.Program} {method : Nat} {args : List Value} {memory : Memory}
    {exception : String} (raised : Raises base method args memory exception) (links : Links base linked) :
    Raises linked method args memory exception := by
  obtain ⟨fuel, fault, invoked, thrown⟩ := raised
  refine ⟨fuel, fault, invoke_extend links fuel method args memory _ ?_ invoked, thrown⟩
  intro located same
  cases same
  rw [thrown]
  exact nofun

/-- A contract proved on `base` holds at the same index in every program that links it. -/
theorem MethodContract.Holds.extend {Input Output : Type} {c : MethodContract Input Output}
    {base linked : CIL.Program} {method : Nat} (holds : c.Holds base method) (links : Links base linked) :
    c.Holds linked method := fun input initial permitted =>
  let ⟨fuel, final, values, invoked, framed, returns⟩ := holds input initial permitted
  ⟨fuel, final, values, invoke_extend links _ _ _ _ _ (fun _ h => nomatch h) invoked, framed, returns⟩

/-- Both outcomes transfer: a normal return as for `MethodContract`, a raise by `Raises.extend`. -/
theorem OutcomeContract.Holds.extend {Input Output : Type} {c : OutcomeContract Input Output}
    {base linked : CIL.Program} {method : Nat} (holds : c.Holds base method) (links : Links base linked) :
    c.Holds linked method := by
  intro input initial permitted
  have outcome := holds input initial permitted
  revert outcome
  cases c.raises input initial with
  | some exception => exact fun raised => raised.extend links
  | none =>
    exact fun ⟨fuel, final, values, invoked, framed, returns⟩ =>
      ⟨fuel, final, values, invoke_extend links _ _ _ _ _ (fun _ h => nomatch h) invoked, framed, returns⟩

/-- A call to a method the program lacks, such as an unlinked import, faults `invalidState` at the call. -/
theorem run_call_unlinked {program : CIL.Program} {fuel method pc callee : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (missing : program[callee]? = none) :
    run program (fuel + 1) method pc args frame stack memory = .error ⟨method, pc, .invalidState⟩ := by
  simp only [run, methodFound, instructionFound, stepped, missing, Except.mapError, Bind.bind, Except.bind]

/-- Invoking a method the program lacks faults `invalidState` at its entry. -/
theorem invoke_unlinked {program : CIL.Program} {fuel method : Nat} {args : List Value} {memory : Memory}
    (missing : program[method]? = none) :
    invoke program fuel method args memory = .error ⟨method, 0, .invalidState⟩ := by
  simp only [invoke, missing]

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
