import CIL.Safety.RunReturnTrace

/-!
# Invocation certificates

`InvocationCertificate` packages one successful `invoke` with the facts a consumer needs
about it: the frame it entered, that every running state it visits satisfies `LiveState`,
and that the returned state satisfies `ReturnedState`. `certify_invocation` builds one from
a live entry state and a successful `run`; `InvocationCertificate.of_run` and
`InvocationCertificate.of_invoke` need only well-formed initial memory and a valid static
world, since checked frame entry establishes the live entry state itself.
-/

namespace CIL.Safety

/-- Evidence for the actual invocation, including nested running/suspended
    states. Successful execution excludes checked faults and fuel exhaustion;
    the visited-state clause additionally exposes reference/lifetime invariants. -/
def InvocationCertificate (program : CIL.Program) (method : Nat) (args : List Value)
    (initial : Memory) (fuel : Nat) (final : Memory) (values : List Value) : Prop :=
  invoke program fuel method args initial = .ok (final, values) ∧
  ∃ body frame entered,
    program[method]? = some body ∧
    args.mapM (checkedValue initial) = .ok args ∧
    enterFrame body args initial = .ok (frame, entered) ∧
    run program fuel method 0 args frame [] entered = .ok (final, values) ∧
    LiveState program args frame [] entered ∧
    (∀ observedArgs observedFrame observedStack observed,
      RunningVisits program fuel method 0 args frame [] entered
        observedArgs observedFrame observedStack observed →
      LiveState program observedArgs observedFrame observedStack observed) ∧
    ReturnedState program final values

/-- A successful run from a live entry state certifies the invocation. -/
theorem certify_invocation (program : CIL.Program) (method : Nat) (body : CIL.Method)
    (args : List Value) (initial : Memory) (frame : Frame) (entered : Memory)
    (fuel : Nat) (final : Memory) (values : List Value)
    (lookup : program[method]? = some body)
    (checked : args.mapM (checkedValue initial) = .ok args)
    (setup : enterFrame body args initial = .ok (frame, entered))
    (live : LiveState program args frame [] entered)
    (finished : run program fuel method 0 args frame [] entered = .ok (final, values)) :
    InvocationCertificate program method args initial fuel final values := by
  refine ⟨?_, body, frame, entered, lookup, checked, setup, finished, live, ?_, ?_⟩
  · simpa only [invoke, lookup, checked, setup, Except.mapError, Bind.bind, Except.bind]
      using finished
  · intro observedArgs observedFrame observedStack observed visit
    exact runningVisits_live_state visit live
  · exact run_returned_state _ _ _ _ _ _ _ _ _ _ live finished

#print axioms certify_invocation

/-- A run of the frame that checked arguments enter certifies the invocation from well-formed
    memory in a valid static world. -/
theorem InvocationCertificate.of_run {program : CIL.Program} {method : Nat} {body : CIL.Method}
    {args : List Value} {initial : Memory} {frame : Frame} {entered : Memory} {fuel : Nat}
    {final : Memory} {values : List Value}
    (formed : initial.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) initial)
    (lookup : program[method]? = some body)
    (checked : args.mapM (checkedValue initial) = .ok args)
    (setup : enterFrame body args initial = .ok (frame, entered))
    (finished : run program fuel method 0 args frame [] entered = .ok (final, values)) :
    InvocationCertificate program method args initial fuel final values :=
  certify_invocation program method body args initial frame entered fuel final values lookup
    checked setup (checked_entry_live_state program body args args initial entered frame formed
      world checked setup) finished

#print axioms InvocationCertificate.of_run

/-- Every successful invocation from well-formed memory in a valid static world is certified:
    `invoke` checks its arguments and enters the frame itself. -/
theorem InvocationCertificate.of_invoke {program : CIL.Program} {method : Nat}
    {args : List Value} {initial : Memory} {fuel : Nat} {final : Memory} {values : List Value}
    (formed : initial.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) initial)
    (invoked : invoke program fuel method args initial = .ok (final, values)) :
    InvocationCertificate program method args initial fuel final values := by
  cases lookup : program[method]? with
  | none => simp [invoke, lookup] at invoked
  | some body =>
    cases checking : args.mapM (checkedValue initial) with
    | error fault =>
      simp [invoke, lookup, checking, Except.mapError, Bind.bind, Except.bind] at invoked
    | ok checked =>
      obtain ⟨rfl, -⟩ := checkedValues_valid _ _ _ checking
      cases setup : enterFrame body checked initial with
      | error fault =>
        simp [invoke, lookup, checking, setup, Except.mapError, Bind.bind, Except.bind] at invoked
      | ok entry =>
        obtain ⟨frame, entered⟩ := entry
        simp only [invoke, lookup, checking, setup, Except.mapError, Bind.bind, Except.bind]
          at invoked
        exact .of_run formed world lookup checking setup invoked

#print axioms InvocationCertificate.of_invoke

end CIL.Safety
