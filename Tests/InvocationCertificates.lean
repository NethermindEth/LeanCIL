import CIL.Safety.CertifiedContract
import CIL.Safety.ReturnMemory

/-!
Consumer uses of invocation certificates on `Echo(v) => v` and its caller
`Relay(v) => Echo(v)`: a certificate built from a computed `invoke` and from a computed run,
a certified contract that keeps `ReturnedState` through `Holds` and a refinement, a call
that hands the caller the callee's certificate, and a refutation that compares only the
returned values of a computed run.
-/

namespace Tests.InvocationCertificates

open CIL.Safety

/-- The method index of `Echo`. -/
abbrev echoMethod : Nat := 0

/-- The method index of `Relay`. -/
abbrev relayMethod : Nat := 1

/-- `Echo(v) => v` on one scalar argument. -/
@[cil_code] def echo : CIL.Method := { returnsValue := true, locals := [], code := [.arg 0, .ret] }

/-- `Relay(v) => Echo(v)`: one call whose result it returns. -/
@[cil_code] def relay : CIL.Method :=
  { returnsValue := true, locals := [], code := [.arg 0, .call echoMethod 1, .ret] }

/-- `Echo` then `Relay`; the program declares no statics. -/
@[cil_code] def program : CIL.Program := [echo, relay]

/-- One unit of fuel for each `Echo` instruction. -/
abbrev echoFuel : Nat := 2

/-- The argument of the computed runs. -/
abbrev sample : CIL.W64 := 7

/-- `sample` as the argument list. -/
abbrev sampleArgs : List Value := [.scalar (.i64 sample)]

/-- No allocation, view or static binding. -/
def empty : Memory :=
  { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }

/-- Memory with no allocation is well formed. -/
theorem empty_formed : empty.WellFormed :=
  ⟨fun _ _ absent => (nomatch absent), fun _ member => (nomatch member)⟩

/-- With no static descriptor and no binding, the static world is valid. -/
theorem empty_world : StaticWorldValid (programStaticDescriptors program) empty :=
  StaticWorldValid.of_absent _ _ (by simp [programStaticDescriptors, program, echo, relay])
    (by simp [programStaticDescriptors, program, echo, relay])
    ⟨List.Pairwise.nil, fun _ member => (nomatch member)⟩ fun _ member => (nomatch member)

/-! Certificates from a computed invocation and from its computed parts. -/

/-- `of_invoke` needs only entry premises and the invocation. -/
theorem echo_certificate :
    ∃ final, InvocationCertificate program echoMethod sampleArgs empty echoFuel final sampleArgs :=
  ⟨_, .of_invoke empty_formed empty_world
    (rfl : invoke program echoFuel echoMethod sampleArgs empty = .ok _)⟩

/-- The certificate exposes the returned-state invariant that a bare invocation does not. -/
theorem echo_returned_state :
    ∃ final, ReturnedState program final sampleArgs := by
  obtain ⟨final, -, -, -, -, -, -, -, -, -, -, returned⟩ := echo_certificate
  exact ⟨final, returned⟩

/-- `of_run` takes the checked arguments, frame entry and run that `invoke` composes. -/
theorem echo_run_certificate :
    ∃ final, InvocationCertificate program echoMethod sampleArgs empty echoFuel final sampleArgs :=
  ⟨_, .of_run (body := echo) empty_formed empty_world rfl rfl
    (rfl : enterFrame echo sampleArgs empty = .ok _) rfl⟩

#print axioms echo_certificate
#print axioms echo_returned_state
#print axioms echo_run_certificate

/-! A certified contract keeps the certificate through `Holds` and `Refines`. -/

/-- `Echo` returns its argument; the precondition supplies the entry premises. -/
def echoContract : MethodContract CIL.W64 CIL.W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ memory := memory.WellFormed ∧ StaticWorldValid (programStaticDescriptors program) memory
  footprint _ := []
  post v _ _ out := out = v

/-- `Echo` meets its contract, stepped through the checked interpreter. -/
theorem echo_holds : echoContract.Holds program echoMethod := by
  rintro v memory -
  dsimp only [echoContract]
  refine ⟨echoFuel, memory, _, ?_, Confined.refl _ memory, v, rfl, rfl⟩
  cil_checked_steps []

/-- The precondition supplies the entry premises, so the proved contract is certified. -/
theorem echo_certified : echoContract.Certified program echoMethod :=
  echo_holds.certified fun _ _ permitted => permitted

/-- The contract API still applies to a certified contract. -/
theorem echo_holds_of_certified : echoContract.Holds program echoMethod := echo_certified.holds

/-- A public contract that only bounds the result. -/
def echoBounded : MethodContract CIL.W64 CIL.W64 :=
  { echoContract with post := fun v _ _ out => out ≤ v }

/-- Returning `v` bounds the result by `v`. -/
theorem echo_bounded_refines : echoContract.Refines echoBounded :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ permitted => permitted,
    fun _ _ _ entry member => ⟨entry, member, Within.refl _⟩,
    fun _ _ _ _ _ _ same => by dsimp only [echoBounded]; exact same ▸ BitVec.le_refl _⟩

/-- The weakened contract is still certified, with its own postcondition. -/
theorem echo_bounded_certified : echoBounded.Certified program echoMethod :=
  echo_certified.weaken echo_bounded_refines

/-- Callers of the weakened contract keep `ReturnedState` next to the exported bound. -/
theorem echo_bounded_returned (v : CIL.W64) (memory : Memory)
    (permitted : echoBounded.pre v memory) :
    ∃ fuel final out, invoke program fuel echoMethod [.scalar (.i64 v)] memory =
      .ok (final, [.scalar (.i64 out)]) ∧ ReturnedState program final [.scalar (.i64 out)] ∧
      out ≤ v := by
  obtain ⟨fuel, final, _, ⟨invoked, -, -, -, -, -, -, -, -, -, returned⟩, -, out, rfl, bound⟩ :=
    echo_bounded_certified v memory permitted
  exact ⟨fuel, final, out, invoked, returned, bound⟩

#print axioms empty_formed
#print axioms empty_world
#print axioms echo_holds
#print axioms echo_certified
#print axioms echo_bounded_refines
#print axioms echo_bounded_certified
#print axioms echo_holds_of_certified
#print axioms echo_bounded_returned

/-! A caller keeps the callee's certificate across the call. -/

/-- `Echo` with no precondition: it returns its argument from any memory. -/
def echoAnywhere : MethodContract CIL.W64 CIL.W64 :=
  { echoContract with pre := fun _ _ => True }

/-- `Echo` meets its contract from any memory. -/
theorem echo_anywhere : echoAnywhere.Holds program echoMethod := by
  rintro v memory -
  dsimp only [echoAnywhere, echoContract]
  refine ⟨echoFuel, memory, _, ?_, Confined.refl _ memory, v, rfl, rfl⟩
  cil_checked_steps []

/-- Names the frame `Echo(v)` enters from `memory` and a fuel at which that frame's run
    returns `v`, and says every state of that run is live. This is the visited-state clause
    of its certificate: neither `Holds` nor `run_call_of_contract_formed` supplies it. -/
def EchoVisitsLive (memory : Memory) (v : CIL.W64) : Prop :=
  ∃ fuel frame entered final, enterFrame echo [.scalar (.i64 v)] memory = .ok (frame, entered) ∧
    run program fuel echoMethod 0 [.scalar (.i64 v)] frame [] entered =
      .ok (final, [.scalar (.i64 v)]) ∧
    ∀ observedArgs observedFrame observedStack observed,
      RunningVisits program fuel echoMethod 0 [.scalar (.i64 v)] frame [] entered
        observedArgs observedFrame observedStack observed →
      LiveState program observedArgs observedFrame observedStack observed

/-- `Relay` returns its argument, and every state of its call to `Echo` is live. -/
def relayContract : MethodContract CIL.W64 CIL.W64 :=
  { echoContract with post := fun v initial _ out => out = v ∧ EchoVisitsLive initial v }

-- Hygiene would rename the `rfl` patterns into binders instead of substitutions.
set_option hygiene false in
/-- Closes a relay goal after its call: the callee's certificate supplies the run and
    visited-state clause of `EchoVisitsLive`, and `Relay` returns what `Echo` returned. -/
macro "relay_finish" : tactic => `(tactic| (
  rintro calleeFuel final values certificate framed ⟨out, rfl, rfl⟩
  obtain ⟨-, body, frame, entered, lookup, -, setup, finished, -, visits, -⟩ := certificate
  cases lookup
  cil_contract_steps []
  -- `Relay` owns no allocation, so leaving its frame keeps all memory below its watermark.
  exact ⟨framed.then_below
      (leaveFrame_preserves_memory_below _ final _ fun _ member => nomatch member)
      (Nat.le_of_eq (leaveFrame_nextIdentity _ final).symm), out, rfl, rfl,
    calleeFuel, frame, entered, final, setup, finished, visits⟩
  ))

/-- The call `Relay` makes at pc 1, standing in for a `bind_call` site. -/
theorem relaySite.call : relay.code[1]? = some (.call echoMethod 1) := rfl

/-- The caller supplies the entry premises, so a callee without a precondition still hands
    over its certificate, whose visited-state clause is the postcondition. -/
theorem relay_holds : relayContract.Holds program relayMethod := by
  rintro v memory ⟨formed, world⟩
  dsimp only [relayContract, echoContract]
  -- `Relay` has no locals, and `arg` and the call step leave memory unchanged, so the
  -- callee runs from `memory`.
  cil_contract_steps []
  cil_contract_certified_call echo_anywhere v []
  · trivial
  · exact formed
  · exact world
  relay_finish

/-- Through a certified callee, the precondition of `Echo` supplies the entry premises. -/
theorem relay_holds_of_certified : relayContract.Holds program relayMethod := by
  rintro v memory ⟨formed, world⟩
  dsimp only [relayContract, echoContract]
  cil_contract_steps []
  cil_certified_call echo_certified v []
  · exact ⟨formed, world⟩
  relay_finish

/-- The `at site` form of `cil_contract_certified_call` checks the call instruction. -/
theorem relay_holds_at_site : relayContract.Holds program relayMethod := by
  rintro v memory ⟨formed, world⟩
  dsimp only [relayContract, echoContract]
  cil_contract_steps []
  cil_contract_certified_call echo_anywhere v at relaySite []
  · trivial
  · exact formed
  · exact world
  relay_finish

/-- The `at site` form of `cil_certified_call` checks the call instruction. -/
theorem relay_holds_of_certified_at_site : relayContract.Holds program relayMethod := by
  rintro v memory ⟨formed, world⟩
  dsimp only [relayContract, echoContract]
  cil_contract_steps []
  cil_certified_call echo_certified v at relaySite []
  · exact ⟨formed, world⟩
  relay_finish

#print axioms echo_anywhere
#print axioms relay_holds
#print axioms relay_holds_of_certified
#print axioms relay_holds_at_site
#print axioms relay_holds_of_certified_at_site

/-! A refutation that observes only the returned values. -/

/-- Off by one: `Echo(sample)` returns `sample`, not `sample + 1`. -/
def echoOff : MethodContract CIL.W64 CIL.W64 :=
  { echoContract with post := fun v _ _ out => out = v + 1 }

/-- Only the returned values of a computed run are compared; memories never are. -/
theorem echo_off_rejected : ¬ echoOff.Holds program echoMethod := fun holds => by
  obtain ⟨_, _, values, invoked, -, out, encoded, wrong⟩ :=
    holds sample empty ⟨empty_formed, empty_world⟩
  have observed := invoke_ok_observation_unique Prod.snd
    (rfl : (invoke program echoFuel echoMethod (echoOff.args sample) empty).map Prod.snd =
      .ok sampleArgs)
    invoked
  dsimp only [echoOff, echoContract] at observed encoded wrong
  subst observed wrong
  simp at encoded

#print axioms echo_off_rejected

end Tests.InvocationCertificates
