import CIL.Safety.CertifiedContract

/-!
Consumer uses of invocation certificates on a one-method program, `Echo(v) => v`: a
certificate built from a computed `invoke` and from a computed run, a certified contract
that keeps `ReturnedState` through `Holds` and a refinement, and a refutation that compares
only the returned values of a computed run.
-/

namespace Tests.InvocationCertificates

open CIL.Safety

@[cil_code] def echo : CIL.Method := { returnsValue := true, locals := [], code := [.arg 0, .ret] }
@[cil_code] def program : CIL.Program := [echo]

/-- No allocation, view or static binding. -/
def empty : Memory :=
  { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }

theorem empty_formed : empty.WellFormed :=
  ⟨fun _ _ absent => (nomatch absent), fun _ member => (nomatch member)⟩

theorem empty_world : StaticWorldValid (programStaticDescriptors program) empty :=
  StaticWorldValid.of_absent _ _ (by simp [programStaticDescriptors, program, echo])
    (by simp [programStaticDescriptors, program, echo])
    ⟨List.Pairwise.nil, fun _ member => (nomatch member)⟩ fun _ member => (nomatch member)

/-! Certificates from a computed invocation and from its computed parts. -/

/-- `of_invoke` needs only entry premises and the invocation. -/
theorem echo_certificate :
    ∃ final, InvocationCertificate program 0 [.scalar (.i64 7)] empty 4 final [.scalar (.i64 7)] :=
  ⟨_, .of_invoke empty_formed empty_world
    (rfl : invoke program 4 0 [.scalar (.i64 7)] empty = .ok _)⟩

/-- The certificate exposes the returned-state invariant that a bare invocation does not. -/
theorem echo_returned_state :
    ∃ final, ReturnedState program final [.scalar (.i64 7)] := by
  obtain ⟨final, -, -, -, -, -, -, -, -, -, -, returned⟩ := echo_certificate
  exact ⟨final, returned⟩

/-- `of_run` takes the checked arguments, frame entry and run that `invoke` composes. -/
theorem echo_run_certificate :
    ∃ final, InvocationCertificate program 0 [.scalar (.i64 7)] empty 4 final [.scalar (.i64 7)] :=
  ⟨_, .of_run (body := echo) empty_formed empty_world rfl rfl
    (rfl : enterFrame echo [.scalar (.i64 7)] empty = .ok _) rfl⟩

#print axioms echo_certificate
#print axioms echo_returned_state
#print axioms echo_run_certificate

/-! A certified contract keeps the certificate through `Holds` and `Refines`. -/

/-- `Echo` returns its argument; the precondition supplies the entry premises. -/
def echoContract : MethodContract CIL.W64 CIL.W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ m := m.WellFormed ∧ StaticWorldValid (programStaticDescriptors program) m
  footprint _ := []
  post v _ _ out := out = v

theorem echo_holds : echoContract.Holds program 0 := by
  rintro v m -
  dsimp only [echoContract]
  refine ⟨4, m, _, ?_, Confined.refl _ m, v, rfl, rfl⟩
  cil_checked_steps []

theorem echo_certified : echoContract.Certified program 0 :=
  echo_holds.certified fun _ _ permitted => permitted

/-- The contract API still applies to a certified contract. -/
theorem echo_holds_of_certified : echoContract.Holds program 0 := echo_certified.holds

/-- A public contract that only bounds the result. -/
def echoBounded : MethodContract CIL.W64 CIL.W64 :=
  { echoContract with post := fun v _ _ out => out ≤ v }

theorem echo_bounded_refines : echoContract.Refines echoBounded :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ permitted => permitted,
    fun _ _ _ entry member => ⟨entry, member, Within.refl _⟩,
    fun _ _ _ _ _ _ same => by dsimp only [echoBounded]; exact same ▸ BitVec.le_refl _⟩

/-- The weakened contract keeps the certificate, so its callers keep `ReturnedState`. -/
theorem echo_bounded_returned (v : CIL.W64) (m : Memory) (permitted : echoBounded.pre v m) :
    ∃ fuel final values, invoke program fuel 0 [.scalar (.i64 v)] m = .ok (final, values) ∧
      ReturnedState program final values := by
  obtain ⟨fuel, final, values, ⟨invoked, -, -, -, -, -, -, -, -, -, returned⟩, -⟩ :=
    echo_certified.weaken echo_bounded_refines v m permitted
  exact ⟨fuel, final, values, invoked, returned⟩

#print axioms echo_certified
#print axioms echo_holds_of_certified
#print axioms echo_bounded_returned

/-! A refutation that observes only the returned values. -/

/-- Off by one: `Echo(7)` returns 7, not 8. -/
def echoOff : MethodContract CIL.W64 CIL.W64 :=
  { echoContract with post := fun v _ _ out => out = v + 1 }

theorem echo_off_rejected : ¬ echoOff.Holds program 0 := fun holds => by
  obtain ⟨_, _, values, invoked, -, out, encoded, wrong⟩ :=
    holds 7 empty ⟨empty_formed, empty_world⟩
  have observed := invoke_observation_unique Prod.snd
    (rfl : (invoke program 4 0 (echoOff.args 7) empty).map Prod.snd = .ok [.scalar (.i64 7)])
    invoked
  dsimp only [echoOff, echoContract] at observed encoded wrong
  subst observed wrong
  simp at encoded

#print axioms echo_off_rejected

end Tests.InvocationCertificates
