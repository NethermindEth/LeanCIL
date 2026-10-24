import CIL.Safety.MethodContract

/-!
# Certified method contracts

`MethodContract.Certified` strengthens `MethodContract.Holds` with the
`InvocationCertificate` of the returning invocation, so a consumer keeps the visited-state
and returned-state invariants alongside the contract. `Holds.certified` derives it from a
proved contract whose precondition implies well-formed memory and a valid static world;
`Certified.holds` and `Certified.weaken` return to the ordinary contract API.
-/

namespace CIL.Safety

/-- Every invocation meeting `pre` returns normally within the footprint, satisfies `post`,
    and is certified by an `InvocationCertificate` for the same fuel and result. -/
def MethodContract.Certified {Input Output : Type} (c : MethodContract Input Output)
    (program : CIL.Program) (method : Nat) : Prop :=
  ∀ input initial, c.pre input initial →
    ∃ fuel final values,
      InvocationCertificate program method (c.args input) initial fuel final values ∧
      Confined (c.footprint input) initial final ∧ c.Returns input initial final values

/-- A certified contract holds; the certificate's first clause is the invocation. -/
theorem MethodContract.Certified.holds {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} (certified : c.Certified program method) :
    c.Holds program method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, certificate, framed, returns⟩ :=
    certified input initial permitted
  exact ⟨fuel, final, values, certificate.1, framed, returns⟩

/-- A proved contract is certified when its precondition implies well-formed memory and a
    valid static world, the premises checked frame entry needs. -/
theorem MethodContract.Holds.certified {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} (holds : c.Holds program method)
    (entry : ∀ input initial, c.pre input initial →
      initial.WellFormed ∧ StaticWorldValid (programStaticDescriptors program) initial) :
    c.Certified program method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, invoked, framed, returns⟩ := holds input initial permitted
  obtain ⟨formed, world⟩ := entry input initial permitted
  exact ⟨fuel, final, values, .of_invoke formed world invoked, framed, returns⟩

/-- Derive a certified contract from a certified one it refines, keeping the certificate;
    the method is neither unfolded nor executed. -/
theorem MethodContract.Certified.weaken {Input Output : Type}
    {internal exported : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} (certified : internal.Certified program method)
    (refines : internal.Refines exported) : exported.Certified program method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, certificate, framed, out, encoded, satisfied⟩ :=
    certified input initial (refines.pre _ _ permitted)
  refine ⟨fuel, final, values, ?_, framed.widen_within (refines.footprint _ _ permitted),
    out, ?_, refines.post _ _ _ _ permitted framed satisfied⟩
  · rw [refines.args]; exact certificate
  · rw [refines.results]; exact encoded

#print axioms MethodContract.Certified.holds
#print axioms MethodContract.Holds.certified
#print axioms MethodContract.Certified.weaken

end CIL.Safety
