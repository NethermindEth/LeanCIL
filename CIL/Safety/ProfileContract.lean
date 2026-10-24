import CIL.Safety.ProfileCertificate
import CIL.Safety.RuntimeExceptions

/-!
# Method contracts across feature profiles

A contract proved for a program whose methods all use one feature profile also holds for the
same program reprofiled to any profile that agrees with it on every flag the program reads
(`CIL.Program.ProfileAgreement`, decided by `CIL.Program.ProfileAgreement.of_flags`). One proof
then certifies a method on every such profile. Builds on the checked invocation equivalence in
`CIL.Safety.ProfileEquivalence`.
-/

namespace CIL.Safety

/-- A uniform program and its reprofiling to an agreeing profile invoke identically, at every
    fuel, method, argument list and memory. -/
theorem invoke_uniform_reprofile_fun (program : CIL.Program) (p q : CIL.FeatureProfile)
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q) :
    invoke (CIL.reprofile program q) = invoke program := by
  funext fuel method args memory
  exact (invoke_uniform_reprofile_eq program p q uniform agreement fuel method args memory).symm

/-- A contract proved for a program whose methods all use profile `p` holds for the program
    reprofiled to any `q` that agrees with `p` on the program. -/
theorem MethodContract.Holds.reprofile {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} {p q : CIL.FeatureProfile}
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (holds : c.Holds program method) : c.Holds (CIL.reprofile program q) method := by
  unfold MethodContract.Holds
  rw [invoke_uniform_reprofile_fun program p q uniform agreement]
  exact holds

/-- `MethodContract.Holds.reprofile` for a contract that reads the program's static
    descriptors: reprofiling keeps them, so the same contract certifies the target. -/
theorem MethodContract.Holds.reprofile_statics {Input Output : Type}
    {contract : List CIL.StaticDescriptor → MethodContract Input Output}
    {program : CIL.Program} {method : Nat} {p q : CIL.FeatureProfile}
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (holds : (contract (programStaticDescriptors program)).Holds program method) :
    (contract (programStaticDescriptors (CIL.reprofile program q))).Holds
      (CIL.reprofile program q) method := by
  rw [programStaticDescriptors_reprofile]
  exact holds.reprofile uniform agreement

/-- An outcome contract, exceptions included, carries over to an agreeing profile as
    `MethodContract.Holds.reprofile` does. -/
theorem OutcomeContract.Holds.reprofile {Input Output : Type} {c : OutcomeContract Input Output}
    {program : CIL.Program} {method : Nat} {p q : CIL.FeatureProfile}
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (holds : c.Holds program method) : c.Holds (CIL.reprofile program q) method := by
  unfold OutcomeContract.Holds Raises
  rw [invoke_uniform_reprofile_fun program p q uniform agreement]
  exact holds

/-- `OutcomeContract.Holds.reprofile` for a contract that reads the program's static
    descriptors. -/
theorem OutcomeContract.Holds.reprofile_statics {Input Output : Type}
    {contract : List CIL.StaticDescriptor → OutcomeContract Input Output}
    {program : CIL.Program} {method : Nat} {p q : CIL.FeatureProfile}
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (holds : (contract (programStaticDescriptors program)).Holds program method) :
    (contract (programStaticDescriptors (CIL.reprofile program q))).Holds
      (CIL.reprofile program q) method := by
  rw [programStaticDescriptors_reprofile]
  exact holds.reprofile uniform agreement

/-- `OutcomeContract.Holds.reprofile` with exceptions named as the CLR reports them. -/
theorem OutcomeContract.HoldsCLR.reprofile {Input Output : Type}
    {c : OutcomeContract Input Output} {program : CIL.Program} {method : Nat}
    {p q : CIL.FeatureProfile}
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (holds : c.HoldsCLR program method) : c.HoldsCLR (CIL.reprofile program q) method := by
  unfold OutcomeContract.HoldsCLR RaisesCLR
  rw [invoke_uniform_reprofile_fun program p q uniform agreement]
  exact holds

#print axioms invoke_uniform_reprofile_fun
#print axioms MethodContract.Holds.reprofile
#print axioms MethodContract.Holds.reprofile_statics
#print axioms OutcomeContract.Holds.reprofile
#print axioms OutcomeContract.Holds.reprofile_statics
#print axioms OutcomeContract.HoldsCLR.reprofile
end CIL.Safety
