import CIL.Safety.DecodedSummary
import CIL.Safety.ProfileCertificate
import CIL.Safety.RuntimeExceptions

/-!
# Method contracts across feature profiles

A contract proved for a program whose methods all use one feature profile also holds for the
same program reprofiled to any profile it agrees with on the program: every feature test and
intrinsic availability check answers the same (`CIL.Program.ProfileAgreement`).
`CIL.Program.ProfileAgreement.of_flags` derives that agreement from the flags the program reads,
a hypothesis `decide` closes for concrete profiles. One proof then certifies a method on every
such profile. Each lemma takes the source profile `p` explicitly, since `uniform` may be a
`decide` proof that cannot name it. Builds on the checked invocation equivalence in
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
    {program : CIL.Program} {method : Nat} {q : CIL.FeatureProfile} (p : CIL.FeatureProfile)
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (holds : c.Holds program method) : c.Holds (CIL.reprofile program q) method := by
  unfold MethodContract.Holds
  rw [invoke_uniform_reprofile_fun program p q uniform agreement]
  exact holds

open CIL.Extraction in
/-- Decoding the same evidence at a second profile preserves the method's pinned identity. -/
theorem DecodedAt.reprofile {program : CIL.Program} {evidence : List MethodEvidence}
    {source target : FeatureProfile} {environment : LayoutEnvironment} {index token : Nat}
    {pin : AssemblyPin} {arguments : List TypeExpr} {imports : List ImportSlot}
    (bound : DecodedAt program evidence source environment index pin token arguments)
    (decoded : decodedProgram? target environment evidence imports =
      some (CIL.reprofile program target)) :
    DecodedAt (CIL.reprofile program target) evidence target environment index pin token
      arguments := by
  obtain ⟨item, found, rfl, rfl, rfl, instantiated, _⟩ := bound
  exact .of_decoded decoded found instantiated

#print axioms DecodedAt.reprofile

open CIL.Extraction in
/-- A decoded summary carries to an agreeing profile when the same evidence decodes to the
    reprofiled program. The target summary retains the pinned assembly, token and arguments. -/
theorem DecodedSummary.reprofile {Input Output : Type} {contract : MethodContract Input Output}
    {program : CIL.Program} {evidence : List MethodEvidence} {source target : CIL.FeatureProfile}
    {environment : LayoutEnvironment} {index token : Nat} {pin : AssemblyPin}
    {arguments : List TypeExpr} {imports : List CIL.ImportSlot}
    (summary : DecodedSummary program evidence source environment index pin token arguments
      contract)
    (uniform : ∀ body ∈ program, body.profile = source)
    (agreement : program.ProfileAgreement source target)
    (decoded : decodedProgram? target environment evidence imports =
      some (CIL.reprofile program target)) :
    DecodedSummary (CIL.reprofile program target) evidence target environment index pin token
      arguments contract :=
  ⟨summary.holds.reprofile source uniform agreement, summary.bound.reprofile decoded⟩

#print axioms DecodedSummary.reprofile

/-- `MethodContract.Holds.reprofile` for a contract that reads the program's static
    descriptors: reprofiling keeps them, so the same contract certifies the target. `contract`
    is explicit because unification cannot recover it from its applications. -/
theorem MethodContract.Holds.reprofile_statics {Input Output : Type}
    (contract : List CIL.StaticDescriptor → MethodContract Input Output)
    {program : CIL.Program} {method : Nat} {q : CIL.FeatureProfile} (p : CIL.FeatureProfile)
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (holds : (contract (programStaticDescriptors program)).Holds program method) :
    (contract (programStaticDescriptors (CIL.reprofile program q))).Holds
      (CIL.reprofile program q) method := by
  rw [programStaticDescriptors_reprofile]
  exact holds.reprofile p uniform agreement

/-- An outcome contract, exceptions included, carries over to an agreeing profile as
    `MethodContract.Holds.reprofile` does. -/
theorem OutcomeContract.Holds.reprofile {Input Output : Type} {c : OutcomeContract Input Output}
    {program : CIL.Program} {method : Nat} {q : CIL.FeatureProfile} (p : CIL.FeatureProfile)
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (holds : c.Holds program method) : c.Holds (CIL.reprofile program q) method := by
  unfold OutcomeContract.Holds Raises
  rw [invoke_uniform_reprofile_fun program p q uniform agreement]
  exact holds

open CIL.Extraction in
/-- Both normal and exceptional outcomes carry to an agreeing profile when the target
    program decodes from the same pinned evidence. -/
theorem DecodedOutcomeSummary.reprofile {Input Output : Type}
    {contract : OutcomeContract Input Output}
    {program : CIL.Program} {evidence : List MethodEvidence} {source target : FeatureProfile}
    {environment : LayoutEnvironment} {index token : Nat} {pin : AssemblyPin}
    {arguments : List TypeExpr} {imports : List ImportSlot}
    (summary : DecodedOutcomeSummary program evidence source environment index pin token arguments
      contract) (uniform : ∀ body ∈ program, body.profile = source)
    (agreement : program.ProfileAgreement source target)
    (decoded : decodedProgram? target environment evidence imports =
      some (CIL.reprofile program target)) :
    DecodedOutcomeSummary (CIL.reprofile program target) evidence target environment index pin token
      arguments contract :=
  ⟨summary.holds.reprofile source uniform agreement, summary.bound.reprofile decoded⟩

#print axioms DecodedOutcomeSummary.reprofile

/-- `OutcomeContract.Holds.reprofile` for a contract that reads the program's static
    descriptors, with `contract` explicit as in `MethodContract.Holds.reprofile_statics`. -/
theorem OutcomeContract.Holds.reprofile_statics {Input Output : Type}
    (contract : List CIL.StaticDescriptor → OutcomeContract Input Output)
    {program : CIL.Program} {method : Nat} {q : CIL.FeatureProfile} (p : CIL.FeatureProfile)
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (holds : (contract (programStaticDescriptors program)).Holds program method) :
    (contract (programStaticDescriptors (CIL.reprofile program q))).Holds
      (CIL.reprofile program q) method := by
  rw [programStaticDescriptors_reprofile]
  exact holds.reprofile p uniform agreement

/-- `OutcomeContract.Holds.reprofile` with exceptions named as the CLR reports them. -/
theorem OutcomeContract.HoldsCLR.reprofile {Input Output : Type}
    {c : OutcomeContract Input Output} {program : CIL.Program} {method : Nat}
    {q : CIL.FeatureProfile} (p : CIL.FeatureProfile)
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
