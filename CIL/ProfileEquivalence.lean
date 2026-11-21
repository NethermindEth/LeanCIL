import CIL.ExecutionLemmas
import CIL.Extraction.RuntimeModels

/-!
# Profile equivalence

Shows when a method's result does not depend on the hardware it runs on. Two feature
profiles agree on a program when every feature test and intrinsic availability check in it,
including those of the runtime models its calls run, gives the same answer under both. Checked
execution equivalence is proved in `CIL.Safety.ProfileEquivalence`.
-/

namespace CIL

/-- Replace only the fixed execution profile; instructions, arguments, local
layout, static data and return conventions remain exactly the same. -/
def reprofile (program : Program) (profile : FeatureProfile) : Program :=
  program.map fun body => { body with profile := profile }

/-- `p` and `q` answer the profile query `model` makes, if any, the same way: a feature test
    or an intrinsic's availability. -/
def RuntimeModel.ProfileAgreement (model : RuntimeModel) (p q : FeatureProfile) : Prop :=
  match model with
  | .feature featureId => p.evaluate featureId = q.evaluate featureId
  | .intrinsic operation _ => operation.available p = operation.available q
  | _ => True

/-- `p` and `q` answer the profile query `op` makes, if any, the same way: a feature test, an
    intrinsic's availability, or the query of the runtime model a call of a method with one runs,
    resolved in `environment`. -/
def Instruction.ProfileAgreement (environment : LayoutEnvironment) (op : Instruction)
    (p q : FeatureProfile) : Prop :=
  match op with
  | .intrinsic operation _ => operation.available p = operation.available q
  | .call method _ => ∀ model, Extraction.runtimeModel environment .call method = some model →
      model.ProfileAgreement p q
  | .newobj method => ∀ model, Extraction.runtimeModel environment .newobj method = some model →
      model.ProfileAgreement p q
  | _ => True

/-- `p` and `q` agree on every instruction of every method, in that method's environment. -/
def Program.ProfileAgreement (program : Program) (p q : FeatureProfile) : Prop :=
  ∀ body ∈ program, ∀ op ∈ body.code, op.ProfileAgreement body.environment p q

/-- An intrinsic step observes the profile only through the intrinsic's availability. -/
theorem step_intrinsic (operation : Intrinsic) (argc : Nat) (returns : Bool)
    (narrow : Option NarrowKind) (pc : Nat) (stack : List Value) (memory : Memory)
    (profile : FeatureProfile) :
    step (.intrinsic operation argc) returns narrow pc stack memory profile =
      if stack.length < argc || !operation.available profile then none else do
        return .next (pc + 1)
          ((← evalIntrinsic operation (stack.take argc).reverse) :: stack.drop argc) memory :=
  rfl

#print axioms step_intrinsic

/-- A step under agreeing profiles has the same outcome. -/
theorem step_profile_eq (environment : LayoutEnvironment) (op : Instruction)
    (p q : FeatureProfile) (h : op.ProfileAgreement environment p q) (returns : Bool)
    (narrow : Option NarrowKind) (pc : Nat)
    (stack : List Value) (memory : Memory) :
    step op returns narrow pc stack memory p =
      step op returns narrow pc stack memory q := by
  cases op <;> try rfl
  case intrinsic operation argc =>
    change operation.available p = operation.available q at h
    rw [step_intrinsic, step_intrinsic, h]
  case' ldind kind => cases kind
  case' stind kind => cases kind
  all_goals
    cases stack with
    | nil => rfl
    | cons a rest =>
      first
      | rfl
      | cases rest with
        | nil => first | rfl | (cases a <;> rfl)
        | cons b rest => first | rfl | (cases a <;> first | rfl | (cases b <;> rfl))

@[simp] theorem reprofile_lookup (program : Program) (profile : FeatureProfile) (index : Nat) :
    (reprofile program profile)[index]? =
      program[index]?.map (fun body => { body with profile := profile }) := by
  simp [reprofile]

theorem reprofile_eq_of_uniform (program : Program) (p : FeatureProfile)
    (h : ∀ body ∈ program, body.profile = p) : reprofile program p = program := by
  induction program with
  | nil => rfl
  | cons body rest ih =>
    have hp : body.profile = p := h body (by simp)
    have he : { body with profile := p } = body := by
      cases body
      cases hp
      rfl
    change { body with profile := p } :: reprofile rest p = body :: rest
    rw [he, ih]
    intro child hc
    exact h child (List.mem_cons_of_mem body hc)

theorem uniform_of_profile_map (program : Program) (p : FeatureProfile)
    (h : program.map (·.profile) = List.replicate program.length p) :
    ∀ body ∈ program, body.profile = p := by
  intro body hb
  have hm : body.profile ∈ program.map (·.profile) := List.mem_map.mpr ⟨body, hb, rfl⟩
  rw [h] at hm
  exact (List.mem_replicate.mp hm).2

/-- The features an intrinsic needs; `available_of_required` shows they suffice. -/
def Intrinsic.requiredFeatures : Intrinsic → List Feature
  | .scalar _ => []
  | .vector _ => []
  | .advSimd _ => [.advSimd]
  | .sse .shiftLeftBytes | .sse .multiplyEven32 => [.sse2]
  | .sse .alignBytes | .sse .shuffleBytes => [.ssse3]
  | .avx _ => [.avx]
  | .avx2 _ => [.avx2]
  | .avx512 .ltu512 | .avx512 .gtu512 => [.avx512F]
  | .avx512 _ => [.avx512F, .avx512FVL]
  | .bmi1 _ => [.bmi1]
  | .bmi2 _ => [.bmi2]
  | .armBase64 _ => [.armBase64]
  | .x86Base _ => [.x86Base64]
  | .aes _ => [.aes]
  | .armAes _ => [.armAes]
  | .avx512DQ .moveMask64 | .avx512DQ .moveMask512 => [.avx512DQ]
  | .avx512DQ .mul64 => [.avx512DQ, .avx512DQVL, .avx512F, .avx512FVL]

theorem Intrinsic.available_of_required (operation : Intrinsic) (p : FeatureProfile)
    (h : ∀ featureId ∈ operation.requiredFeatures, p.evaluate featureId = true) :
    operation.available p = true := by
  cases operation <;>
    simp_all [Intrinsic.requiredFeatures, Intrinsic.available, FeatureProfile.evaluate]
  case sse operation => cases operation <;> simp_all
  case avx512 operation =>
    cases operation <;>
      simp_all [Intrinsic.requiredFeatures, Intrinsic.available, FeatureProfile.evaluate]
  case avx512DQ operation => cases operation <;> simp_all

theorem RuntimeModel.ProfileAgreement.symm (model : RuntimeModel) (p q : FeatureProfile)
    (h : model.ProfileAgreement p q) : model.ProfileAgreement q p := by
  cases model <;> try trivial
  all_goals exact Eq.symm h

theorem RuntimeModel.ProfileAgreement.trans (model : RuntimeModel) (p q r : FeatureProfile)
    (hpq : model.ProfileAgreement p q) (hqr : model.ProfileAgreement q r) :
    model.ProfileAgreement p r := by
  cases model <;> try trivial
  all_goals exact Eq.trans hpq hqr

theorem Instruction.ProfileAgreement.symm (environment : LayoutEnvironment) (op : Instruction)
    (p q : FeatureProfile) (h : op.ProfileAgreement environment p q) :
    op.ProfileAgreement environment q p := by
  cases op <;> try trivial
  case call | newobj => exact fun model found => (h model found).symm
  all_goals exact Eq.symm h

theorem Instruction.ProfileAgreement.trans (environment : LayoutEnvironment) (op : Instruction)
    (p q r : FeatureProfile) (hpq : op.ProfileAgreement environment p q)
    (hqr : op.ProfileAgreement environment q r) : op.ProfileAgreement environment p r := by
  cases op <;> try trivial
  case call | newobj => exact fun model found => (hpq model found).trans _ _ _ _ (hqr model found)
  all_goals exact Eq.trans hpq hqr

/-- An intrinsic's availability is fixed by the features it needs: two profiles that agree on
    each of `requiredFeatures` agree on `available`. -/
theorem Intrinsic.available_eq_of_required (operation : Intrinsic) (p q : FeatureProfile)
    (agree : ∀ featureId ∈ operation.requiredFeatures,
      p.evaluate featureId = q.evaluate featureId) :
    operation.available p = operation.available q := by
  cases operation <;>
    simp_all [Intrinsic.requiredFeatures, Intrinsic.available, FeatureProfile.evaluate]
  case sse operation => cases operation <;> simp_all
  case avx512 operation => cases operation <;> simp_all
  case avx512DQ operation => cases operation <;> simp_all

/-- The profile flags `model` reads: the feature it tests, or every feature its intrinsic
    needs. -/
def RuntimeModel.profileReads : RuntimeModel → List Feature
  | .feature featureId => [featureId]
  | .intrinsic operation _ => operation.requiredFeatures
  | _ => []

/-- The profile flags `op` reads: the feature it tests, every feature its intrinsic needs, or
    those of the runtime model a call runs, resolved in `environment`. -/
def Instruction.profileReads (environment : LayoutEnvironment) : Instruction → List Feature
  | .intrinsic operation _ => operation.requiredFeatures
  | .call method _ =>
    ((Extraction.runtimeModel environment .call method).map RuntimeModel.profileReads).getD []
  | .newobj method =>
    ((Extraction.runtimeModel environment .newobj method).map RuntimeModel.profileReads).getD []
  -- A new profile-reading op breaks `step_profile_eq`; covering it in `ProfileAgreement`
  -- then breaks `ProfileAgreement.of_flags` until it is listed here.
  | _ => []

/-- Every profile flag an instruction of any method in the program reads, the same scope
    `Program.ProfileAgreement` quantifies over. -/
def Program.profileReads (program : Program) : List Feature :=
  program.flatMap fun body => body.code.flatMap (Instruction.profileReads body.environment)

/-- Two profiles that agree on every flag a model reads agree on the model. -/
theorem RuntimeModel.ProfileAgreement.of_flags (model : RuntimeModel) (p q : FeatureProfile)
    (agree : ∀ featureId ∈ model.profileReads, p.evaluate featureId = q.evaluate featureId) :
    model.ProfileAgreement p q := by
  cases model with
  | feature featureId => exact agree featureId (List.mem_singleton_self featureId)
  | intrinsic operation _ => exact Intrinsic.available_eq_of_required operation p q agree
  | _ => trivial

/-- Two profiles that agree on every flag the program reads agree on the whole program. The
    hypothesis is decidable, so `decide` closes it for concrete profiles. -/
theorem Program.ProfileAgreement.of_flags (program : Program) (p q : FeatureProfile)
    (agree : ∀ featureId ∈ program.profileReads, p.evaluate featureId = q.evaluate featureId) :
    program.ProfileAgreement p q := by
  intro body member op instruction
  have reads : ∀ featureId ∈ op.profileReads body.environment,
      p.evaluate featureId = q.evaluate featureId :=
    fun featureId read => agree featureId (List.mem_flatMap.mpr
      ⟨body, member, List.mem_flatMap.mpr ⟨op, instruction, read⟩⟩)
  cases op with
  | intrinsic operation _ => exact Intrinsic.available_eq_of_required operation p q reads
  | call method _ | newobj method =>
    intro model found
    exact RuntimeModel.ProfileAgreement.of_flags model p q fun featureId read =>
      reads featureId (by simp [Instruction.profileReads, found, read])
  | _ => trivial

#print axioms Intrinsic.available_eq_of_required
#print axioms Program.ProfileAgreement.of_flags
#print axioms RuntimeModel.ProfileAgreement.of_flags

end CIL
