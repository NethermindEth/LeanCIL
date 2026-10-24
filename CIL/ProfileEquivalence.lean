import CIL.ExecutionLemmas

/-!
# Profile equivalence

Shows when a method's result does not depend on the hardware it runs on. Two feature
profiles agree on a program when every feature test and intrinsic availability check in it
gives the same answer under both; agreeing profiles then give identical `run` and `invoke`
results, so one proof covers every such deployment.
-/

namespace CIL

/-- Replace only the fixed execution profile; instructions, arguments, local
layout, static data and return conventions remain exactly the same. -/
def reprofile (program : Program) (profile : FeatureProfile) : Program :=
  program.map fun body => { body with profile := profile }

/-- `p` and `q` answer the profile query `op` makes, if any, the same way: a feature test or
    an intrinsic's availability. -/
def Op.ProfileAgreement (op : Op) (p q : FeatureProfile) : Prop :=
  match op with
  | .feature featureId => p.evaluate featureId = q.evaluate featureId
  | .intrinsic operation _ => operation.available p = operation.available q
  | _ => True

/-- `p` and `q` agree on every instruction of every method. -/
def Program.ProfileAgreement (program : Program) (p q : FeatureProfile) : Prop :=
  ∀ body ∈ program, ∀ op ∈ body.code, op.ProfileAgreement p q

/-- A syntactic check for operations whose execution does not observe a profile. -/
def Op.profileIndependentCheck : Op → Bool
  | .feature _ => false
  | .intrinsic (.scalar _) _ => true
  | .intrinsic (.vector _) _ => true
  | .intrinsic _ _ => false
  | _ => true

/-- Whether no instruction in the program observes the profile. -/
def Program.profileIndependentCheck (program : Program) : Bool :=
  program.all fun body => body.code.all Op.profileIndependentCheck

theorem Program.profile_independent_agreement (program : Program)
    (checked : program.profileIndependentCheck = true) (p q : FeatureProfile) :
    program.ProfileAgreement p q := by
  intro body member op instruction
  have bodyCheck := List.all_eq_true.mp checked body member
  have instructionCheck := List.all_eq_true.mp bodyCheck op instruction
  cases op <;> simp [Op.profileIndependentCheck, Op.ProfileAgreement] at *
  case intrinsic operation _ =>
    cases operation <;> simp [Intrinsic.available] at *

/-- A feature test pushes the profile's answer as `1` or `0`. -/
theorem step_feature (id : Feature) (returns : Bool) (pc : Nat) (args : List Value)
    (frame : Nat) (stack : List Value) (memory : Memory) (profile : FeatureProfile) :
    step (.feature id) returns pc args frame stack memory profile =
      some (.next (pc + 1) (.i32 (if profile.evaluate id then 1 else 0) :: stack) memory) :=
  rfl

/-- An intrinsic step observes the profile only through the intrinsic's availability. -/
theorem step_intrinsic (operation : Intrinsic) (argc : Nat) (returns : Bool) (pc : Nat)
    (args : List Value) (frame : Nat) (stack : List Value) (memory : Memory)
    (profile : FeatureProfile) :
    step (.intrinsic operation argc) returns pc args frame stack memory profile =
      if stack.length < argc || !operation.available profile then none else do
        return .next (pc + 1)
          ((← evalIntrinsic operation (stack.take argc).reverse) :: stack.drop argc) memory :=
  rfl

#print axioms step_feature
#print axioms step_intrinsic

/-- A step under agreeing profiles has the same outcome. -/
theorem step_profile_eq (op : Op) (p q : FeatureProfile)
    (h : op.ProfileAgreement p q) (returns : Bool) (pc : Nat) (args : List Value)
    (frame : Nat) (stack : List Value) (memory : Memory) :
    step op returns pc args frame stack memory p =
      step op returns pc args frame stack memory q := by
  cases op <;> try rfl
  case feature id =>
    change p.evaluate id = q.evaluate id at h
    rw [step_feature, step_feature, h]
  case intrinsic operation argc =>
    change operation.available p = operation.available q at h
    rw [step_intrinsic, step_intrinsic, h]
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

/-- Running a program under either of two agreeing profiles gives the same result. -/
theorem run_reprofile_eq (program : Program) (p q : FeatureProfile)
    (h : program.ProfileAgreement p q) (fuel method pc : Nat) (args : List Value)
    (frame : Nat) (stack : List Value) (memory : Memory) :
    run (reprofile program p) fuel method pc args frame stack memory =
      run (reprofile program q) fuel method pc args frame stack memory := by
  induction fuel generalizing method pc args frame stack memory with
  | zero => rfl
  | succ fuel ih =>
    rw [run_succ, run_succ]
    simp only [reprofile_lookup]
    cases hbody : program[method]? with
    | none => rfl
    | some body =>
      cases hop : body.code[pc]? with
      | none => simp [hop]
      | some op =>
        have agree := h body (List.mem_of_getElem? hbody) op (List.mem_of_getElem? hop)
        simp only [Option.map_some, Option.bind_some, hop,
          step_profile_eq op p q agree body.returnsValue pc args frame stack memory]
        have callees (source target : FeatureProfile) (callee : Nat) (child : Method)
            (found : (reprofile program source)[callee]? = some child) :
            ∃ child', (reprofile program target)[callee]? = some child' ∧
              ∀ memory frame args, initFrame memory frame child args =
                initFrame memory frame child' args := by
          simp only [reprofile_lookup, Option.map_eq_some_iff] at found
          obtain ⟨original, found, rfl⟩ := found
          exact ⟨{ original with profile := target }, by simp [found],
            fun _ _ _ => by simp only [initFrame_profile]⟩
        congr 1
        funext action
        exact Option.ext fun result =>
          ⟨runAction_transfer (callees p q) (fun _ _ _ _ _ _ _ run => (ih ..).symm.trans run)
              _ _ _ _ _ _,
            runAction_transfer (callees q p) (fun _ _ _ _ _ _ _ run => (ih ..).trans run)
              _ _ _ _ _ _⟩

theorem invoke_reprofile_eq (program : Program) (p q : FeatureProfile)
    (h : program.ProfileAgreement p q) (fuel method : Nat) (args : List Value) (memory : Memory) :
    invoke (reprofile program p) fuel method args memory =
      invoke (reprofile program q) fuel method args memory := by
  cases hb : program[method]? with
  | none => simp [invoke, hb]
  | some body =>
    simpa only [invoke, reprofile_lookup, hb, Option.map_some, Option.bind_eq_bind,
      Option.bind_some, initFrame_profile] using
      run_reprofile_eq program p q h fuel method 0 args 0 [] (initFrame memory 0 body args)

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

/-- A program whose methods all carry profile `p` behaves the same under any profile that
    agrees with `p`. -/
theorem invoke_uniform_reprofile_eq (program : Program) (p q : FeatureProfile)
    (hu : ∀ body ∈ program, body.profile = p) (ha : program.ProfileAgreement p q)
    (fuel method : Nat) (args : List Value) (memory : Memory) :
    invoke program fuel method args memory =
      invoke (reprofile program q) fuel method args memory := by
  have he := invoke_reprofile_eq program p q ha fuel method args memory
  rw [reprofile_eq_of_uniform program p hu] at he
  exact he

/-- The features an intrinsic needs; `available_of_required` shows they suffice. -/
def Intrinsic.requiredFeatures : Intrinsic → List Feature
  | .scalar _ => []
  | .vector _ => []
  | .advSimd _ => [.advSimd]
  | .sse .shiftLeftBytes => [.sse2]
  | .sse .alignBytes => [.ssse3]
  | .avx _ => [.avx]
  | .avx2 _ => [.avx2]
  | .avx512 .ltu512 | .avx512 .gtu512 => [.avx512F]
  | .avx512 _ => [.avx512F, .avx512FVL]
  | .bmi1 _ => [.bmi1]
  | .bmi2 _ => [.bmi2]
  | .armBase64 _ => [.armBase64]
  | .x86Base _ => [.x86Base64]
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

theorem Op.ProfileAgreement.symm (op : Op) (p q : FeatureProfile)
    (h : op.ProfileAgreement p q) : op.ProfileAgreement q p := by
  cases op <;> try trivial
  all_goals exact Eq.symm h

theorem Op.ProfileAgreement.trans (op : Op) (p q r : FeatureProfile)
    (hpq : op.ProfileAgreement p q) (hqr : op.ProfileAgreement q r) :
    op.ProfileAgreement p r := by
  cases op <;> try trivial
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

/-- The profile flags `op` reads: the feature it tests, or every feature its intrinsic needs. -/
def Op.profileReads : Op → List Feature
  | .feature featureId => [featureId]
  | .intrinsic operation _ => operation.requiredFeatures
  | _ => []

/-- Every profile flag an instruction of any method in the program reads. Extraction emits the
    methods reachable from its entry points, so these are the flags the reachable bodies read. -/
def Program.profileReads (program : Program) : List Feature :=
  program.flatMap fun body => body.code.flatMap Op.profileReads

/-- Two profiles that agree on every flag the program reads agree on the whole program. The
    hypothesis is decidable, so `decide` closes it for concrete profiles. -/
theorem Program.ProfileAgreement.of_flags (program : Program) (p q : FeatureProfile)
    (agree : ∀ featureId ∈ program.profileReads, p.evaluate featureId = q.evaluate featureId) :
    program.ProfileAgreement p q := by
  intro body member op instruction
  have reads : ∀ featureId ∈ op.profileReads, p.evaluate featureId = q.evaluate featureId :=
    fun featureId read => agree featureId (List.mem_flatMap.mpr
      ⟨body, member, List.mem_flatMap.mpr ⟨op, instruction, read⟩⟩)
  cases op with
  | feature featureId => exact reads featureId (List.mem_singleton_self featureId)
  | intrinsic operation _ => exact Intrinsic.available_eq_of_required operation p q reads
  | _ => trivial

#print axioms Intrinsic.available_eq_of_required
#print axioms Program.ProfileAgreement.of_flags

end CIL
