import CIL.Semantics

namespace CIL

/-- Replace only the fixed execution profile; instructions, arguments, local
layout, static data and return conventions remain exactly the same. -/
def reprofile (program : Program) (profile : FeatureProfile) : Program :=
  program.map fun body => { body with profile := profile }

def Op.ProfileAgreement (op : Op) (p q : FeatureProfile) : Prop :=
  match op with
  | .feature featureId => p.evaluate featureId = q.evaluate featureId
  | .intrinsic operation _ => operation.available p = operation.available q
  | _ => True

def Program.ProfileAgreement (program : Program) (p q : FeatureProfile) : Prop :=
  ∀ body ∈ program, ∀ op ∈ body.code, op.ProfileAgreement p q

/-- A syntactic check for operations whose execution does not observe a profile. -/
def Op.profileIndependentCheck : Op → Bool
  | .feature _ => false
  | .intrinsic (.scalar _) _ => true
  | .intrinsic (.vector _) _ => true
  | .intrinsic _ _ => false
  | _ => true

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

theorem step_profile_eq (op : Op) (p q : FeatureProfile)
    (h : op.ProfileAgreement p q) (returns : Bool) (pc : Nat) (args : List Value)
    (frame : Nat) (stack : List Value) (memory : Memory) :
    step op returns pc args frame stack memory p = step op returns pc args frame stack memory q := by
  cases op <;> try rfl
  case feature id =>
    change p.evaluate id = q.evaluate id at h
    change some (Action.next (pc + 1) (.i32 (if p.evaluate id then 1 else 0) :: stack) memory) =
      some (Action.next (pc + 1) (.i32 (if q.evaluate id then 1 else 0) :: stack) memory)
    rw [h]
  case intrinsic operation argc =>
    change operation.available p = operation.available q at h
    exact congrArg (fun available =>
      if stack.length < argc || !available then none else do
        return Action.next (pc + 1)
          ((← evalIntrinsic operation (stack.take argc).reverse) :: stack.drop argc) memory) h
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
    (reprofile program profile)[index]? = program[index]?.map (fun body => { body with profile := profile }) := by
  simp [reprofile]

theorem run_reprofile_eq (program : Program) (p q : FeatureProfile)
    (h : program.ProfileAgreement p q) (fuel method pc : Nat) (args : List Value)
    (frame : Nat) (stack : List Value) (memory : Memory) :
    run (reprofile program p) fuel method pc args frame stack memory =
      run (reprofile program q) fuel method pc args frame stack memory := by
  induction fuel generalizing method pc args frame stack memory with
  | zero => rfl
  | succ fuel ih =>
    cases hbody : program[method]? with
    | none => simp [run, hbody]
    | some body =>
      cases hop : body.code[pc]? with
      | none => simp [run, hbody, hop]
      | some op =>
        have hb : body ∈ program := List.mem_of_getElem? hbody
        have ho : op ∈ body.code := List.mem_of_getElem? hop
        have he := step_profile_eq op p q (h body hb op ho) body.returnsValue pc args frame stack memory
        simp only [run, reprofile_lookup, hbody, Option.map_some, Option.bind_eq_bind, Option.bind_some, hop]
        rw [he]
        cases hs : step op body.returnsValue pc args frame stack memory q with
        | none => rfl
        | some action =>
          cases action with
          | next target values updated => simpa only [Option.bind_eq_bind, Option.bind_some] using ih method target args frame values updated
          | returned values final => rfl
          | call callee childArgs rest updated =>
            cases hc : program[callee]? with
            | none => simp [hc]
            | some child =>
              simp only [hc, Option.map_some, Option.bind_some, initFrame_profile]
              rw [ih callee 0 childArgs (frame + 1) [] (initFrame updated (frame + 1) child childArgs)]
              cases hr : run (reprofile program q) fuel callee 0 childArgs (frame + 1) []
                  (initFrame updated (frame + 1) child childArgs) with
              | none => rfl
              | some result =>
                obtain ⟨final, values⟩ := result
                simpa only [Option.bind_eq_bind, Option.bind_some] using ih method (pc + 1) args frame (values ++ rest) final
          | construct callee childArgs rest updated =>
            cases hc : program[callee]? with
            | none => simp [hc]
            | some child =>
              simp only [hc, Option.map_some, Option.bind_some, initFrame_profile]
              rw [ih callee 0 childArgs (frame + 1) [] (initFrame updated (frame + 1) child childArgs)]
              cases hr : run (reprofile program q) fuel callee 0 childArgs (frame + 1) []
                  (initFrame updated (frame + 1) child childArgs) with
              | none => rfl
              | some result =>
                obtain ⟨final, values⟩ := result
                cases values with
                | cons value tail => rfl
                | nil =>
                  cases hsnapshot : readVectorHome final frame 2 pc with
                  | none => simp [hsnapshot]
                  | some value =>
                    simpa [hsnapshot] using
                      ih method (pc + 1) args frame (value :: rest) final

theorem invoke_reprofile_eq (program : Program) (p q : FeatureProfile)
    (h : program.ProfileAgreement p q) (fuel method : Nat) (args : List Value) (memory : Memory) :
    invoke (reprofile program p) fuel method args memory =
      invoke (reprofile program q) fuel method args memory := by
  cases hb : program[method]? with
  | none => simp [invoke, hb]
  | some body =>
    simpa only [invoke, reprofile_lookup, hb, Option.map_some, Option.bind_eq_bind, Option.bind_some,
      initFrame_profile] using
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

theorem invoke_uniform_reprofile_eq (program : Program) (p q : FeatureProfile)
    (hu : ∀ body ∈ program, body.profile = p) (ha : program.ProfileAgreement p q)
    (fuel method : Nat) (args : List Value) (memory : Memory) :
    invoke program fuel method args memory = invoke (reprofile program q) fuel method args memory := by
  have he := invoke_reprofile_eq program p q ha fuel method args memory
  rw [reprofile_eq_of_uniform program p hu] at he
  exact he

def Intrinsic.requiredFeatures : Intrinsic → List Feature
  | .scalar _ => []
  | .vector _ => []
  | .advSimd _ => [.advSimd]
  | .sse .shiftLeftBytes => [.sse2]
  | .sse .alignBytes => [.ssse3]
  | .avx _ => [.avx]
  | .avx2 _ => [.avx2]
  | .avx512 _ => [.avx512F, .avx512FVL]
  | .bmi1 _ => [.bmi1]
  | .bmi2 _ => [.bmi2]
  | .armBase64 _ => [.armBase64]
  | .x86Base _ => [.x86Base64]
  | .avx512DQ .moveMask64 => [.avx512DQ]
  | .avx512DQ .mul64 => [.avx512DQ, .avx512DQVL, .avx512F, .avx512FVL]

theorem Intrinsic.available_of_required (operation : Intrinsic) (p : FeatureProfile)
    (h : ∀ featureId ∈ operation.requiredFeatures, p.evaluate featureId = true) :
    operation.available p = true := by
  cases operation <;> simp_all [Intrinsic.requiredFeatures, Intrinsic.available, FeatureProfile.evaluate]
  case sse operation => cases operation <;> simp_all
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


end CIL
