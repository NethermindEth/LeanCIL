import CIL.ProfileEquivalence
import CIL.Safety.Execution

/-!
# Checked execution across feature profiles

The checked interpreter gives the same result for a program under two feature profiles
whenever every instruction agrees on them (`CIL.Instruction.ProfileAgreement`): only feature tests
and intrinsics consult the profile. `CIL.Safety.ProfileCertificate` lifts this to
invocation certificates and `CIL.Safety.ProfileContract` to method and outcome contracts.
-/

namespace CIL.Safety

theorem enterFrame_profile (body : CIL.Method) (profile : CIL.FeatureProfile)
    (args : List Value) (memory : Memory) :
    enterFrame { body with profile } args memory = enterFrame body args memory := rfl

/-- A call without a link runs the same under two profiles that agree on the query of the
    model its method has, if any. -/
theorem modelStep_profile_eq {opcode : CIL.CallOpcode} (body : CIL.Method)
    (method : Extraction.MethodRef) (p q : CIL.FeatureProfile)
    (agreement : ∀ model, Extraction.runtimeModel body.environment opcode method = some model →
      model.ProfileAgreement p q)
    (pc : Nat) (frame : Frame) (stack : List Value) (memory : Memory) :
    modelStep (Extraction.runtimeModel body.environment opcode method) { body with profile := p }
        pc frame stack memory =
      modelStep (Extraction.runtimeModel body.environment opcode method)
        { body with profile := q } pc frame stack memory := by
  cases found : Extraction.runtimeModel body.environment opcode method with
  | none => rfl
  | some model =>
    have agrees := agreement model found
    cases model <;> try rfl
    all_goals simp only [CIL.RuntimeModel.ProfileAgreement] at agrees
    all_goals simp only [modelStep, runModel, intrinsicCall, featureCall, agrees]

/-- A checked step does not depend on the method's profile when the instruction agrees on
    both profiles. -/
theorem step_profile_eq (body : CIL.Method) (op : CIL.Instruction) (p q : CIL.FeatureProfile)
    (agreement : op.ProfileAgreement body.environment p q) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (memory : Memory) :
    step { body with profile := p } op pc args frame stack memory =
      step { body with profile := q } op pc args frame stack memory := by
  have reprofiled : ∀ profile, ({ body with profile } : CIL.Method).linkAt pc = body.linkAt pc :=
    fun _ => rfl
  have construction (constructor : Extraction.MethodRef)
      (agrees : (CIL.Instruction.newobj constructor).ProfileAgreement body.environment p q) :
      newobjStep (body.linkAt pc) constructor { body with profile := p } pc frame stack memory =
        newobjStep (body.linkAt pc) constructor { body with profile := q } pc frame stack
          memory := by
    cases body.linkAt pc with
    | none => exact modelStep_profile_eq (opcode := .newobj) body constructor p q agrees ..
    | some link => cases link <;> rfl
  have baseStep := CIL.step_profile_eq body.environment op p q agreement
  unfold step referenceCompareCall referenceSubtractCall
  simp only [reprofiled]
  split <;> try rfl
  all_goals split <;> try rfl
  all_goals try exact construction _ agreement
  all_goals split <;> try rfl
  all_goals try exact modelStep_profile_eq _ _ _ _ agreement ..
  all_goals try (split <;> first | rfl | exact modelStep_profile_eq _ _ _ _ agreement ..)
  all_goals simp only [CIL.Instruction.ProfileAgreement] at agreement
  all_goals try simp only [agreement]
  all_goals simp only [baseStep]

/-- Handlers read the clauses of a body, never its profile. -/
theorem recover_profile (method : Nat) (body : CIL.Method) (profile : CIL.FeatureProfile)
    (pc : Nat) (frame : Frame) (memory : Memory) (state : FaultState) :
    recover method { body with profile } pc frame memory state =
      recover method body pc frame memory state := rfl

#print axioms recover_profile

/-- Running a reprofiled program stops in the same state or succeeds alike under any two
    profiles the program agrees on. -/
theorem runFaulting_reprofile_eq (program : CIL.Program) (p q : CIL.FeatureProfile)
    (agreement : program.ProfileAgreement p q) (fuel method pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (memory : Memory) :
    runFaulting ((CIL.reprofile program p)[·]?) fuel method pc args frame stack memory =
      runFaulting ((CIL.reprofile program q)[·]?) fuel method pc args frame stack memory := by
  have lookup (profile : CIL.FeatureProfile) {index : Nat} {body : CIL.Method}
      (found : program[index]? = some body) :
      (CIL.reprofile program profile)[index]? = some { body with profile } := by
    simp [CIL.reprofile_lookup, found]
  have missing (profile : CIL.FeatureProfile) {index : Nat} (absent : program[index]? = none) :
      (CIL.reprofile program profile)[index]? = none := by
    simp [CIL.reprofile_lookup, absent]
  induction fuel generalizing method pc args frame stack memory with
  | zero => rfl
  | succ fuel ih =>
    cases hb : program[method]? with
    | none => simp only [runFaulting, missing p hb, missing q hb]
    | some body =>
      cases ho : body.code[pc]? with
      | none => simp only [runFaulting, lookup p hb, lookup q hb, ho]
      | some op =>
        have same := step_profile_eq body op p q
          (agreement body (List.mem_of_getElem? hb) op (List.mem_of_getElem? ho))
          pc args frame stack memory
        simp only [runFaulting, lookup p hb, lookup q hb, ho, same, recover_profile]
        cases haction : step { body with profile := q } op pc args frame stack memory with
        | error fault => simp only [ih]
        | ok action =>
          cases action with
          | next target values frame memory => simp only [ih]
          | raise location object frame memory => simp only [ih]
          | returned values memory => rfl
          | tailCall callee arguments memory =>
            cases child : program[callee]? with
            | none => simp only [missing p child, missing q child]
            | some childBody =>
              simp only [lookup p child, lookup q child, enterFrame_profile, ih]
          | call callee arguments rest memory =>
            cases child : program[callee]? with
            | none => simp only [missing p child, missing q child]
            | some childBody =>
              simp only [lookup p child, lookup q child, enterFrame_profile, ih]
          | construct callee arguments rest frame temporary kind memory =>
            cases child : program[callee]? with
            | none => simp only [missing p child, missing q child]
            | some childBody =>
              simp only [lookup p child, lookup q child, enterFrame_profile, ih]

#print axioms runFaulting_reprofile_eq

/-- Running a reprofiled program gives the same result, fault or success, under any two
    profiles the program agrees on. -/
theorem run_reprofile_eq (program : CIL.Program) (p q : CIL.FeatureProfile)
    (agreement : program.ProfileAgreement p q) (fuel method pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (memory : Memory) :
    run (CIL.reprofile program p) fuel method pc args frame stack memory =
      run (CIL.reprofile program q) fuel method pc args frame stack memory := by
  unfold run runWith
  rw [runFaulting_reprofile_eq program p q agreement]

theorem invoke_reprofile_eq (program : CIL.Program) (p q : CIL.FeatureProfile)
    (agreement : program.ProfileAgreement p q) (fuel method : Nat)
    (args : List Value) (memory : Memory) :
    invoke (CIL.reprofile program p) fuel method args memory =
      invoke (CIL.reprofile program q) fuel method args memory := by
  cases hb : program[method]? with
  | none => simp [invoke_eq, hb]
  | some body =>
    simp only [invoke_eq, CIL.reprofile_lookup, hb, Option.map_some, enterFrame_profile]
    simp only [run_reprofile_eq program p q agreement]

/-- A program whose methods all use profile `p` behaves exactly as its reprofiling to `q`. -/
theorem invoke_uniform_reprofile_eq (program : CIL.Program) (p q : CIL.FeatureProfile)
    (uniform : ∀ body ∈ program, body.profile = p)
    (agreement : program.ProfileAgreement p q) (fuel method : Nat)
    (args : List Value) (memory : Memory) :
    invoke program fuel method args memory =
      invoke (CIL.reprofile program q) fuel method args memory := by
  have same := invoke_reprofile_eq program p q agreement fuel method args memory
  rw [CIL.reprofile_eq_of_uniform program p uniform] at same
  exact same

#print axioms invoke_reprofile_eq
#print axioms invoke_uniform_reprofile_eq
#print axioms run_reprofile_eq
#print axioms enterFrame_profile
#print axioms step_profile_eq
#print axioms modelStep_profile_eq
end CIL.Safety
