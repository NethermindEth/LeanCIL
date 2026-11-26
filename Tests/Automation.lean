import Tests.Support.IntrinsicMethods
import Tests.FeatureExecution
import CIL.Safety.SymbolicExecution
import CIL.Safety.MethodContract
import CIL.Safety.LoopAutomation
import CIL.Safety.OutcomeContract
import CIL.Safety.LocalSnapshotSteps
import CIL.SIMD.VectorLemmas
import Tests.Support
import Tests.WordFields

namespace Tests.Automation

attribute [local cil_code] Tests.supportedGetter_avx2_model
open Tests.WordFields

def candidate : Nat := 7
if_extracted Tests.Automation.candidate {
  theorem accepted : candidate = 7 := rfl
}

#guard_msgs (drop info) in
if_extracted Tests.Automation.candidate {
  theorem rejected : (1 : Nat) = 2 := by rfl
}

run_cmd do
  let env ← Lean.getEnv
  unless env.contains `Tests.Automation.accepted do
    throwError "Valid summary was lost"
  if env.contains `Tests.Automation.rejected then
    throwError "Failed summary escaped its transaction"

@[cil_code] def branchMethod : CIL.Method := {
  code := [.ldarg 0, .brfalse 4, .ldarg 1, .ret, .ldarg 1, .ret]
  locals := [], returnsValue := true }
@[cil_code] def branchProgram : CIL.Program := [branchMethod]

-- Both paths preserve arbitrary caller memory and a symbolic return value.
theorem checked_branch (memory : CIL.Safety.Memory) (condition value : CIL.W32) :
    CIL.Safety.invoke branchProgram (CIL.executionBound branchProgram 0) 0
      [.scalar (.i32 condition), .scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) := by
  by_cases zero : condition = 0
  · have truth : CIL.truth (.i32 condition) = some false := by simp [CIL.truth, zero]
    cil_checked_steps [truth]
  · have truth : CIL.truth (.i32 condition) = some true := by simp [CIL.truth]; exact zero
    cil_checked_steps [truth]

#print axioms checked_branch

-- An error logged earlier in the same proof must not reject a later valid candidate.
example : True := by
  run_tac do
    let earlier ← Lean.Core.getMessageLog
    Lean.logError "earlier failure"
    Lean.Elab.Tactic.evalTactic (← `(tactic| cil_strict exact trivial))
    Lean.Core.setMessageLog earlier

@[cil_code] def arithmeticMethod : CIL.Method := {
  code := [.ldarg 0, .ldarg 1, .ldc_i4 1, .shl, .add, .ldc_i4 0, .cgt_un, .ret]
  locals := [], returnsValue := true }

-- Symbolic values still reduce definitionally, including the final return.
theorem checked_arithmetic (memory : CIL.Safety.Memory) (left right : CIL.W32) :
    CIL.Safety.invoke [arithmeticMethod] 9 0
      [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (if left + (right <<< 1) > 0 then 1 else 0))]) := by
  cil_checked_steps

/-- info: 'Tests.Automation.checked_arithmetic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checked_arithmetic

@[cil_code] def narrowEqualityMethod : CIL.Method := {
  declared := { returnType := .primitive .boolean },
  code := [.ldarg 0, .ldarg 1, .xor, .ldc_i4 0, .ceq, .ret]
  locals := [], returnsValue := true }

def scalarDifference (left right : CIL.W32) : CIL.W32 := left ^^^ right

theorem checked_narrow_return (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame)
    (left right : CIL.W32) :
    CIL.Safety.run [narrowEqualityMethod] 6 0 0
      [.scalar (.i32 left), .scalar (.i32 right)] frame [] memory =
      .ok (CIL.Safety.leaveFrame frame memory,
        [.scalar (.i32 (if scalarDifference left right = 0 then 1 else 0))]) := by
  cil_checked_steps
  run_tac do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    unless (target.getArg! 1).isAppOf ``Except.ok do
      throwError "Expected the checked return equation"
    -- The return cleanup drops the narrowing, so consumers never unfold `NarrowKind.extend`.
    if (target.find? (·.isConstOf ``CIL.NarrowKind.extend)).isSome then
      throwError "The narrowed comparison return kept NarrowKind.extend"
  by_cases same : left = right <;> simp [scalarDifference, same]

#print axioms checked_narrow_return

@[cil_code] def decidedNarrowMethod : CIL.Method := {
  declared := { returnType := .primitive .boolean },
  code := [.ldc_i4 0, .ldc_i4 0, .ceq, .ret]
  locals := [], returnsValue := true }

/-- A comparison of literals decides to `1#32` before the narrowed return, which keeps it, so
    stepping alone closes the goal without unfolding `NarrowKind.extend`. -/
theorem checked_decided_narrow_return (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame) :
    CIL.Safety.run [decidedNarrowMethod] 4 0 0 [] frame [] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i32 1)]) := by
  cil_checked_steps

#print axioms checked_decided_narrow_return

theorem checked_plain_return (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame)
    (value : CIL.W32) :
    CIL.Safety.run [branchMethod] 1 0 3
      [] frame [.scalar (.i32 value)] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i32 value)]) := by
  cil_checked_steps

#print axioms checked_plain_return

/-! Run-to-run goals: a prefix of a method rewritten to the `run` it continues with. -/

@[cil_code] def prefixMethod : CIL.Method := {
  code := [.ldarg 0, .ldarg 1, .add, .ldarg 0, .add, .ret]
  locals := [], returnsValue := true }

-- Symbolic remaining fuel stops the unbounded stepper at the target, which cleanup closes.
theorem run_prefix (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame) (fuel : Nat) (a b : CIL.W64) :
    CIL.Safety.run [prefixMethod] (fuel + 3) 0 0 [.scalar (.i64 a), .scalar (.i64 b)] frame [] memory =
      CIL.Safety.run [prefixMethod] fuel 0 3 [.scalar (.i64 a), .scalar (.i64 b)] frame
        [.scalar (.i64 (a + b))] memory := by
  cil_checked_steps

-- A literal-fuel target the stepped state reaches syntactically is closed there, not run past.
theorem run_prefix_literal (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame) (a b : CIL.W64) :
    CIL.Safety.run [prefixMethod] 10 0 0 [.scalar (.i64 a), .scalar (.i64 b)] frame [] memory =
      CIL.Safety.run [prefixMethod] 7 0 3 [.scalar (.i64 a), .scalar (.i64 b)] frame
        [.scalar (.i64 (a + b))] memory := by
  cil_checked_steps

-- A target equal only up to commutativity: the bounded form stops at pc 3 instead of running past it.
theorem run_prefix_bounded (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame) (a b : CIL.W64) :
    CIL.Safety.run [prefixMethod] 10 0 0 [.scalar (.i64 a), .scalar (.i64 b)] frame [] memory =
      CIL.Safety.run [prefixMethod] 7 0 3 [.scalar (.i64 a), .scalar (.i64 b)] frame
        [.scalar (.i64 (b + a))] memory := by
  -- Unbounded stepping runs on to the return, past the target state.
  fail_if_success (cil_checked_steps; rw [BitVec.add_comm]; done)
  cil_checked_steps 3 []
  run_tac do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let some (_, lhs, _) := target.eq? | throwError "Expected a run equation"
    unless lhs.isAppOf ``CIL.Safety.run && lhs.getAppArgs[3]!.nat? == some 3 do
      throwError "cil_checked_steps 3 did not stop at pc 3"
  rw [BitVec.add_comm]

-- A tactic `have` wraps the target in metadata; bounded stepping must still see the run equation.
theorem run_prefix_bounded_after_have (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame)
    (a b : CIL.W64) (h : a + b = b + a) :
    CIL.Safety.run [prefixMethod] 10 0 0 [.scalar (.i64 a), .scalar (.i64 b)] frame [] memory =
      CIL.Safety.run [prefixMethod] 7 0 3 [.scalar (.i64 a), .scalar (.i64 b)] frame
        [.scalar (.i64 (b + a))] memory := by
  have commuted : a + b = b + a := h
  cil_checked_steps 3 [commuted]
  rw [commuted]

/-- error: cil_checked_steps 4: the goal closed after 3 steps -/
#guard_msgs in
example (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame) (fuel : Nat) (a b : CIL.W64) :
    CIL.Safety.run [prefixMethod] (fuel + 3) 0 0 [.scalar (.i64 a), .scalar (.i64 b)] frame [] memory =
      CIL.Safety.run [prefixMethod] fuel 0 3 [.scalar (.i64 a), .scalar (.i64 b)] frame
        [.scalar (.i64 (a + b))] memory := by
  cil_checked_steps 4

-- Bounded stepping is confined to the main goal: an early close errors instead of advancing the next goal.
/-- error: cil_checked_steps 4: the goal closed after 3 steps -/
#guard_msgs in
example (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame) (fuel : Nat) (a b : CIL.W64) :
    CIL.Safety.run [prefixMethod] (fuel + 3) 0 0 [.scalar (.i64 a), .scalar (.i64 b)] frame [] memory =
        CIL.Safety.run [prefixMethod] fuel 0 3 [.scalar (.i64 a), .scalar (.i64 b)] frame
          [.scalar (.i64 (a + b))] memory ∧
      CIL.Safety.run [prefixMethod] (fuel + 3) 0 0 [.scalar (.i64 a), .scalar (.i64 b)] frame [] memory =
        CIL.Safety.run [prefixMethod] fuel 0 3 [.scalar (.i64 a), .scalar (.i64 b)] frame
          [.scalar (.i64 (a + b))] memory := by
  constructor
  cil_checked_steps 4

-- Closing the first goal in exactly its steps leaves the second goal at pc 0, unstepped.
theorem run_prefix_bounded_two_goals (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame) (fuel : Nat)
    (a b : CIL.W64) :
    CIL.Safety.run [prefixMethod] (fuel + 3) 0 0 [.scalar (.i64 a), .scalar (.i64 b)] frame [] memory =
        CIL.Safety.run [prefixMethod] fuel 0 3 [.scalar (.i64 a), .scalar (.i64 b)] frame
          [.scalar (.i64 (a + b))] memory ∧
      CIL.Safety.run [prefixMethod] (fuel + 3) 0 0 [.scalar (.i64 a), .scalar (.i64 b)] frame [] memory =
        CIL.Safety.run [prefixMethod] fuel 0 3 [.scalar (.i64 a), .scalar (.i64 b)] frame
          [.scalar (.i64 (a + b))] memory := by
  constructor
  cil_checked_steps 3 []
  run_tac do
    let [goal] ← Lean.Elab.Tactic.getGoals | throwError "Expected only the second goal to remain"
    let target ← Lean.instantiateMVars (← goal.getType)
    let some (_, lhs, _) := target.consumeMData.eq? | throwError "Expected a run equation"
    unless lhs.isAppOf ``CIL.Safety.run && lhs.getAppArgs[3]!.nat? == some 0 do
      throwError "cil_checked_steps 3 advanced the second goal"
  cil_checked_steps 3 []

@[cil_code] def identityCallee : CIL.Method := {
  code := [.ldarg 0, .ret], locals := [], returnsValue := true }

@[cil_code] def callPrefixMethod : CIL.Method := {
  code := [.ldarg 0, .call (Tests.callee 1) {}, .ldarg 0, .add,
    .ret], links := [(1, .direct 1)], locals := [], returnsValue := true }

-- A bounded step over a call runs the callee but stops before the caller's continuation.
theorem run_call_prefix_bounded (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame) (a : CIL.W64) :
    CIL.Safety.run [callPrefixMethod, identityCallee] 10 0 0 [.scalar (.i64 a)] frame [] memory =
      CIL.Safety.run [callPrefixMethod, identityCallee] 8 0 2 [.scalar (.i64 a)] frame
        [.scalar (.i64 (a + 0))] memory := by
  -- Unbounded stepping runs through the caller's return, past the target state.
  fail_if_success (cil_checked_steps; simp; done)
  cil_checked_steps 2 []
  run_tac do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let some (_, lhs, _) := target.eq? | throwError "Expected a run equation"
    unless lhs.isAppOf ``CIL.Safety.run && lhs.getAppArgs[3]!.nat? == some 2 do
      throwError "cil_checked_steps 2 did not stop after the call"
  simp

#print axioms run_call_prefix_bounded
#print axioms run_prefix
#print axioms run_prefix_literal
#print axioms run_prefix_bounded
#print axioms run_prefix_bounded_after_have
#print axioms run_prefix_bounded_two_goals

def deferredReturnValue (value : CIL.W32) : CIL.W32 := value

theorem checked_plain_return_preserves_semireducible_goal
    (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame)
    (value : CIL.W32) :
    CIL.Safety.run [branchMethod] 1 0 3
      [] frame [.scalar (.i32 value)] memory =
      .ok (CIL.Safety.leaveFrame frame memory,
        [.scalar (.i32 (deferredReturnValue value))]) := by
  cil_checked_steps
  run_tac do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    unless (target.getArg! 1).isAppOf ``Except.ok do
      throwError "Expected the checked return equation"
  rfl

#print axioms checked_plain_return_preserves_semireducible_goal

theorem checked_literal_extension_return (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame)
    (left right : CIL.W64) :
    CIL.Safety.run [branchMethod] 1 0 3 [] frame
      [.scalar (.i64 (left * BitVec.signExtend 64 (3#32) + right))] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i64 (left * 3 + right))]) := by
  cil_checked_steps

theorem checked_decided_return (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame)
    (condition : Bool) (left right : CIL.W64) :
    CIL.Safety.run [branchMethod] 1 0 3 [] frame
      [.scalar (.i64 (match condition with | true => left | false => right))] memory =
      .ok (CIL.Safety.leaveFrame frame memory,
        [.scalar (.i64 (if condition = true then left else right))]) := by
  cases condition <;> cil_checked_steps

#print axioms checked_literal_extension_return
#print axioms checked_decided_return

theorem checked_negative_literal_return (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame)
    (left : CIL.W32) :
    CIL.Safety.run [branchMethod] 1 0 3 [] frame
      [.scalar (.i32 (left + BitVec.ofInt 32 (-1)))] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i32 (left + 4294967295#32))]) := by
  cil_checked_steps

#print axioms checked_negative_literal_return
/-- A reusable body, bound to an extraction only through a lookup hypothesis. -/
def wordBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [], code := [.ldarg 0, .not, .ldarg 1, .not, .or,
      .not, .ret] }

theorem word_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (wordBody profile)) (memory : CIL.Safety.Memory) (a b : BitVec 64) :
    CIL.Safety.invoke program 10 index [.scalar (.i64 a), .scalar (.i64 b)] memory =
      .ok (memory, [.scalar (.i64 (~~~(~~~a ||| ~~~b)))]) := by
  cil_checked_steps

/-- A profile-dependent body: its instructions are fetched only once the feature test is decided. -/
@[cil_code] def featureBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [], code := if profile.avx2 then [.ldarg 1,
      .ret] else [.ldarg 0, .ret] }

theorem feature_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (scalar : profile.avx2 = false) (found : program[index]? = some (featureBody profile))
    (memory : CIL.Safety.Memory) (a b : CIL.W32) :
    CIL.Safety.invoke program 3 index [.scalar (.i32 a), .scalar (.i32 b)] memory = .ok (memory, [.scalar (.i32 a)]) := by
  cil_checked_steps [scalar]

-- Without the lookup hypothesis no instruction can be fetched, and the tactic says so instead of doing nothing.
example (program : CIL.Program) (index : Nat) (memory : CIL.Safety.Memory) (a b : BitVec 64) (stop : False) :
    CIL.Safety.invoke program 10 index [.scalar (.i64 a), .scalar (.i64 b)] memory =
      .ok (memory, [.scalar (.i64 (~~~(~~~a ||| ~~~b)))]) := by
  fail_if_success cil_checked_steps
  exact stop.elim

/-- info: 'Tests.Automation.word_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms word_checked

/-- A 27-instruction read-only leaf over symbolic memory: each field load comes from a fact, every step from an
    equation, so no step unfolds the dispatcher. -/
def leafBody (profile : CIL.FeatureProfile) : CIL.Method := {
  declared := { returnType := .primitive .boolean },
  profile, environment := wordsEnvironment, returnsValue := true, locals := [], code := [
  .ldarg 0, .ldfld word0, .ldarg 1, .ldfld word0, .xor,
  .ldarg 0, .ldfld word1, .ldarg 1, .ldfld word1, .xor, .or,
  .ldarg 0, .ldfld word2, .ldarg 1, .ldfld word2, .xor, .or,
  .ldarg 0, .ldfld word3, .ldarg 1, .ldfld word3, .xor, .or,
  .ldc_i4 0, .conv_i8, .ceq, .ret] }

open CIL.Safety in
theorem leaf_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (leafBody profile)) (memory : Memory) (left right : Reference)
    (limb : Reference → Nat → BitVec 64) (fl : form memory left = .ok left) (fr : form memory right = .ok right)
    (field : ∀ r offset rest, loadValueField offset 8 false (.reference (.address r) :: rest) memory =
      .ok (memory, .scalar (.i64 (limb r offset)) :: rest)) :
    let difference := (limb left 0 ^^^ limb right 0) ||| (limb left 8 ^^^ limb right 8) |||
      (limb left 16 ^^^ limb right 16) ||| (limb left 24 ^^^ limb right 24)
    invoke program 28 index [.reference (.address left), .reference (.address right)] memory =
      .ok (memory, [.scalar (.i32 (CIL.NarrowKind.unsigned8.extend (if difference = 0 then 1 else 0)))]) := by
  cil_checked_steps [fl, fr, field]

def boundBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [],
    code := [.ldarg 0, .ldarg 1, .blt_un 5, .ldarg 0, .ret, .ldarg 1, .ret] }

/-- A fact decides an unsigned i64 branch, so the run falls through to pc 3. -/
theorem bound_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (boundBody profile)) (memory : CIL.Safety.Memory) (x y : CIL.W64)
    (above : ¬ x < y) :
    CIL.Safety.invoke program 8 index [.scalar (.i64 x), .scalar (.i64 y)] memory =
      .ok (memory, [.scalar (.i64 x)]) := by
  cil_checked_steps [above]

/-- A signed branch takes its fact in the interpreter's own form, so no linear-arithmetic restatement is needed. -/
theorem signed_bound_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some { boundBody profile with code := [.ldarg 0, .ldarg 1, .blt 5,
        .ldarg 0, .ret, .ldarg 1, .ret] })
    (memory : CIL.Safety.Memory) (x y : CIL.W64) (above : ¬ x.toInt < y.toInt) :
    CIL.Safety.invoke program 8 index [.scalar (.i64 x), .scalar (.i64 y)] memory =
      .ok (memory, [.scalar (.i64 x)]) := by
  cil_checked_steps [above]

-- The step equations alone rewrite a compare-branch; the dispatcher stays folded.
example (body : CIL.Method) (args : List CIL.Safety.Value) (frame : CIL.Safety.Frame) (m : CIL.Safety.Memory)
    (x y : CIL.W64) (above : ¬ x < y) :
    CIL.Safety.step body (.blt_un 5) 2 args frame [.scalar (.i64 y), .scalar (.i64 x)] m =
      .ok (.next 3 [] frame m) := by
  simp only [cil_step, above, ↓reduceIte]

-- Guard reduction inspects only consumed values, even with an unknown stack tail.
theorem guard_known_i64 (value : CIL.W64) (rest : List CIL.Safety.Value) :
    CIL.Safety.unspecifiedOperands 1 (.scalar (.i64 value) :: rest) = false := by
  simp only [cil_guard, Bool.false_or]

theorem guard_i64_step (body : CIL.Method) (args : List CIL.Safety.Value)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) (pc : Nat)
    (value : CIL.W64) (rest : List CIL.Safety.Value) :
    CIL.Safety.step body .neg pc args frame (.scalar (.i64 value) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i64 (-value)) :: rest) frame memory) := by
  simp only [cil_step]

-- A tactic `have` wraps the target in metadata; the single-step helper must still see the step equation.
theorem checked_step_after_have (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame)
    (a b : CIL.W64) (h : a = a) :
    CIL.Safety.step prefixMethod .add 2 [.scalar (.i64 a), .scalar (.i64 b)] frame
      [.scalar (.i64 b), .scalar (.i64 a)] memory =
      .ok (.next 3 [.scalar (.i64 (a + b))] frame memory) := by
  have unused : a = a := h
  cil_checked_step [unused]

#print axioms checked_step_after_have

-- A partial vector must still fail before an instruction observes its unknown bits.
theorem guard_partial_vector_rejected (body : CIL.Method) (args : List CIL.Safety.Value)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) (pc : Nat)
    (value : CIL.W64) (rest : List CIL.Safety.Value) :
    CIL.Safety.step body .neg pc args frame (.scalar (.v128Low64 value) :: rest) memory =
      .error (.unsupported "Instruction observes unspecified vector bits") := by
  cil_checked_step []

-- An unknown constructor leaves its guard as a required fact.
theorem guard_unknown_requires_fact (value : CIL.Value) (known : value.hasUnspecified = false) :
    CIL.Safety.unspecifiedOperands 1 [.scalar value] = false := by
  fail_if_success (simp only [cil_guard, Bool.or_false]; done)
  simpa only [cil_guard, Bool.or_false] using known

/-- info: 'Tests.Automation.leaf_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms leaf_checked
/-- info: 'Tests.Automation.bound_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bound_checked
open CIL.Safety in
theorem scalar_fact_stack (body : CIL.Method) (args : List Value) (frame : Frame)
    (memory : Memory) (left right : CIL.W64) (word : Nat) (unrelated : word = 7) :
    ∃ stack, step body .xor 0 args frame [.scalar (.i64 right), .scalar (.i64 left)] memory =
      .ok (.next 1 stack frame memory) ∧ stack = [.scalar (.i64 (left ^^^ right))] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [unrelated]
  · rfl

open CIL.Safety in
theorem bitcast_fact_stack (body : CIL.Method) (frame : Frame)
    (memory : Memory) (bytes : List (BitVec 8)) (value : BitVec 256)
    (casted : bitcastValue (.aggregate 32) .vector256 (.aggregate bytes) = .ok (.v256 value)) :
    ∃ stack, modelStep (some (.memory (.bitcastValue (.aggregate 32) .vector256))) body 0 frame
      [.scalar (.aggregate bytes)] memory = .ok (.next 1 stack frame memory) ∧
      stack = [.scalar (.v256 value)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [casted]
  · rfl

@[cil_eval] theorem eval_reverse256 (a b c d : CIL.W64) :
    CIL.evalIntrinsic (.avx2 .permute4x64)
      [.v256 (CIL.Vector.pack256 a b c d), .i32 (BitVec.ofNat 32 27)] =
      some (.v256 (CIL.Vector.pack256 d c b a)) := by
  change some (CIL.Value.v256
    (CIL.Vector.permute4x64 (CIL.Vector.pack256 a b c d) (BitVec.ofNat 8 0x1B))) = _
  rw [CIL.Vector.permute4x64_reverse]

@[cil_code] def permuteStoreMethod : CIL.Method := {
  profile := { architecture := .x64, avx2 := true }
  code := [.call Tests.IntrinsicMethods.permute, .stobj Tests.IntrinsicMethods.vector256UInt64, .ret]
  locals := [], returnsValue := false }

@[cil_code] def permuteStoreProgram : CIL.Program := [permuteStoreMethod]

-- A store fact stated at the `memoryInstruction` level, as consumers wrote before per-shape
-- equations, still applies without `staticInstruction` passed to unfold.
open CIL.Safety in
theorem permute_then_store (a b c d : CIL.W64) (destination : Reference) (memory final : Memory)
    (stored : ∀ rest, memoryInstruction .store256
      (.scalar (.v256 (CIL.Vector.pack256 d c b a)) :: .reference (.address destination) :: rest) memory =
      .ok (final, rest)) :
    run permuteStoreProgram 3 0 0 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.i32 (BitVec.ofInt 32 27)), .scalar (.v256 (CIL.Vector.pack256 a b c d)),
        .reference (.address destination)] memory = .ok (final, []) := by
  cil_checked_steps [stored]

open CIL.Safety in
/-- A `memoryInstruction` fact closes a single store step without `staticInstruction` passed. -/
theorem store_from_instruction_fact (body : CIL.Method) (frame : Frame)
    (bits : BitVec 256) (destination : Reference) (memory final : Memory)
    (stored : memoryInstruction .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    modelStep (some (.memory .store256)) body 2 frame
      [.scalar (.v256 bits), .reference (.address destination)] memory =
      .ok (.next 3 [] frame final) := by
  cil_checked_step [stored]

/--
info: 'Tests.Automation.store_from_instruction_fact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms store_from_instruction_fact

open CIL.Safety in
/-- A quantified instruction fact supplies duplication through the generic step equation. -/
theorem duplicate_from_instruction_fact (body : CIL.Method) (pc : Nat)
    (args rest : List Value) (frame : Frame) (memory : Memory) (bits : BitVec 256)
    (duplicated : ∀ (memory : Memory) (bits : BitVec 256) (rest : List Value),
      instruction .dup (.scalar (.v256 bits) :: rest) memory =
        .ok (memory, .scalar (.v256 bits) :: .scalar (.v256 bits) :: rest)) :
    step body .dup pc args frame (.scalar (.v256 bits) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.v256 bits) :: .scalar (.v256 bits) :: rest)
        frame memory) := by
  cil_checked_step [duplicated]

/--
info: 'Tests.Automation.duplicate_from_instruction_fact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms duplicate_from_instruction_fact

open CIL.Safety in
/-- A fact one level up, on `staticInstruction`, still closes the store: the retry tries it
    before unfolding `staticInstruction`, which would rewrite past it. -/
theorem store_from_static_fact (body : CIL.Method) (frame : Frame)
    (bits : BitVec 256) (destination : Reference) (memory final : Memory)
    (stored : staticInstruction body 2 .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    modelStep (some (.memory .store256)) body 2 frame
      [.scalar (.v256 bits), .reference (.address destination)] memory =
      .ok (.next 3 [] frame final) := by
  cil_checked_step [stored]

/--
info: 'Tests.Automation.store_from_static_fact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms store_from_static_fact

open CIL.Safety in
/-- A static load steps by a fact about `staticLoad`, which `staticLoad_initialized` gives from
    the descriptor a `staticAt` fact binds to the pc. -/
theorem static_load_from_fact (body : CIL.Method) (args : List Value) (frame : Frame)
    (field : CIL.Extraction.FieldRef) (value : CIL.Value) (memory : Memory)
    (loaded : staticLoad body 0 memory = .ok (memory, .scalar value)) :
    step body (.ldsfld field) 0 args frame [] memory =
      .ok (.next 1 [.scalar value] frame memory) := by
  cil_checked_step [loaded]

/--
info: 'Tests.Automation.static_load_from_fact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms static_load_from_fact

/-- Two vector stores; reached through a lookup hypothesis, so facts can name the body. -/
def twoStoresMethod : CIL.Method := {
  code := [.stobj Tests.IntrinsicMethods.vector256UInt64, .stobj Tests.IntrinsicMethods.vector256UInt64, .ret], locals := [], returnsValue := false }

open CIL.Safety in
/-- Facts at both levels in one run: each store takes the retry for its own fact's level, so
    neither retry may exclude the other. -/
theorem stores_from_mixed_facts (program : CIL.Program) (index : Nat)
    (found : program[index]? = some twoStoresMethod) (first second : BitVec 256)
    (near far : Reference) (memory middle final : Memory)
    (storedFirst : ∀ rest, staticInstruction twoStoresMethod 0 .store256
      (.scalar (.v256 first) :: .reference (.address near) :: rest) memory = .ok (middle, rest))
    (storedSecond : ∀ rest, memoryInstruction .store256
      (.scalar (.v256 second) :: .reference (.address far) :: rest) middle = .ok (final, rest)) :
    run program 3 index 0 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.v256 first), .reference (.address near), .scalar (.v256 second),
        .reference (.address far)] memory = .ok (final, []) := by
  cil_checked_steps [storedFirst, storedSecond]

/-- info: 'Tests.Automation.stores_from_mixed_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stores_from_mixed_facts

-- Naming `staticInstruction` explicitly, and stating either fact as a proof term, still applies.
open CIL.Safety in
example (body : CIL.Method) (frame : Frame) (bits : BitVec 256)
    (destination : Reference) (memory final : Memory)
    (stored : memoryInstruction .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    modelStep (some (.memory .store256)) body 2 frame
      [.scalar (.v256 bits), .reference (.address destination)] memory =
      .ok (.next 3 [] frame final) := by
  cil_checked_step [staticInstruction, stored]

open CIL.Safety in
example (body : CIL.Method) (frame : Frame) (bits : BitVec 256)
    (destination : Reference) (memory final : Memory)
    (stored : memoryInstruction .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    modelStep (some (.memory .store256)) body 2 frame
      [.scalar (.v256 bits), .reference (.address destination)] memory =
      .ok (.next 3 [] frame final) := by
  cil_checked_step [(stored)]

open CIL.Safety in
example (body : CIL.Method) (frame : Frame) (bits : BitVec 256)
    (destination : Reference) (memory final : Memory)
    (stored : staticInstruction body 2 .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    modelStep (some (.memory .store256)) body 2 frame
      [.scalar (.v256 bits), .reference (.address destination)] memory =
      .ok (.next 3 [] frame final) := by
  cil_checked_step [(stored)]

-- The same store from a `storeValue` fact: the per-shape memory equation exposes it without unfolding a dispatcher.
open CIL.Safety in
theorem permute_then_store_value (a b c d : CIL.W64) (destination : Reference) (memory final : Memory)
    (stored : storeValue memory (.address destination) (.v256 (CIL.Vector.pack256 d c b a)) = .ok final) :
    run permuteStoreProgram 3 0 0 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.i32 (BitVec.ofInt 32 27)), .scalar (.v256 (CIL.Vector.pack256 a b c d)),
        .reference (.address destination)] memory = .ok (final, []) := by
  cil_checked_steps [stored]

/-- A feature test steps from a fact about the profile field, through a body neither unfolded nor tagged. -/
def featureTestBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [], code := [.call (Tests.supportedGetter "X86.Avx2"), .ret] }

theorem feature_step_from_fact (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (wide : profile.avx2 = true) (found : program[index]? = some (featureTestBody profile))
    (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke program 3 index [] memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [wide]

theorem feature_step_free_body (program : CIL.Program) (index : Nat) (body : CIL.Method)
    (wide : body.profile.avx2 = false) (unlinked : body.linkAt 0 = none)
    (code : body.code = [.call (Tests.supportedGetter "X86.Avx2"), .ret])
    (returns : body.returnsValue = true) (found : program[index]? = some body)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) :
    CIL.Safety.run program 3 index 0 [] frame [] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i32 0)]) := by
  cases narrow : body.returnNarrow <;> cil_checked_steps [unlinked, wide, code, returns, narrow]

-- A literal profile decides the test with no fact.
theorem feature_step_literal_profile (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke [{ permuteStoreMethod with code := [.call (Tests.supportedGetter "X86.Avx2"), .ret], returnsValue := true }] 3 0 []
      memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps

-- Each memory step rewrites by its own equation; no fact names `staticInstruction` or `memoryInstruction`.
open CIL.Safety in
theorem asRef_fact_stack (body : CIL.Method) (frame : Frame) (memory : Memory)
    (reference : Reference) (formed : form memory reference = .ok reference) :
    ∃ stack, modelStep (some (.memory .asRef)) body 0 frame [.reference (.address reference)] memory =
      .ok (.next 1 stack frame memory) ∧ stack = [.reference (.address reference)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [formed]
  · rfl

open CIL.Safety in
theorem load128_fact_stack (body : CIL.Method) (frame : Frame) (memory : Memory)
    (source : ManagedReference) (value : BitVec 128)
    (loaded : loadValue memory source 16 = .ok (.v128 value)) :
    ∃ stack, modelStep (some (.memory .load128)) body 0 frame [.reference source] memory =
      .ok (.next 1 stack frame memory) ∧ stack = [.scalar (.v128 value)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [loaded]
  · rfl

open CIL.Safety in
theorem add_fact_stack (body : CIL.Method) (frame : Frame) (memory : Memory)
    (base result : Reference) (offset : CIL.W32)
    (moved : add memory base 8 (BitVec.ofInt 64 offset.toInt) = .ok result) :
    ∃ stack, modelStep (some (.memory (.add 8 true))) body 0 frame
      [.scalar (.i32 offset), .reference (.address base)] memory =
      .ok (.next 1 stack frame memory) ∧ stack = [.reference (.address result)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [moved]
  · rfl

-- A symbolic managed reference stays `referenceAt reference`, so the caller's fact about it applies.
open CIL.Safety in
theorem add_symbolic_reference (body : CIL.Method) (frame : Frame) (memory : Memory)
    (reference : ManagedReference) (base result : Reference) (offset : CIL.W32)
    (addressed : referenceAt reference = .ok base)
    (moved : add memory base 8 (BitVec.ofInt 64 offset.toInt) = .ok result) :
    ∃ stack, modelStep (some (.memory (.add 8 true))) body 0 frame
      [.scalar (.i32 offset), .reference reference] memory =
      .ok (.next 1 stack frame memory) ∧ stack = [.reference (.address result)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [addressed, moved]
  · rfl

-- An unknown scalar keeps its guard: the equation exposes it rather than assuming it away.
open CIL.Safety in
example (body : CIL.Method) (frame : Frame) (memory : Memory) (value : CIL.Value) :
    modelStep (some (.memory (.bitcastValue (.aggregate 32) .vector256))) body 0 frame [.scalar value] memory =
      if value.hasUnspecified then .error (.unsupported "Instruction observes unspecified vector bits") else do
        let cast ← bitcastValue (.aggregate 32) .vector256 value
        return .next 1 [.scalar cast] frame memory := by
  simp only [cil_step]

-- `cil_step` reduces the pushed `evaluate` to the field; a fact stated through `evaluate` still decides the test.
theorem feature_step_evaluate_fact (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (wide : profile.evaluate .avx2 = true) (found : program[index]? = some (featureTestBody profile))
    (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke program 3 index [] memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [wide]

theorem feature_step_evaluate_free_body (program : CIL.Program) (index : Nat) (body : CIL.Method)
    (wide : body.profile.evaluate .avx2 = false) (unlinked : body.linkAt 0 = none)
    (code : body.code = [.call (Tests.supportedGetter "X86.Avx2"), .ret])
    (returns : body.returnsValue = true) (found : program[index]? = some body)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) :
    CIL.Safety.run program 3 index 0 [] frame [] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i32 0)]) := by
  cases narrow : body.returnNarrow <;> cil_checked_steps [unlinked, wide, code, returns, narrow]

-- A supplied proof term, not just a local name, is normalized to the profile field.
theorem feature_step_evaluate_term (body : CIL.Method) (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory)
    (unlinked : body.linkAt 0 = none) (wide : body.profile.evaluate .avx2 = true) :
    CIL.Safety.step body (.call (Tests.supportedGetter "X86.Avx2")) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [unlinked, (show body.profile.evaluate .avx2 = true from wide)]

theorem feature_steps_evaluate_term (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (wide : profile.evaluate .avx2 = true) (found : program[index]? = some (featureTestBody profile))
    (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke program 3 index [] memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [(show profile.evaluate .avx2 = true from wide)]

-- A fact over every feature is instantiated at each constructor, so it still decides the field test.
theorem feature_step_evaluate_forall (body : CIL.Method) (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory)
    (unlinked : body.linkAt 0 = none) (all : ∀ f, body.profile.evaluate f = true) :
    CIL.Safety.step body (.call (Tests.supportedGetter "X86.Avx2")) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [unlinked, all]

theorem feature_steps_evaluate_forall (program : CIL.Program) (index : Nat) (body : CIL.Method)
    (all : ∀ f, body.profile.evaluate f = false) (unlinked : body.linkAt 0 = none)
    (code : body.code = [.call (Tests.supportedGetter "X86.Avx2"), .ret])
    (returns : body.returnsValue = true) (found : program[index]? = some body)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) :
    CIL.Safety.run program 3 index 0 [] frame [] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i32 0)]) := by
  cases narrow : body.returnNarrow <;> cil_checked_steps [unlinked, all, code, returns, narrow]

/-- A fact about a symbolic feature rewrites the pushed test by hand: `cil_step` keeps
    `body.profile.evaluate f` folded instead of splitting on `f`. -/
theorem feature_step_symbolic_fact (body : CIL.Method) (frame : CIL.Safety.Frame)
    (memory : CIL.Safety.Memory) (feature : CIL.Feature) (getter : CIL.Extraction.MethodRef)
    (unlinked : body.linkAt 0 = none)
    (model : CIL.Extraction.runtimeModel body.environment .call getter = some (.feature feature))
    (enabled : body.profile.evaluate feature = true) :
    CIL.Safety.step body (.call getter) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  rw [CIL.Safety.step_call_feature _ _ _ _ _ unlinked model rfl]
  simp only [enabled, ite_true]

open Lean Elab Tactic in
/-- Fails if normalising `facts` restates any of them as a new hypothesis. -/
elab "expect_facts_already_normal " "[" facts:term,* "]" : tactic => do
  let config ← `(Lean.Parser.Tactic.optConfig|)
  let prepared ← CIL.Safety.normaliseStepFacts config facts.getElems
  unless prepared.size == facts.getElems.size do
    throwError "normalisation restated {prepared.size - facts.getElems.size} facts"

/-- Checked stepping uses the fact as stated: the normaliser leaves a symbolic feature test
    folded, as the step leaves it, rather than restating the fact as a match on `f`. -/
theorem checked_symbolic_feature_fact (body : CIL.Method) (frame : CIL.Safety.Frame)
    (memory : CIL.Safety.Memory) (feature : CIL.Feature) (getter : CIL.Extraction.MethodRef)
    (unlinked : body.linkAt 0 = none)
    (model : CIL.Extraction.runtimeModel body.environment .call getter = some (.feature feature))
    (disabled : body.profile.evaluate feature = false) :
    CIL.Safety.step body (.call getter) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 0)] frame memory) := by
  expect_facts_already_normal [disabled]
  cil_checked_step [unlinked, model, disabled]

/-- info: 'Tests.Automation.feature_step_symbolic_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_symbolic_fact
/--
info: 'Tests.Automation.checked_symbolic_feature_fact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms checked_symbolic_feature_fact

-- A global theorem stated through `evaluate` is normalized like a local fact.
def wideProfile : CIL.FeatureProfile := { avx2 := true }

theorem wideProfile_avx2 : wideProfile.evaluate .avx2 = true := rfl

attribute [irreducible] wideProfile

theorem feature_step_evaluate_global (body : CIL.Method) (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory)
    (unlinked : body.linkAt 0 = none) (profile : body.profile = wideProfile) :
    CIL.Safety.step body (.call (Tests.supportedGetter "X86.Avx2")) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [unlinked, profile, wideProfile_avx2]

-- A fact on a method's profile projection lands where `cil_step` reduces the projection.
theorem feature_step_projection_fact (profile : CIL.FeatureProfile) (frame : CIL.Safety.Frame)
    (memory : CIL.Safety.Memory) (wide : (featureTestBody profile).profile.evaluate .avx2 = true) :
    CIL.Safety.step (featureTestBody profile) (.call (Tests.supportedGetter "X86.Avx2")) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [wide]

theorem feature_steps_projection_fact (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (wide : (featureTestBody profile).profile.evaluate .avx2 = true)
    (found : program[index]? = some (featureTestBody profile)) (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke program 3 index [] memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [wide]

theorem feature_step_projection_field (profile : CIL.FeatureProfile) (frame : CIL.Safety.Frame)
    (memory : CIL.Safety.Memory) (wide : (featureTestBody profile).profile.avx2 = true) :
    CIL.Safety.step (featureTestBody profile) (.call (Tests.supportedGetter "X86.Avx2")) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [wide]

-- Quantified feature facts given as proof terms or global theorems are instantiated like local ones.
theorem feature_step_forall_term (body : CIL.Method) (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory)
    (unlinked : body.linkAt 0 = none) (all : ∀ f, body.profile.evaluate f = true) :
    CIL.Safety.step body (.call (Tests.supportedGetter "X86.Avx2")) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [unlinked, (show ∀ f, body.profile.evaluate f = true from all)]

def bareProfile : CIL.FeatureProfile := {}

theorem bareProfile_none : ∀ f, bareProfile.evaluate f = false := by intro f; cases f <;> rfl

attribute [irreducible] bareProfile

theorem feature_step_forall_global (body : CIL.Method) (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory)
    (unlinked : body.linkAt 0 = none) (profile : body.profile = bareProfile) :
    CIL.Safety.step body (.call (Tests.supportedGetter "X86.Avx2")) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 0)] frame memory) := by
  cil_checked_step [unlinked, profile, bareProfile_none]

-- Pointer arithmetic in the run loop steps without a `referenceAt` fact.
private def addUInt64 : CIL.Extraction.MethodRef :=
  let element := CIL.Extraction.TypeExpr.primitive .uint64
  let offset := CIL.Extraction.TypeExpr.primitive .int32
  { owner := CIL.Extraction.unsafeOwner, name := name!"Add", hasThis := false,
    genericArity := 1, methodArguments := [element], parameters := [.byref element, offset],
    returnType := .byref element }

@[cil_code] def addBody : CIL.Method :=
  { returnsValue := true, locals := [], code := [.ldarg 0, .ldc_i4 8, .call addUInt64, .pop,
      .ldc_i4 1, .ret] }

cil_runtime_models addBody

open CIL.Safety in
theorem add_run (memory : Memory) (source moved : Reference)
    (formed : form memory source = .ok source)
    (shifted : add memory source 8 (BitVec.ofInt 64 (BitVec.ofInt 32 8).toInt) = .ok moved) :
    invoke [addBody] 6 0 [.reference (.address source)] memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [formed, shifted]

-- A missing memory fact reports the per-shape goal, not the legacy `staticInstruction` match.
open CIL.Safety in
/--
error: Tactic `rfl` failed: The left-hand side
  match
    match
      match form memory reference with
      | Except.error err => Except.error (ExecutionFault.memory err (ManagedReference.address reference) 0)
      | Except.ok v => Except.ok v with
    | Except.error err => Except.error err
    | Except.ok v => Except.ok (Value.reference (ManagedReference.address v)) with
  | Except.error err => Except.error err
  | Except.ok v => Except.ok (FrameAction.next 1 [v] frame memory)
is not definitionally equal to the right-hand side
  Except.ok (FrameAction.next 1 [Value.reference (ManagedReference.address reference)] frame memory)

body : CIL.Method
frame : Frame
memory : Memory
reference : Reference
⊢ (match
      match
        match form memory reference with
        | Except.error err => Except.error (ExecutionFault.memory err (ManagedReference.address reference) 0)
        | Except.ok v => Except.ok v with
      | Except.error err => Except.error err
      | Except.ok v => Except.ok (Value.reference (ManagedReference.address v)) with
    | Except.error err => Except.error err
    | Except.ok v => Except.ok (FrameAction.next 1 [v] frame memory)) =
    Except.ok (FrameAction.next 1 [Value.reference (ManagedReference.address reference)] frame memory)
-/
#guard_msgs in
example (body : CIL.Method) (frame : Frame) (memory : Memory) (reference : Reference) :
    modelStep (some (.memory .asRef)) body 0 frame [.reference (.address reference)] memory =
      .ok (.next 1 [.reference (.address reference)] frame memory) := by
  cil_checked_step []

open CIL.Safety in
theorem literal_stack_cleanup (program : CIL.Program) (frame : Frame) (memory : Memory)
    (value : Value) (fuel : Nat) :
    run program fuel 0 0 [] frame (([value].reverse ++ []).drop 0) memory =
      run program fuel 0 0 [] frame [value] memory := by
  cil_stack_cleanup

#print axioms scalar_fact_stack
#print axioms bitcast_fact_stack
#print axioms permute_then_store
/-- info: 'Tests.Automation.permute_then_store_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms permute_then_store_value
/-- info: 'Tests.Automation.feature_step_from_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_from_fact
/-- info: 'Tests.Automation.feature_step_free_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_free_body
/-- info: 'Tests.Automation.feature_step_literal_profile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_literal_profile
/-- info: 'Tests.Automation.asRef_fact_stack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms asRef_fact_stack
/-- info: 'Tests.Automation.load128_fact_stack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms load128_fact_stack
/-- info: 'Tests.Automation.add_fact_stack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms add_fact_stack
/-- info: 'Tests.Automation.add_symbolic_reference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms add_symbolic_reference
/-- info: 'Tests.Automation.feature_step_evaluate_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_evaluate_fact
/-- info: 'Tests.Automation.feature_step_evaluate_free_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_evaluate_free_body
/-- info: 'Tests.Automation.feature_step_evaluate_term' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_evaluate_term
/-- info: 'Tests.Automation.feature_steps_evaluate_term' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_steps_evaluate_term
/-- info: 'Tests.Automation.feature_step_evaluate_forall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_evaluate_forall
/-- info: 'Tests.Automation.feature_steps_evaluate_forall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_steps_evaluate_forall
/-- info: 'Tests.Automation.feature_step_evaluate_global' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_evaluate_global
/-- info: 'Tests.Automation.feature_step_projection_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_projection_fact
/-- info: 'Tests.Automation.feature_steps_projection_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_steps_projection_fact
/-- info: 'Tests.Automation.feature_step_projection_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_projection_field
/-- info: 'Tests.Automation.feature_step_forall_term' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_forall_term
/-- info: 'Tests.Automation.feature_step_forall_global' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_step_forall_global
/-- info: 'Tests.Automation.add_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms add_run

/-- A supplied step fact is used before the op's own equation, which here cannot read the frame's slot;
    the body is `cil_code`, so the fact must be tried before the lookup unfolds it. -/
@[cil_code] def slotBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [], code := [.stloc 0, .ldloc 0, .ret] }

open CIL.Safety in
theorem step_facts_first (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (slotBody profile)) (args : List Value) (frame stored : Frame)
    (memory written : Memory) (value : CIL.W32)
    (store : step (slotBody profile) (.stloc 0) 0 args frame [.scalar (.i32 value)] memory =
      .ok (.next 1 [] stored written))
    (load : ∀ stack, step (slotBody profile) (.ldloc 0) 1 args stored stack written =
      .ok (.next 2 (.scalar (.i32 value) :: stack) stored written)) :
    run program 3 index 0 args frame [.scalar (.i32 value)] memory =
      .ok (leaveFrame stored written, [.scalar (.i32 value)]) := by
  cil_checked_steps [store, load]

/-- info: 'Tests.Automation.step_facts_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_facts_first

-- An applied lemma or a parenthesised proof is a step fact too, so it is also tried before the equation.
open CIL.Safety in
theorem applied_step_facts_first (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (slotBody profile)) (args : List Value) (frame stored : Frame)
    (memory written : Memory) (value : CIL.W32)
    (store : ∀ value : CIL.W32,
      step (slotBody profile) (.stloc 0) 0 args frame [.scalar (.i32 value)] memory =
      .ok (.next 1 [] stored written))
    (load : ∀ stack, step (slotBody profile) (.ldloc 0) 1 args stored stack written =
      .ok (.next 2 (.scalar (.i32 value) :: stack) stored written)) :
    run program 3 index 0 args frame [.scalar (.i32 value)] memory =
      .ok (leaveFrame stored written, [.scalar (.i32 value)]) := by
  cil_checked_steps [store value, (load)]

/-- info: 'Tests.Automation.applied_step_facts_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms applied_step_facts_first

/-- An extracted program's lookup unfolds the body to its literal, so a fact on the named body must still match. -/
@[cil_code] def slotMethod : CIL.Method :=
  { returnsValue := true, locals := [], code := [.stloc 0, .ldloc 0, .ret] }
@[cil_code] def slotProgram : CIL.Program := [slotMethod]

open CIL.Safety in
theorem named_body_step_facts (frame stored : Frame) (memory written : Memory) (value : CIL.W32)
    (store : step slotMethod (.stloc 0) 0 [] frame [.scalar (.i32 value)] memory =
      .ok (.next 1 [] stored written))
    (load : ∀ stack, step slotMethod (.ldloc 0) 1 [] stored stack written =
      .ok (.next 2 (.scalar (.i32 value) :: stack) stored written)) :
    run slotProgram 3 0 0 [] frame [.scalar (.i32 value)] memory =
      .ok (leaveFrame stored written, [.scalar (.i32 value)]) := by
  cil_checked_steps [store, load]

/-- info: 'Tests.Automation.named_body_step_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms named_body_step_facts

-- A fact quantified over the body matches the literal directly.
open CIL.Safety in
theorem quantified_body_step_facts (frame stored : Frame) (memory written : Memory) (value : CIL.W32)
    (store : ∀ body pc args, step body (.stloc 0) pc args frame [.scalar (.i32 value)] memory =
      .ok (.next (pc + 1) [] stored written))
    (load : ∀ body pc args stack, step body (.ldloc 0) pc args stored stack written =
      .ok (.next (pc + 1) (.scalar (.i32 value) :: stack) stored written)) :
    run slotProgram 3 0 0 [] frame [.scalar (.i32 value)] memory =
      .ok (leaveFrame stored written, [.scalar (.i32 value)]) := by
  cil_checked_steps [store, load]

/-- info: 'Tests.Automation.quantified_body_step_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms quantified_body_step_facts

open CIL.Safety in
/-- A supplied step fact is found after an earlier tactic `have` wraps the target in metadata;
    the `stloc` equation alone cannot read the abstract frame's slot. -/
theorem step_fact_after_have (frame stored : Frame) (memory written : Memory) (value : CIL.W32)
    (store : step slotMethod (.stloc 0) 0 [] frame [.scalar (.i32 value)] memory =
      .ok (.next 1 [] stored written)) :
    step slotMethod (.stloc 0) 0 [] frame [.scalar (.i32 value)] memory =
      .ok (.next 1 [] stored written) := by
  have unchanged : value = value := rfl
  cil_checked_step [store]

/-- info: 'Tests.Automation.step_fact_after_have' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_fact_after_have

@[cil_code] def nonzeroMethod : CIL.Method := {
  code := [.ldarg 0, .brtrue 4, .ldarg 1, .ret, .ldarg 0, .ret]
  locals := [], returnsValue := true }

-- A branch pc is decided from the condition's own fact, not only from a `CIL.truth` restatement.
theorem branch_from_nonzero (memory : CIL.Safety.Memory) (condition value : CIL.W32) (nonzero : ¬ condition = 0) :
    CIL.Safety.invoke branchProgram (CIL.executionBound branchProgram 0) 0
      [.scalar (.i32 condition), .scalar (.i32 value)] memory = .ok (memory, [.scalar (.i32 value)]) := by
  cil_checked_steps [nonzero]

theorem nonzero_branch_from_nonzero (memory : CIL.Safety.Memory) (condition value : CIL.W32)
    (nonzero : ¬ condition = 0) :
    CIL.Safety.invoke [nonzeroMethod] 9 0
      [.scalar (.i32 condition), .scalar (.i32 value)] memory = .ok (memory, [.scalar (.i32 condition)]) := by
  cil_checked_steps [nonzero]

theorem branch_from_zero (memory : CIL.Safety.Memory) (condition value : CIL.W32) (zero : condition = 0) :
    CIL.Safety.invoke branchProgram (CIL.executionBound branchProgram 0) 0
      [.scalar (.i32 condition), .scalar (.i32 value)] memory = .ok (memory, [.scalar (.i32 value)]) := by
  cil_checked_steps [zero]

-- A literal condition is decided by evaluation, with no fact at all.
@[cil_code] def literalBranchMethod : CIL.Method := {
  code := [.ldc_i4 5, .brtrue 4, .ldarg 0, .ret, .ldarg 1, .ret]
  locals := [], returnsValue := true }

theorem literal_branch (memory : CIL.Safety.Memory) (condition value : CIL.W32) :
    CIL.Safety.invoke [literalBranchMethod] 9 0
      [.scalar (.i32 condition), .scalar (.i32 value)] memory = .ok (memory, [.scalar (.i32 value)]) := by
  cil_checked_steps []

#print axioms branch_from_nonzero
#print axioms branch_from_zero
#print axioms literal_branch
#print axioms nonzero_branch_from_nonzero

/-- A body whose instructions, not its code list, depend on a feature. -/
def featureOpBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, environment := wordsEnvironment, returnsValue := true, locals := [],
    code := [if profile.avx2 then .ldarg 1 else .ldarg 0, .ldfld word0, .ret] }

-- The lookup decides the feature test, so the fetched op is a constructor with a step equation.
-- A term-mode `by`, as the contract and loop tactics call it, must still assign the op.
example (profile : CIL.FeatureProfile) (scalar : profile.avx2 = false) :
    ∃ op, (featureOpBody profile).code[0]? = some op ∧ op = .ldarg 0 :=
  ⟨_, by cil_lookup [scalar], by with_reducible rfl⟩

open CIL.Safety in
theorem feature_op_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (scalar : profile.avx2 = false) (found : program[index]? = some (featureOpBody profile))
    (frame : Frame) (memory : Memory) (left right : Reference) (limb : BitVec 64)
    (formed : form memory left = .ok left)
    (field : ∀ rest, loadValueField 0 8 false (.reference (.address left) :: rest) memory =
      .ok (memory, .scalar (.i64 limb) :: rest)) :
    run program 4 index 0 [.reference (.address left), .reference (.address right)] frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i64 limb)]) := by
  cil_checked_steps [scalar, formed, field]

/-- info: 'Tests.Automation.feature_op_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms feature_op_checked

def reverseLanes (v : CIL.Vector.V256) : CIL.Vector.V256 := CIL.Vector.permute4x64 v 27

-- Stated with a literal control, as a consumer writes it; the operand arrives as `BitVec.ofNat 32 27`.
theorem eval_reverse_lanes (v : CIL.Vector.V256) :
    CIL.evalIntrinsic (.avx2 .permute4x64) [.v256 v, .i32 27] = some (.v256 (reverseLanes v)) := rfl

#print axioms eval_reverse_lanes

-- The pushed value is the evaluation fact's, so the store fact on `reverseLanes v` applies next.
open CIL.Safety in
theorem evaluated_then_stored (v : CIL.Vector.V256) (destination : Reference) (memory final : Memory)
    (stored : ∀ rest, memoryInstruction .store256
      (.scalar (.v256 (reverseLanes v)) :: .reference (.address destination) :: rest) memory = .ok (final, rest)) :
    run permuteStoreProgram 3 0 0 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.i32 (BitVec.ofInt 32 27)), .scalar (.v256 v), .reference (.address destination)] memory =
      .ok (final, []) := by
  cil_checked_steps [stored, eval_reverse_lanes]

#print axioms evaluated_then_stored

-- Literal operands are respelled for the evaluation fact; a symbolic slot below them keeps its form.
open CIL.Safety in
theorem evaluated_keeps_symbolic_slot (v : CIL.Vector.V256) (destination : Reference) (memory : Memory) (x : Nat)
    (k : Except LocatedFault (Memory × List Value))
    (rest : run permuteStoreProgram 2 0 1 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.v256 (reverseLanes v)), .reference (.address destination), .scalar (.i32 (BitVec.ofNat 32 x))]
      memory = k) :
    run permuteStoreProgram 3 0 0 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.i32 (BitVec.ofInt 32 27)), .scalar (.v256 v), .reference (.address destination),
        .scalar (.i32 (BitVec.ofNat 32 x))] memory = k := by
  cil_checked_run_step [eval_reverse_lanes]
  with_reducible exact rest

#print axioms evaluated_keeps_symbolic_slot

-- An applied hypothesis with a numeral operand also enables the respelling pass.
open CIL.Safety in
theorem evaluated_by_applied_hypothesis (v : CIL.Vector.V256) (destination : Reference) (memory : Memory)
    (k : Except LocatedFault (Memory × List Value))
    (eval : ∀ w, CIL.evalIntrinsic (.avx2 .permute4x64) [.v256 w, .i32 27] = some (.v256 (reverseLanes w)))
    (rest : run permuteStoreProgram 2 0 1 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.v256 (reverseLanes v)), .reference (.address destination)] memory = k) :
    run permuteStoreProgram 3 0 0 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.i32 (BitVec.ofInt 32 27)), .scalar (.v256 v), .reference (.address destination)] memory = k := by
  cil_checked_run_step [eval v]
  with_reducible exact rest

#print axioms evaluated_by_applied_hypothesis

-- A bare step with no supplied facts still evaluates an intrinsic through the `@[cil_eval]` lemmas.
open CIL.Safety in
theorem intrinsic_without_facts (a b c d : CIL.W64) (destination : Reference) (memory : Memory)
    (k : Except LocatedFault (Memory × List Value))
    (rest : run permuteStoreProgram 2 0 1 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.v256 (CIL.Vector.pack256 d c b a)), .reference (.address destination)] memory = k) :
    run permuteStoreProgram 3 0 0 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.i32 (BitVec.ofInt 32 27)), .scalar (.v256 (CIL.Vector.pack256 a b c d)),
        .reference (.address destination)] memory = k := by
  cil_checked_run_step []
  with_reducible exact rest

/-- info: 'Tests.Automation.intrinsic_without_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intrinsic_without_facts

@[cil_code] def checkedAdd64Method : CIL.Method := {
  code := [.ldarg 0, .ldarg 1, .add_ovf_un, .ret]
  locals := [], returnsValue := true }
@[cil_code] def checkedAdd64Program : CIL.Program := [checkedAdd64Method]

-- Keep the checked-add/return proof within the default kernel recursion limit.
-- Eagerly unfolding checkedAt and formValue in the generic fallback made this fail.
open CIL CIL.Safety in
theorem checked_add64_return (memory : CIL.Safety.Memory) (x y : W64) (fits : x.toNat + y.toNat < 2^64) :
    CIL.Safety.invoke checkedAdd64Program (executionBound checkedAdd64Program 0) 0
      [.scalar (.i64 x), .scalar (.i64 y)] memory =
        .ok (memory, [.scalar (.i64 (BitVec.ofNat 64 (x.toNat + y.toNat)))]) := by
  have calculation : checkedValues .add false (.i64 x) (.i64 y) =
      .ok (.i64 (BitVec.ofNat 64 (x.toNat + y.toNat))) := by
    have range : 0 ≤ (x.toNat : Int) + y.toNat ∧ (x.toNat : Int) + y.toNat < 2^64 := by omega
    simp only [checkedValues, checkedBits, Bool.false_eq_true, ite_false]
    rw [ite_eq_left range]
    rfl
  cil_checked_steps [calculation]

#print axioms checked_add64_return

open CIL.Safety in
/-- A dispatch fact preserves its abstract value when the step infers the next stack. -/
theorem bitcast_dispatch_keeps_value (body : CIL.Method) (frame : Frame)
    (memory : Memory) (byte : BitVec 8) (value : BitVec 256)
    (casted : memoryInstruction (.bitcastValue (.aggregate 32) .vector256)
      [.scalar (.aggregate (List.replicate 32 byte))] memory =
        .ok (memory, [.scalar (.v256 value)])) :
    ∃ stack, modelStep (some (.memory (.bitcastValue (.aggregate 32) .vector256))) body 0 frame
      [.scalar (.aggregate (List.replicate 32 byte))] memory =
        .ok (.next 1 stack frame memory) ∧ stack = [.scalar (.v256 value)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [casted]
  · rfl

#print axioms bitcast_dispatch_keeps_value

open CIL.Safety in
/-- The same abstract result is retained for a fact at the static dispatch boundary. -/
theorem bitcast_static_keeps_value (body : CIL.Method) (frame : Frame)
    (memory : Memory) (byte : BitVec 8) (value : BitVec 256)
    (casted : staticInstruction body 0 (.bitcastValue (.aggregate 32) .vector256)
      [.scalar (.aggregate (List.replicate 32 byte))] memory =
        .ok (memory, [.scalar (.v256 value)])) :
    ∃ stack, modelStep (some (.memory (.bitcastValue (.aggregate 32) .vector256))) body 0 frame
      [.scalar (.aggregate (List.replicate 32 byte))] memory =
        .ok (.next 1 stack frame memory) ∧ stack = [.scalar (.v256 value)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [casted]
  · rfl

#print axioms bitcast_static_keeps_value

open CIL.Safety in
/-- A conjunction-wrapped dispatch fact remains usable through the generic fallback. -/
theorem store_from_wrapped_fact (body : CIL.Method) (frame : Frame)
    (bits : BitVec 256) (destination : Reference) (memory final : Memory)
    (stored : True ∧ memoryInstruction .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    modelStep (some (.memory .store256)) body 2 frame
      [.scalar (.v256 bits), .reference (.address destination)] memory =
      .ok (.next 3 [] frame final) := by
  cil_checked_step_normalized [stored]

#print axioms store_from_wrapped_fact

private def byteToBoolean : CIL.Extraction.MethodRef :=
  let source := CIL.Extraction.TypeExpr.primitive .byte
  let target := CIL.Extraction.TypeExpr.primitive .boolean
  { owner := CIL.Extraction.unsafeOwner, name := name!"BitCast", hasThis := false,
    genericArity := 2, methodArguments := [source, target], parameters := [source],
    returnType := target }

/-- Compare two words and reinterpret the result as a Boolean. -/
@[cil_code] def comparedBoolean : CIL.Method := {
  code := [.ldarg 0, .ldarg 1, .ceq, .call byteToBoolean, .ret]
  locals := [], returnsValue := true }

cil_runtime_models comparedBoolean

open CIL.Safety in
/-- A comparison result is a canonical Boolean whatever its condition, so the reinterpretation
    steps without a fact; an arbitrary int32 would still need its bound. -/
theorem compared_boolean_cast (left right : CIL.W64) (memory : Memory) :
    invoke [comparedBoolean] 6 0 [.scalar (.i64 left), .scalar (.i64 right)] memory =
      .ok (memory, [.scalar (.i32 (if left = right then 1 else 0))]) := by
  cil_checked_steps []

#print axioms compared_boolean_cast

open CIL.Safety in
/-- A Boolean cast of an unconstrained int32 keeps its canonical-range obligation. -/
theorem unconstrained_boolean_cast (body : CIL.Method) (frame : Frame) (bits : CIL.W32)
    (memory : Memory) (canonical : bits.toNat ≤ 1) :
    modelStep (some (.memory .bitcastByteBool)) body 0 frame [.scalar (.i32 bits)] memory =
      .ok (.next 1 [.scalar (.i32 bits)] frame memory) := by
  fail_if_success cil_checked_step []
  cil_checked_step [canonical]

#print axioms unconstrained_boolean_cast

open CIL.Safety in
/-- A canonical bit stays canonical through the byte and int32 widths a field load gives it,
    so its bound steps the Boolean cast of the widened value. -/
theorem widened_boolean_cast (body : CIL.Method) (frame : Frame) (field : CIL.W64)
    (memory : Memory) (canonical : field.toNat ≤ 1) :
    modelStep (some (.memory .bitcastByteBool)) body 0 frame
        [.scalar (.i32 ((field.setWidth 8).setWidth 32))] memory =
      .ok (.next 1 [.scalar (.i32 ((field.setWidth 8).setWidth 32))] frame memory) := by
  fail_if_success cil_checked_step []
  cil_checked_step [canonical]

#print axioms widened_boolean_cast

open CIL.Safety in
/-- A value known only to be numeric loads as a plain argument: the facts meet the argument
    access and the checked value test in the unfolded form stepping leaves them in. -/
theorem opaque_numeric_argument (body : CIL.Method) (frame : Frame) (argument : CIL.Value)
    (memory : Memory) (plain : body.argumentAccess 0 = .value none)
    (numeric : numericValue argument = true) :
    step body (.ldarg 0) 0 [.scalar argument] frame [] memory =
      .ok (.next 1 [.scalar argument] frame memory) := by
  fail_if_success cil_checked_step [numeric]
  cil_checked_step [plain, numeric]

#print axioms opaque_numeric_argument

open CIL.Safety in
/-- The same fact passes an opaque numeric value to a call. -/
theorem opaque_numeric_call (body : CIL.Method) (frame : Frame) (argument : CIL.Value)
    (memory : Memory) (numeric : numericValue argument = true)
    (known : argument.hasUnspecified = false) (linked : body.linkAt 0 = some (.direct 1)) :
    step body (.call (Tests.callee 1)) 0 [] frame [.scalar argument] memory =
      .ok (.call 1 [.scalar argument] [] memory) := by
  fail_if_success cil_checked_step [known, linked]
  cil_checked_step [numeric, known, linked]

#print axioms opaque_numeric_call

open CIL.Safety in
/-- A read introduced by `have name := term` states its type through an assigned
    metavariable; its load is derived like that of a hypothesis with a written type. -/
theorem inferred_read_load (memory : Memory) (limb : Reference) (word : CIL.W64)
    (loaded : read memory limb 8 1 = .ok (numberBytes word.toNat 8))
    (body : CIL.Method) (frame : Frame) :
    step body (.ldind .i8) 0 [] frame [.reference (.address limb)] memory =
      .ok (.next 1 [.scalar (.i64 word)] frame memory) := by
  have restated := loaded
  clear loaded
  cil_checked_step [restated]

#print axioms inferred_read_load

open Lean in
/-- A step names its hypotheses from the first suffix that leaves every base unused, found in
    one pass: suffixes in use are skipped, and spellings no step produces are not counted. -/
example : True := by
  run_tac do
    let declare (context : LocalContext) (name : String) : MetaM LocalContext :=
      return context.mkLocalDecl (← mkFreshFVarId) (Name.mkSimple name) (mkConst ``Nat)
    let bases := #["stored", "written"]
    let mut context : LocalContext := {}
    unless CIL.firstUnusedSuffix context bases == 0 do throwError "an empty context uses no suffix"
    for name in
        ["stored_1", "written_2", "stored_01", "stored_0", "other", "other_1", "stored1"] do
      context ← declare context name
    unless CIL.firstUnusedSuffix context bases == 0 do
      throwError "names that no step produces made suffix 0 look used"
    context ← declare context "written"
    unless CIL.firstUnusedSuffix context bases == 3 do
      throwError "suffixes 0, 1 and 2 are in use, so the first free suffix is 3"
  trivial

open Lean in
/-- Choosing a suffix against a context takes one pass over it, so four times as many names cost
    about four times as many heartbeats; a probe per suffix costs sixteen times as many. -/
example : True := by
  run_tac do
    let cost (names : Nat) : MetaM Nat := do
      let mut context : LocalContext := {}
      for index in [:names] do
        let name := if index == 0 then "stored" else s!"stored_{index}"
        context := context.mkLocalDecl (← mkFreshFVarId) (Name.mkSimple name) (mkConst ``Nat)
      let started ← IO.getNumHeartbeats
      let suffix ← IO.lazyPure fun _ => CIL.firstUnusedSuffix context #["stored", "written"]
      unless suffix == names do throwError "expected suffix {names}, found {suffix}"
      return (← IO.getNumHeartbeats) - started
    let small ← cost 2000
    let large ← cost 8000
    unless large * 10 < small * 54 do
      throwError "choosing a suffix cost {small} heartbeats at 2000 names and {large} at 8000"
  trivial

/-! ### The record of normal-form nodes

A stepping driver skips the terms that earlier steps of the run left unchanged. These tests check
what the record keeps, when it is dropped, and that skipping never changes the goal a step
leaves. `cil.stepping.record` turns it off to give the goal that plain simplification reaches. -/

open CIL.Safety

-- The record is used from the first step here; a driver uses it after a dozen steps.
set_option cil.stepping.warmup 0

open Lean Elab Tactic Meta in
/-- The goal that `steps` leaves, with the record of normal-form nodes on or off. The state is
    restored afterwards. -/
def steppedTarget (record : Bool) (steps : TSyntax `tactic) : TacticM Expr := do
  let saved ← saveState
  try
    withOptions (fun options => cil.stepping.record.set options record) (evalTactic steps)
    instantiateMVars (← getMainTarget)
  finally saved.restore

open Lean Elab Tactic Meta in
/-- Fails unless `steps` leaves the same goal with the record and without it. -/
def sameGoal (steps : TSyntax `tactic) : TacticM Unit := do
  let recorded ← steppedTarget true steps
  let plain ← steppedTarget false steps
  unless recorded == plain do
    throwError "the record changed the goal:{indentExpr recorded}\n\
      against plain:{indentExpr plain}"

open Lean Elab Tactic in
/-- Whether a record is active or kept. -/
def recordIsLeft : TacticM Bool := do
  let record ← getNormalNodes
  return record.driven || record.active || !record.nodes.isEmpty ||
    record.equations.covered != 0 || record.equationLocals.isSome ||
    !record.contexts.isEmpty || !record.others.isEmpty

open Lean Elab Tactic in
/-- Fails unless no record is active or kept. -/
def recordIsEmpty : TacticM Unit := do
  if ← recordIsLeft then throwError "a stepping record outlived its run"

/-- Adds two arguments. -/
@[cil_code] def recordBody : CIL.Method := {
  code := [.ldarg 0, .ldarg 1, .add, .ret], locals := [], returnsValue := true }

/-- The program of `recordBody`. -/
@[cil_code] def recordProgram : CIL.Program := [recordBody]

/-- Adds the arguments in the other order, so its goals differ from those of `recordBody`. -/
@[cil_code] def otherBody : CIL.Method := {
  code := [.ldarg 1, .ldarg 0, .add, .ret], locals := [], returnsValue := true }

/-- The program of `otherBody`. -/
@[cil_code] def otherProgram : CIL.Program := [otherBody]

section
-- Declarations rather than theorems, elaborated on the main branch, keep what a failure leaves.
set_option Elab.async false

-- A step that cannot fetch its instruction fails inside the run, which leaves no record.
#guard_msgs (drop all) in
theorem failedRun (memory : Memory) (frame : Frame) :
    ∃ result, run recordProgram 5 7 0 [] frame [] memory = result :=
  ⟨_, by cil_checked_steps 1 []⟩

/-- The declaration after a failed run finds no record, and steps to the goal that plain
    simplification gives for a different body. -/
theorem runAfterFailure (memory : Memory) (frame : Frame) (left right : CIL.W64) :
    run otherProgram 5 0 0 [.scalar (.i64 left), .scalar (.i64 right)] frame [] memory =
      run otherProgram 3 0 2 [.scalar (.i64 left), .scalar (.i64 right)] frame
        [.scalar (.i64 left), .scalar (.i64 right)] memory := by
  run_tac recordIsEmpty
  run_tac sameGoal (← `(tactic| cil_checked_steps 1 []))
  cil_checked_steps 2 []
  all_goals rfl

-- A bare step that fails drops the record it started.
#guard_msgs (drop all) in
theorem failedBareStep (memory : Memory) (frame : Frame) :
    ∃ result, run recordProgram 5 7 0 [] frame [] memory = result :=
  ⟨_, by cil_checked_run_step []⟩

/-- The declaration after a failed bare step finds no record. -/
theorem runAfterBareFailure : True := by
  run_tac recordIsEmpty
  trivial

/-- A `first` alternative that steps and then fails leaves no record to the next alternative. -/
theorem backtracked (memory : Memory) (frame : Frame) (left right : CIL.W64) :
    run recordProgram 5 0 0 [.scalar (.i64 left), .scalar (.i64 right)] frame [] memory =
      run recordProgram 3 0 2 [.scalar (.i64 left), .scalar (.i64 right)] frame
        [.scalar (.i64 right), .scalar (.i64 left)] memory := by
  first
  | (cil_checked_steps 2 []; fail "undone")
  | (cil_checked_run_step []; fail "undone")
  | run_tac recordIsEmpty
  cil_checked_steps 2 []
  all_goals rfl

open Lean Elab Tactic in
/-- A diagnostic that steps and restores its state leaves no record behind. -/
theorem diagnosed (memory : Memory) (frame : Frame) (left right : CIL.W64) :
    run recordProgram 5 0 0 [.scalar (.i64 left), .scalar (.i64 right)] frame [] memory =
      run recordProgram 3 0 2 [.scalar (.i64 left), .scalar (.i64 right)] frame
        [.scalar (.i64 right), .scalar (.i64 left)] memory := by
  run_tac do
    let saved ← saveState
    evalTactic (← `(tactic| cil_checked_run_step []))
    saved.restore
  run_tac recordIsEmpty
  cil_checked_steps 2 []
  all_goals rfl

open Lean Elab Tactic in
/-- A completed bare step leaves no step running, so a later simplification is plain. -/
theorem completedBareStep (memory : Memory) (frame : Frame) (left right : CIL.W64) :
    run recordProgram 5 0 0 [.scalar (.i64 left), .scalar (.i64 right)] frame [] memory =
      run recordProgram 3 0 2 [.scalar (.i64 left), .scalar (.i64 right)] frame
        [.scalar (.i64 right), .scalar (.i64 left)] memory := by
  cil_checked_run_step []
  run_tac do unless !(← getNormalNodes).active do throwError "a step is still marked running"
  cil_checked_steps 1 []
  all_goals rfl

end

set_option linter.unusedVariables false in
open Lean Elab Tactic Meta in
/-- Facts that print alike but state different things are keyed apart, and a record made for one
    is not used for the other. A step that only adds hypotheses keeps the record, which a step
    that rewrites one in place does not. -/
example (one : (1 : Nat) = 1) (two : (2 : Nat) = 2) : True := by
  run_tac withMainContext do
    -- Unhygienic names, since a quoted `one` would carry a macro scope no hypothesis has.
    let first ← factsKey #[mkIdent `one]
    let second ← factsKey #[mkIdent `two]
    unless first.isSome && second.isSome && first != second do
      throwError "different facts were keyed alike"
    let hole (name : Ident) : TacticM Term := do
      Term.exprToSyntax (← elabTerm name none)
    let holeFirst ← hole (mkIdent `one)
    let holeSecond ← hole (mkIdent `two)
    unless (← factsKey #[holeFirst]) != (← factsKey #[holeSecond]) do
      throwError "facts that print alike were keyed alike"
    withNormalRun do
      let remember (facts : Array Term) : TacticM Unit :=
        withNormalNodes facts <| withMainContext <| liftM (recordNormalNodes "probe" #[mkNatLit 7])
      let recorded (facts : Array Term) : TacticM Bool :=
        withNormalNodes facts <| withMainContext <| liftM do
          return (← normalNodesFor "probe").contains (mkNatLit 7)
      remember #[holeFirst]
      unless ← recorded #[holeFirst] do
        throwError "a record was not kept between steps with the same facts"
      if ← recorded #[holeSecond] then throwError "a record was used for different facts"
      remember #[holeSecond]
      unless ← recorded #[holeFirst] do
        throwError "the record of the earlier facts was dropped when a step read other facts"
      -- Steps that add hypotheses, as stores and calls do, keep what the run recorded.
      for extra in [`extraOne, `extraTwo] do
        evalTactic (← `(tactic| have $(mkIdent extra) : True := trivial))
        unless ← recorded #[holeSecond] do
          throwError "the record was dropped when a step added the hypothesis {extra}"
        unless ← recorded #[holeFirst] do
          throwError "the record of the other facts was dropped when a step added {extra}"
      -- A hypothesis outside the facts, rewritten in place, keeps its name and identity but not
      -- what it states, and a simplification may use it.
      let goal ← getMainGoal
      let declaration ← withMainContext (getLocalDeclFromUserName `one)
      let sum ← mkAppM ``HAdd.hAdd #[mkNatLit 1, mkNatLit 0]
      replaceMainGoal [← goal.replaceLocalDeclDefEq declaration.fvarId
        (← mkEq (mkNatLit 1) sum)]
      if ← recorded #[holeSecond] then throwError "a record was used after a hypothesis changed"
    recordIsEmpty
  trivial

set_option linter.unusedVariables false in
open Lean Elab Tactic Meta in
/-- Lemmas with implicit arguments and universe parameters among the facts are keyed, so the
    run keeps the record and finds it again when the same lemmas elaborate anew. -/
example : True := by
  run_tac withMainContext do
    let facts : Array Term := #[← `(List.length_append), ← `(List.map_map)]
    withNormalRun do
      let probed : TacticM Bool := withNormalNodes facts <| withMainContext <| liftM do
        return (← normalNodesFor "probe").contains (mkNatLit 7)
      withNormalNodes facts <| withMainContext do
        unless (← getNormalNodes).active do
          throwError "lemma facts with metavariables switched the record off"
        liftM (recordNormalNodes "probe" #[mkNatLit 7])
      unless ← probed do throwError "the record was not found again for the same lemma facts"
    recordIsEmpty
  trivial

open Lean Elab Tactic Meta in
/-- The goals `cil_try_simp_only` leaves for a sequence of statements run one after another in
    one record, with the record on or off. -/
def simpSequence (record : Bool) (statements : Array Term) : TacticM (Array Expr) := do
  let saved ← saveState
  let seen ← IO.mkRef (#[] : Array Expr)
  try
    withOptions (fun options => cil.stepping.record.set options record) do
      withNormalRun do
        for statement in statements do
          let goal ← mkFreshExprMVar (← elabTerm statement none)
          setGoals [goal.mvarId!]
          withNormalNodes #[] do
            withMainContext do
              evalTactic (← `(tactic| cil_try_simp_only [Nat.reduceAdd, id_eq, Nat.add_zero]))
          seen.modify (·.push (← instantiateMVars (← getMainTarget)))
  finally saved.restore
  seen.get

set_option linter.unusedVariables false in
open Lean Elab Tactic Meta in
/-- Terms that appear first where simplification does not enter them and later where it does,
    under a binder, as a dependent argument and as an instance argument, simplify as without the
    record. -/
example (p : Nat → Prop) : True := by
  run_tac withMainContext do
    let p := mkIdent `p
    let statements : Array Term := #[← `($p (id (2 + 3))),
      ← `($p ((fun x : Nat => x + (2 + 3)) 1)),
      ← `($p (((2 + 3, 1 + 1) : Nat × Nat).1 + (2 + 3))),
      ← `($p ((⟨2 + 3, by omega⟩ : { n : Nat // n < 10 }).val + (2 + 3 + 0))),
      ← `($p (Nat.succ (2 + 3) + id (id (2 + 3))))]
    let recorded ← simpSequence true statements
    let plain ← simpSequence false statements
    for (kept, reference) in recorded.zip plain do
      unless kept == reference do
        throwError "the record changed a simplification:{indentExpr kept}\nagainst:\
          {indentExpr reference}"
  trivial

open Lean Elab Tactic Meta in
/-- The goals `cil_literal_operands` leaves for a persistent operand it cannot evaluate and an
    operand that appears later and can be evaluated, with the record on or off. -/
def literalSequence (record : Bool) : TacticM (Array Expr) := do
  let saved ← saveState
  let seen ← IO.mkRef (#[] : Array Expr)
  try
    withOptions (fun options => cil.stepping.record.set options record) do
      withNormalRun do
        let (w, a, b) := (mkIdent `w, mkIdent `a, mkIdent `b)
        for statement in #[← `(BitVec.signExtend $w (5#4) = $a),
            ← `(BitVec.signExtend $w (5#4) = $a ∧ BitVec.setWidth 8 (3#4) = $b)] do
          let goal ← mkFreshExprMVar (← elabTerm statement none)
          setGoals [goal.mvarId!]
          withNormalNodes #[] (withMainContext (evalTactic (← `(tactic| cil_literal_operands))))
          seen.modify (·.push (← instantiateMVars (← getMainTarget)))
  finally saved.restore
  seen.get

set_option linter.unusedVariables false in
open Lean Elab Tactic Meta in
/-- A persistent literal operand that cannot be evaluated does not stop a later one from being
    evaluated, and the goal is the one without the record. -/
example (w : Nat) (a : BitVec w) (b : BitVec 8) : True := by
  run_tac withMainContext do
    let recorded ← literalSequence true
    let plain ← literalSequence false
    unless recorded == plain do throwError "the record changed the literal operands"
    let [_, evaluated] := recorded.toList | throwError "expected two goals"
    unless (evaluated.find? (·.isConstOf ``BitVec.setWidth)).isNone do
      throwError "the later operand was not evaluated:{indentExpr evaluated}"
  trivial

set_option linter.unusedVariables false in
open Lean Elab Tactic Meta in
/-- The detector flags the operands the `cil_literal` simprocs evaluate and no others: a width
    conversion to a symbolic width stays, and `BitVec.ofInt` of literals is evaluated. -/
example (w : Nat) (a : BitVec w) (b : BitVec 8) : True := by
  run_tac withMainContext do
    let symbolic ← elabTerm (← `(BitVec.signExtend $(mkIdent `w) (5#4))) none
    if closedLiteralOperand symbolic then
      throwError "a conversion to a symbolic width was taken for a literal operand"
    let statement ← elabTerm (← `(BitVec.ofInt 8 (-3) = $(mkIdent `b))) none
    unless (statement.find? closedLiteralOperand).isSome do
      throwError "BitVec.ofInt of literals was not found"
    let goals ← getGoals
    setGoals [(← mkFreshExprMVar statement).mvarId!]
    evalTactic (← `(tactic| cil_literal_operands))
    let reduced ← instantiateMVars (← getMainTarget)
    unless (reduced.find? (·.isConstOf ``BitVec.ofInt)).isNone do
      throwError "BitVec.ofInt of literals was not evaluated:{indentExpr reduced}"
    setGoals goals
  trivial

open Lean Elab Tactic Meta in
/-- A term whose tree doubles at each of sixty levels, as `.dup` then `.add` build it, has sixty
    nodes as a DAG. Recording it visits each node once and costs heartbeats in proportion. -/
example : True := by
  run_tac do
    let mut shared := mkNatLit 1
    for _ in [:60] do
      shared := mkApp2 (mkConst ``Nat.add) shared shared
    let (found, (_, clean)) := (cleanWalk (fun _ => false) {} shared).run ({}, #[])
    -- Two applications per level, and the nodes of the base: far fewer than the tree's 2^60.
    unless !found && clean.size < 200 do
      throwError "expected a node count linear in the depth, found {clean.size}"
    withNormalRun do
      withNormalNodes #[] do
        recordNormalNodes "probe" clean
        unless (← getNormalNodes).count == clean.size do
          throwError "a node was recorded twice"
  trivial

set_option linter.unusedVariables false in
open Lean Elab Tactic Meta in
/-- Simplifying under a binder opens temporary free variables, and the terms that carry them can
    never occur again, so the record keeps none of them while it keeps the closed terms. The goal
    is the one that plain simplification gives. -/
example (p : Nat → Prop) : True := by
  run_tac withMainContext do
    let statement ← `(∀ x : Nat, $(mkIdent `p) (x + 0) ∧ $(mkIdent `p) (2 + 3 + (x + 0)))
    let context ← getLCtx
    let mut goals := #[]
    for record in [true, false] do
      let goal ← mkFreshExprMVar (← elabTerm statement none)
      let saved ← getGoals
      setGoals [goal.mvarId!]
      withOptions (fun options => cil.stepping.record.set options record) do
        withNormalRun do
          withNormalNodes #[] do
            withMainContext (evalTactic (← `(tactic|
              cil_try_simp_only [Nat.add_zero, Nat.reduceAdd])))
          if record then
            let kept ← getNormalNodes
            let mut recorded := 0
            for (_, nodes) in kept.nodes do
              for node in nodes.toList do
                recorded := recorded + 1
                if node.hasAnyFVar (!context.contains ·) then
                  throwError "a term with a temporary free variable was recorded:{indentExpr node}"
            if recorded == 0 then throwError "no node was recorded, so the test checks nothing"
      goals := goals.push (← instantiateMVars (← getMainTarget))
      setGoals saved
    unless goals[0]! == goals[1]! do
      throwError "the record changed the goal:{indentExpr goals[0]!}\n\
        against:{indentExpr goals[1]!}"
  trivial

open Lean Elab Tactic Meta in
/-- Every goal that `steps` leaves, with its hypotheses, as printed text, with the record on or
    off. Printing makes the comparison independent of the identifiers of fresh variables. The
    state is restored afterwards. -/
def steppedGoals (record : Bool) (steps : TSyntax `tactic) : TacticM (Array String) := do
  let saved ← saveState
  try
    withOptions (fun options => cil.stepping.record.set options record) (evalTactic steps)
    let mut printed := #[]
    for goal in ← getGoals do
      printed := printed.push (toString (← withOptions (·.setBool `pp.mvars false) (ppGoal goal)))
    return printed
  finally saved.restore

open Lean Elab Tactic in
/-- Fails unless `steps` leaves the same goals, hypotheses included, with the record and without
    it. Unless `mayClose`, it also fails when the steps close every goal, since the comparison
    would check nothing. -/
def sameGoals (steps : TSyntax `tactic) (mayClose := false) : TacticM Unit := do
  let recorded ← steppedGoals true steps
  let plain ← steppedGoals false steps
  if recorded.isEmpty && !mayClose then
    throwError "the steps closed every goal, so the test checks nothing"
  unless recorded == plain do
    throwError "the record changed the goals:\n{recorded}\nagainst plain:\n{plain}"

/-- A body the loop tactics walk: two operands added, ending in a `nop`. -/
@[cil_code] def loopRecordBody : CIL.Method := {
  code := [.ldarg 0, .ldarg 1, .add, .nop], locals := [], returnsValue := true }

/-- A body that stores an argument into a numeric local and loads it back. -/
@[cil_code] def snapshotRecordBody : CIL.Method := {
  code := [.ldarg 0, .stloc 0, .ldloc 0, .ret], locals := [.i64 0],
  localKinds := [.word64], returnsValue := true }

/-- Contract stepping leaves the goals that plain simplification gives. -/
example (memory : Memory) (left right : CIL.W64) :
    WP (Execution (fun fuel => invoke [recordBody] fuel 0
      [.scalar (.i64 left), .scalar (.i64 right)] memory))
      (fun (final, values) => final = memory ∧ values = [.scalar (.i64 (left + right))]) := by
  run_tac sameGoals (← `(tactic| cil_contract_steps 2 []))
  cil_contract_steps []
  exact ⟨rfl, rfl⟩

open Lean Elab Tactic Meta in
/-- Raise stepping leaves the goals that plain simplification gives. -/
example (memory : Memory) (left right : CIL.W64) (exception : CIL.ExceptionType) : True := by
  run_tac withMainContext do
    let original ← getGoals
    let statement ← `(Raises recordProgram 0 [.scalar (.i64 $(mkIdent `left)),
      .scalar (.i64 $(mkIdent `right))] $(mkIdent `memory) $(mkIdent `exception))
    setGoals [(← mkFreshExprMVar (← elabTerm statement none)).mvarId!]
    sameGoals (← `(tactic| cil_raise_steps []))
    setGoals original
  trivial

/-- Loop stepping leaves the goals that plain simplification gives. -/
example (memory : Memory) (left right : CIL.W64) (frame : Frame) :
    LoopReaches [loopRecordBody] 0 [.scalar (.i64 left), .scalar (.i64 right)]
      (LoopState.mk 0 frame [] memory)
      (LoopState.mk 3 frame [.scalar (.i64 (left + right))] memory) := by
  run_tac sameGoals (← `(tactic| cil_loop_steps)) (mayClose := true)
  cil_loop_steps

/-- Snapshot stepping leaves the goals that plain simplification gives, including the
    hypotheses a store adds and clears. -/
example (memory : Memory) (slots : List LocalSlot) (boundary : Nat)
    (homes : CompleteWritableHomes memory boundary snapshotRecordBody.localKinds slots)
    (inputs outputs : List ArgumentView) (valid : ValidCall memory inputs outputs)
    (word : BitVec 64) :
    WP (Execution (fun fuel => run [snapshotRecordBody] fuel 0 0 [.scalar (.i64 word)]
      ⟨0, slots, [], 0, []⟩ [] memory)) (fun result => result.2 = [.scalar (.i64 word)]) := by
  have formed := valid.wellFormed
  have preserved := MemoryBelow.refl boundary memory
  have authority := (MemoryBelow.refl memory.nextIdentity memory).accessBelow
  have snapshots := LocalSnapshots.empty memory slots
  run_tac sameGoals (← `(tactic| cil_contract_steps (snapshots := snapshots) 2 []))
  cil_contract_steps (snapshots := snapshots) []
  exact rfl

open Lean Elab Tactic Meta in
/-- A loop walk restates a caller buffer fact at a memory the walk introduced and clears the one
    it restated, and keeps a fact at any other memory, which the restatement does not give back,
    even one the caller names `stored` as the walk names its own. -/
example (produced stored entry : Memory) (base : Reference) (x : BitVec 32)
    (producedFact : Contents produced base 4 [x]) (namedFact : Contents stored base 4 [x])
    (callerFact : Contents entry base 4 [x]) : True := by
  run_tac withMainContext do
    let count (memory : Name) : TacticM Nat := withMainContext do
      let memory ← elabTerm (mkIdent memory) none
      return (← getLCtx).foldl (init := 0) fun found declaration =>
        if declaration.type.isAppOf ``Contents &&
            (declaration.type.getAppArgs[0]? == some memory) then found + 1 else found
    let carry : LoopCarried → Ident → TacticM (Option Term) := fun _ fact => pure (some fact)
    recordWalkVariable (← elabTerm (mkIdent `produced) none).fvarId!
    for memory in [`produced, `stored, `entry] do
      loopCarryFacts (← elabTerm (mkIdent memory) none) carry
    unless (← count `produced) == 1 do
      throwError "the fact at the walk's memory was not replaced"
    unless (← count `stored) == 2 do throwError "the fact at the memory named stored was cleared"
    unless (← count `entry) == 2 do throwError "the caller's fact was cleared"
  trivial

open Lean Elab Tactic in
/-- Closes the goal with `cil_lookup_assumption` both outside a stepping driver, where it scans the
    local context, and in a step of one, where it reads the driver's equation index; either may
    find an equation the other misses, so each test runs both. -/
elab "cil_lookup_both_ways" : tactic => do
  let saved ← saveState
  evalTactic (← `(tactic| cil_lookup_assumption))
  saved.restore
  withNormalRun (withNormalNodes #[] (evalTactic (← `(tactic| cil_lookup_assumption))))

/-- The lookup it is given, under a name that reducible unfolding removes. -/
abbrev sameLookup (found : Option Nat) : Option Nat := found

-- A lookup whose left side unfolds at reducible transparency to a variable is stated by an
-- equation about that variable, although the lookup is written with a constant head.
example (found : Option Nat) (stated : found = some 3) : sameLookup found = some 3 := by
  cil_lookup_both_ways

/-- A list that reducible unfolding spells out. -/
abbrev lookupList : List Nat := [1, 2]

/-- The first entry of a list, under a name that reducible unfolding removes. -/
abbrev firstEntry (entries : List Nat) : Option Nat := entries[0]?

/-- Twice a natural number, which reducible unfolding turns into a product. -/
abbrev twice (count : Nat) : Nat := 2 * count

/-- Another name for natural numbers, which reducible unfolding removes. -/
abbrev Position := Nat

-- Both lookups find every hypothesis that unification may equate with the lookup: an
-- abbreviation of a list literal meets an equation about the literal, and arithmetic on natural
-- numbers meets its result whichever side writes the arithmetic.
example (stated : ([1, 2] : List Nat)[0]? = some 1) : lookupList[0]? = some 1 := by
  cil_lookup_both_ways
example (entries : List Nat) (stated : entries[Nat.succ 1]? = some 3) :
    entries[Nat.add 1 1]? = some 3 := by
  cil_lookup_both_ways
example (entries : List Nat) (stated : entries[2 * 1]? = some 3) : entries[2]? = some 3 := by
  cil_lookup_both_ways
example (entries : List Nat) (stated : entries[2]? = some 3) : entries[2 * 1]? = some 3 := by
  cil_lookup_both_ways
-- A local definition unfolds during unification, in a lookup and in a hypothesis alike, and so
-- does the arithmetic it names.
example (entries : List Nat) (stated : entries[1]? = some 3) :
    let position := 1; entries[position]? = some 3 := by
  intro position
  cil_lookup_both_ways
example (entries : List Nat) :
    let found := entries[1]?; found = some 3 → entries[1]? = some 3 := by
  intro found stated
  cil_lookup_both_ways
example (entries : List Nat) (stated : entries[2]? = some 3) :
    let position := 2 * 1; entries[position]? = some 3 := by
  intro position
  cil_lookup_both_ways
example (entries : List Nat) :
    let position := 2 * 1; entries[position]? = some 3 → entries[2]? = some 3 := by
  intro position stated
  cil_lookup_both_ways
-- A reducible definition unfolds on either side, and so does the arithmetic it names or a type
-- it renames.
example (entries : List Nat) (stated : entries[twice 1]? = some 3) : entries[2]? = some 3 := by
  cil_lookup_both_ways
example (entries : List Nat) (stated : entries[2]? = some 3) : entries[twice 1]? = some 3 := by
  cil_lookup_both_ways
example (entries : List Nat) (stated : entries[((2 : Position) * 1 : Position)]? = some 3) :
    entries[2]? = some 3 := by
  cil_lookup_both_ways
example (entries : List Nat) (stated : firstEntry entries = some 3) : entries[0]? = some 3 := by
  cil_lookup_both_ways
example (entries : List Nat) (stated : entries[0]? = some 3) : firstEntry entries = some 3 := by
  cil_lookup_both_ways
-- Unification matches a pair against its projections and any two values of a type with one value.
example (pair : Nat × Nat) (read : Nat × Nat → Option Nat)
    (stated : read (pair.1, pair.2) = some 1) : read pair = some 1 := by
  cil_lookup_both_ways
example (pair : Nat × Nat) (read : Nat × Nat → Option Nat) (stated : read pair = some 1) :
    read (pair.1, pair.2) = some 1 := by
  cil_lookup_both_ways
example (first second : Unit) (read : Unit → Option Nat) (stated : read first = some 1) :
    read second = some 1 := by
  cil_lookup_both_ways
example (first : Unit) (read : Unit → Option Nat) (stated : read () = some 1) :
    read first = some 1 := by
  cil_lookup_both_ways
-- A quantified lookup is closed by the quantified hypothesis that states it.
example (entries : List Nat) (stated : ∀ position : Nat, entries[position]? = some 1) :
    ∀ position : Nat, entries[position]? = some 1 := by
  cil_lookup_both_ways

open Lean Elab Tactic Meta in
-- A hypothesis whose left side holds a metavariable that is assigned after a step indexed it
-- still states the lookup at the next step.
example (entries : List Nat) : entries = entries := by
  run_tac withMainContext do
    let list ← elabTerm (mkIdent `entries) none
    let position ← mkFreshExprSyntheticOpaqueMVar (mkConst ``Nat)
    let found ← mkAppM ``Option.some #[mkNatLit 1]
    let stated ← mkEq (← mkAppM ``GetElem?.getElem? #[list, position]) found
    let wanted ← mkEq (← mkAppM ``GetElem?.getElem? #[list, mkNatLit 2]) found
    let (_, lookup) ← (← mkFreshExprMVar (← mkArrow stated wanted)).mvarId!.intro1P
    let saved ← getGoals
    setGoals [lookup]
    withNormalRun do
      withNormalNodes #[] (pure ())
      position.mvarId!.assign (mkNatLit 2)
      withNormalNodes #[] (evalTactic (← `(tactic| cil_lookup_assumption)))
    unless (← getGoals).isEmpty do throwError "the lookup was not closed"
    setGoals saved
  rfl

/-- A running sum of fifteen additions, long enough for the stepping record to be used. -/
@[cil_code] def runningSum : CIL.Method := {
  locals := [], returnsValue := true,
  code := [.ldarg 0, .ldarg 1, .add, .ldarg 1, .add, .ldarg 1, .add, .ldarg 1, .add,
    .ldarg 1, .add, .ldarg 1, .add, .ldarg 1, .add, .ldarg 1, .add, .ldarg 1, .add,
    .ldarg 1, .add, .ldarg 1, .add, .ldarg 1, .add, .ldarg 1, .add, .ldarg 1, .add,
    .ldarg 1, .add, .ret] }

open Lean Elab Tactic Meta in
/-- Run `steps` and fail when its comparisons of local contexts read more positions than one
    whole-context comparison per instruction of `runningSum`. Comparing the whole context at each
    read of the record costs no heartbeats, so only this count shows it. -/
elab "cil_reads_at_most_one_context_per_instruction " steps:tactic : tactic => do
  let size := (← withMainContext getLCtx).numIndices
  let before ← contextReads
  evalTactic steps
  let reads := (← contextReads) - before
  let limit := size * runningSum.code.length
  unless reads <= limit do
    throwError "the steps read {reads} context positions; at most {limit} were expected"

-- A step whose goal keeps the local context of the record reads none of its positions, however
-- many hypotheses are in scope; checking each read of the record against the whole context
-- read fifteen to twenty contexts per instruction.
theorem running_sum_reads (memory : Memory) (left right : CIL.W64) (first : right + 1 = right + 1)
    (second : right + 2 = right + 2) (third : right + 3 = right + 3) :
    invoke [runningSum] 32 0 [.scalar (.i64 left), .scalar (.i64 right)] memory =
      .ok (memory, [.scalar (.i64 (left + right + right + right + right + right + right + right +
        right + right + right + right + right + right + right + right))]) := by
  cil_reads_at_most_one_context_per_instruction cil_checked_steps

#print axioms running_sum_reads

theorem running_sum_contract_reads (memory : Memory) (left right : CIL.W64)
    (first : right + 1 = right + 1) (second : right + 2 = right + 2) :
    WP (Execution (fun fuel => invoke [runningSum] fuel 0
      [.scalar (.i64 left), .scalar (.i64 right)] memory))
      (fun (final, values) => final = memory ∧ values = [.scalar (.i64 (left + right + right +
        right + right + right + right + right + right + right + right + right + right + right +
        right + right))]) := by
  cil_reads_at_most_one_context_per_instruction
    (cil_contract_steps []; exact And.intro rfl rfl)

#print axioms running_sum_contract_reads

open Lean Elab Tactic Meta in
/-- A step that runs out of heartbeats leaves no record behind. The exception is a runtime
    exception, which `try` does not catch, so the cleanup must not depend on a handler. -/
example (memory : Memory) (frame : Frame) (left right : CIL.W64) :
    run recordProgram 5 0 0 [.scalar (.i64 left), .scalar (.i64 right)] frame [] memory =
      run recordProgram 3 0 2 [.scalar (.i64 left), .scalar (.i64 right)] frame
        [.scalar (.i64 right), .scalar (.i64 left)] memory := by
  run_tac do
    let saved ← saveState
    -- The limit is the cost of preparing the facts plus a little, so it is the step that runs out.
    let started ← IO.getNumHeartbeats
    evalTactic (← `(tactic| cil_checked_steps 0 []))
    let preparation := (← IO.getNumHeartbeats) - started
    saved.restore
    -- A handler restores the state, which would empty the record, so it is read as the
    -- exception passes.
    let left ← IO.mkRef false
    let exhausted ← tryCatchRuntimeEx
      (Core.withCurrHeartbeats <| withTheReader Core.Context
        (fun context => { context with maxHeartbeats := preparation + 20000 }) do
          tryFinally (do evalTactic (← `(tactic| cil_checked_steps 2 [])); pure false)
            (do left.set (← recordIsLeft)))
      (fun exception => if exception.isRuntime then pure true else throw exception)
    unless exhausted do
      throwError "the steps did not run out of heartbeats, so the test checks nothing"
    if ← left.get then throwError "a stepping record outlived the step that ran out of heartbeats"
    saved.restore
  cil_checked_steps 2 []
  all_goals rfl

open Lean Elab Tactic Meta in
/-- A driver uses the record from its thirteenth step: twelve steps run plainly and build no key,
    and the thirteenth builds one and records. -/
example : True := by
  run_tac do
    withOptions (fun options => cil.stepping.warmup.set options 12) do
      withNormalRun do
        let step : TacticM Bool := withNormalNodes #[] do return (← getNormalNodes).active
        for count in [:12] do
          if ← step then throwError "step {count + 1} used the record during the warm-up"
          unless (← getNormalNodes).key.isNone do
            throwError "step {count + 1} built a key during the warm-up"
        unless ← step do throwError "step 13 did not use the record"
        unless (← getNormalNodes).key.isSome do throwError "step 13 built no key"
  trivial

open Lean Elab Tactic Meta in
/-- No `cil_step` equation about `CIL.Safety.step` is an rfl lemma. Simp applies an rfl lemma
    without a proof term, and the kernel then reduces `step` again at every use. -/
example : True := by
  run_tac do
    let some extension ← getSimpExtension? `cil_step | throwError "cil_step is not a simp set"
    let mut examined := 0
    let mut rflEquations := #[]
    for origin in (← extension.getTheorems).lemmaNames.toList do
      let .decl name .. := origin | continue
      let aboutStep ← forallTelescope (← getConstInfo name).type fun _ conclusion =>
        pure <| conclusion.eq?.any fun (_, lhs, _) => lhs.getAppFn.isConstOf ``CIL.Safety.step
      unless aboutStep do continue
      examined := examined + 1
      if (← isRflTheorem name) || (← isBackwardRflTheorem name) then
        rflEquations := rflEquations.push name
    if examined == 0 then throwError "cil_step holds no equation about CIL.Safety.step"
    unless rflEquations.isEmpty do
      throwError "cil_step equations about CIL.Safety.step proved by rfl: {rflEquations.toList}"
  trivial

/-- A constructor whose explicit link table keys only its later call: the `System.Object`
    constructor call at pc 1 states no link and runs its runtime model. -/
def modelledConstructor : CIL.Method :=
  { locals := [], returnsValue := true, links := [(3, .direct 1)],
    code := [.ldarg 0, .call CIL.Extraction.objectConstructorMethod {}, .ldarg 1,
      .call (Tests.callee 1) {}, .ret] }
cil_instruction_equations modelledConstructor
cil_runtime_models modelledConstructor
/-- The method the linked call enters; it returns its argument. -/
def passThrough : CIL.Method := { locals := [], returnsValue := true, code := [.ldarg 0, .ret] }
cil_instruction_equations passThrough

/-- The model call consumes the receiver and the linked call returns the second argument. -/
theorem modelled_then_linked (memory : Memory) (object : Reference) (word : CIL.W64)
    (formed : formObject memory (.address object) = .ok (.object (.address object))) :
    invoke [modelledConstructor, passThrough] 10 0
      [.object (.address object), .scalar (.i64 word)] memory =
      .ok (memory, [.scalar (.i64 word)]) := by
  cil_checked_steps [formed]
#print axioms modelled_then_linked

/-- The unlinked constructor consumes its receiver and preserves the caller's frame and memory. -/
theorem contract_steps_modelled_call (program : CIL.Program)
    (caller : program[0]? = some modelledConstructor) (frame : Frame) (memory : Memory)
    (object : Reference) (args : List Value) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel 0 2 args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel 0 1 args frame [.object (.address object)] memory =
        .ok (final, returned) ∧ post final returned := by
  cil_contract_steps 1 [caller]
  exact continuation
#print axioms contract_steps_modelled_call

/-- `IntPtr.get_Size`, a call the runtime table models. -/
def nativeSizeGetter : CIL.Extraction.MethodRef :=
  { owner := .primitive .intPtr, name := name!"get_Size",
    hasThis := false, genericArity := 0, parameters := [],
    returnType := .primitive .int32 }

/-- Two calls of the modelled size getter. Only the second has a link, which enters method 1. -/
def linkedModelCalls : CIL.Method :=
  { locals := [], returnsValue := true, links := [(2, .direct 1)],
    code := [.call nativeSizeGetter {}, .pop, .call nativeSizeGetter {}, .ret] }
cil_instruction_equations linkedModelCalls
cil_runtime_models linkedModelCalls
/-- The method the linked getter call enters; it returns 4, where the model pushes 8. -/
def fourWord : CIL.Method := { locals := [], returnsValue := true, code := [.ldc_i4 4, .ret] }
cil_instruction_equations fourWord

/-- A linked site enters its callee although its method has a model, so the run returns the
    callee's 4 rather than the model's native size. -/
theorem linked_model_site (memory : Memory) :
    invoke [linkedModelCalls, fourWord] 10 0 [] memory = .ok (memory, [.scalar (.i32 4)]) := by
  cil_checked_steps []
#print axioms linked_model_site

/-- The callee of the linked getter call returns 4 and touches no memory. -/
def fourContract : MethodContract Unit CIL.W32 where
  args _ := []
  results value := [.scalar (.i32 value)]
  pre _ _ := True
  footprint _ := []
  post _ _ _ value := value = 4

/-- Contract stepping runs the unlinked call's model and crosses the linked call with its callee's
    contract, so the result is the contract's 4 rather than the model's native size. -/
theorem contract_steps_linked_model_site (program : CIL.Program) (memory : Memory)
    (caller : program[0]? = some linkedModelCalls) (holds : fourContract.Holds program 1) :
    ∃ fuel final returned,
      run program fuel 0 0 [] ⟨0, [], [], 0, []⟩ [] memory = .ok (final, returned) ∧
        returned = [.scalar (.i32 4)] := by
  cil_contract_steps [caller, holds, fourContract]
  obtain rfl := call.post
  rfl
#print axioms contract_steps_linked_model_site

-- The stepper enters the model call by its one equation, not by `step_call_eq`, whose rewrite
-- under the call's continuation the kernel rechecks at every call.
open Lean in
run_meta do
  let info ← getConstInfo ``modelled_then_linked
  let some proof := info.value? (allowOpaque := true) | throwError "no proof"
  let used := proof.getUsedConstants
  for name in [``CIL.Safety.step_call_model, ``CIL.Safety.step_call_direct] do
    unless used.contains name do throwError "modelled_then_linked does not use {name}"

/-- A return whose list spine depends on the flag. -/
def conditionalReturn (flag : Bool) : CIL.Method :=
  { returnsValue := false, locals := [], code := if flag then [.ret, .nop] else [.ret] }

/-- The same body with the return visible at the head. -/
def leadingReturn (flag : Bool) : CIL.Method :=
  { returnsValue := false, locals := [], code := .ret :: (if flag then [.nop] else []) }

/-- A program with one conditional body. -/
def returnProgram (flag : Bool) : CIL.Program := [conditionalReturn flag]

/-- The generated lookup finds the stored body. -/
@[cil_code] theorem returnProgram_method0 (flag : Bool) :
    (returnProgram flag)[0]? = some (conditionalReturn flag) := rfl
#print axioms returnProgram_method0

/-- The preferred lookup exposes the return for both values of the flag. -/
theorem returnProgram_leading (flag : Bool) :
    (returnProgram flag)[0]? = some (leadingReturn flag) := by cases flag <;> rfl
#print axioms returnProgram_leading

/-- A caller can supply the lookup that exposes the return. -/
theorem supplied_return_steps (flag : Bool) (memory : Memory) :
    invoke (returnProgram flag) 1 0 [] memory = .ok (memory, []) := by
  cil_checked_steps [returnProgram_leading flag]
#print axioms supplied_return_steps

/-- The preferred lookup can describe the indexing function before its position is supplied. -/
theorem returnProgram_lookup (flag : Bool) :
    (GetElem?.getElem? (returnProgram flag) : Nat → Option CIL.Method) =
      (fun index => match index with | 0 => some (leadingReturn flag) | _ + 1 => none) := by
  funext index
  cases index with
  | zero => cases flag <;> rfl
  | succ => rfl
#print axioms returnProgram_lookup

section
attribute [local cil_code high] returnProgram_lookup

/-- Stepping uses the partially applied lookup at method zero. -/
theorem partial_lookup_return_steps (flag : Bool) (memory : Memory) :
    invoke (returnProgram flag) 1 0 [] memory = .ok (memory, []) := by
  cil_checked_steps
#print axioms partial_lookup_return_steps
end

attribute [cil_code high] returnProgram_leading

/-- Stepping honors the higher-priority lookup with the flag still symbolic. -/
theorem conditional_return_steps (flag : Bool) (memory : Memory) :
    invoke (returnProgram flag) 1 0 [] memory = .ok (memory, []) := by
  cil_checked_steps
#print axioms conditional_return_steps

namespace MethodLookup

/-- The immediate return shared by both branches of the program. -/
def body : CIL.Method := { returnsValue := false, locals := [], code := [.ret] }

/-- Both program lengths have the same first method. -/
def prog (flag : Bool) : CIL.Program := if flag then [body] else [body, body]

/-- The first method is available before the branch is known. -/
@[cil_code] theorem prog_method0 (flag : Bool) : (prog flag)[0]? = some body := by
  cases flag <;> rfl
#print axioms prog_method0

example (flag : Bool) : (prog flag)[0]? = some body := by cil_lookup [prog]

example (flag : Bool) (memory : Memory) :
    invoke (prog flag) 1 0 [] memory = .ok (memory, []) := by cil_checked_steps [prog]

section
attribute [local cil_code] prog

example (flag : Bool) : (prog flag)[0]? = some body := by cil_lookup []

example (flag : Bool) (memory : Memory) :
    invoke (prog flag) 1 0 [] memory = .ok (memory, []) := by cil_checked_steps
end

/-- A program with no method at position zero. -/
def vacant : CIL.Program := []

/-- The lookup equation can certify an absent method. -/
@[cil_code] theorem vacant_method0 : vacant[0]? = none := rfl
#print axioms vacant_method0

example : vacant[0]? = none := by cil_lookup_equation

/-- The named result of a successful method lookup. -/
def hit : Option CIL.Method := some body

/-- A program with a named lookup result. -/
def singleton : CIL.Program := [body]

/-- The generated equation can state its result by name. -/
@[cil_code] theorem singleton_method0 : singleton[0]? = hit := rfl
#print axioms singleton_method0

example : singleton[0]? = hit := by cil_lookup_equation

end MethodLookup

end Tests.Automation
