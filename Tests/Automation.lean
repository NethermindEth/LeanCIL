import Tests.FeatureExecution
import CIL.Safety.SymbolicExecution
import CIL.SIMD.VectorLemmas

namespace Tests.Automation

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
  code := [.arg 0, .brzero 4, .arg 1, .ret, .arg 1, .ret]
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
  code := [.arg 0, .arg 1, .const32 1, .shl, .add, .const32 0, .gtu, .ret]
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
  code := [.arg 0, .arg 1, .bxor, .const32 0, .eq, .ret (some .unsigned8)]
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
  code := [.const32 0, .const32 0, .eq, .ret (some .unsigned8)]
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
  code := [.arg 0, .arg 1, .add, .arg 0, .add, .ret]
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
  code := [.arg 0, .ret], locals := [], returnsValue := true }

@[cil_code] def callPrefixMethod : CIL.Method := {
  code := [.arg 0, .call 1 1, .arg 0, .add, .ret], locals := [], returnsValue := true }

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
  { profile, returnsValue := true, locals := [], code := [.arg 0, .bnot, .arg 1, .bnot, .bor, .bnot, .ret] }

theorem word_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (wordBody profile)) (memory : CIL.Safety.Memory) (a b : BitVec 64) :
    CIL.Safety.invoke program 10 index [.scalar (.i64 a), .scalar (.i64 b)] memory =
      .ok (memory, [.scalar (.i64 (~~~(~~~a ||| ~~~b)))]) := by
  cil_checked_steps

/-- A profile-dependent body: its instructions are fetched only once the feature test is decided. -/
@[cil_code] def featureBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [], code := if profile.avx2 then [.arg 1, .ret] else [.arg 0, .ret] }

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
def leafBody (profile : CIL.FeatureProfile) : CIL.Method := { profile, returnsValue := true, locals := [], code := [
  .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, .bxor,
  .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, .bxor, .bor,
  .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, .bxor, .bor,
  .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, .bxor, .bor,
  .const32 0, .convI8, .eq, .ret (some .unsigned8)] }

open CIL.Safety in
theorem leaf_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (leafBody profile)) (memory : Memory) (left right : Reference)
    (limb : Reference → Nat → BitVec 64) (fl : form memory left = .ok left) (fr : form memory right = .ok right)
    (field : ∀ r offset rest, instruction (.fieldAt offset 8) (.reference (.address r) :: rest) memory =
      .ok (memory, .scalar (.i64 (limb r offset)) :: rest)) :
    let difference := (limb left 0 ^^^ limb right 0) ||| (limb left 8 ^^^ limb right 8) |||
      (limb left 16 ^^^ limb right 16) ||| (limb left 24 ^^^ limb right 24)
    invoke program 28 index [.reference (.address left), .reference (.address right)] memory =
      .ok (memory, [.scalar (.i32 (CIL.NarrowKind.unsigned8.extend (if difference = 0 then 1 else 0)))]) := by
  cil_checked_steps [fl, fr, field]

def boundBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [], code := [.arg 0, .arg 1, .bltu 5, .arg 0, .ret, .arg 1, .ret] }

/-- A fact decides an unsigned i64 branch, so the run falls through to pc 3. -/
theorem bound_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (boundBody profile)) (memory : CIL.Safety.Memory) (x y : CIL.W64)
    (above : ¬ x < y) :
    CIL.Safety.invoke program 8 index [.scalar (.i64 x), .scalar (.i64 y)] memory =
      .ok (memory, [.scalar (.i64 x)]) := by
  cil_checked_steps [above]

/-- A signed branch takes its fact in the interpreter's own form, so no linear-arithmetic restatement is needed. -/
theorem signed_bound_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some { boundBody profile with code := [.arg 0, .arg 1, .blt 5, .arg 0, .ret, .arg 1, .ret] })
    (memory : CIL.Safety.Memory) (x y : CIL.W64) (above : ¬ x.toInt < y.toInt) :
    CIL.Safety.invoke program 8 index [.scalar (.i64 x), .scalar (.i64 y)] memory =
      .ok (memory, [.scalar (.i64 x)]) := by
  cil_checked_steps [above]

-- The step equations alone rewrite a compare-branch; the dispatcher stays folded.
example (body : CIL.Method) (args : List CIL.Safety.Value) (frame : CIL.Safety.Frame) (m : CIL.Safety.Memory)
    (x y : CIL.W64) (above : ¬ x < y) :
    CIL.Safety.step body (.bltu 5) 2 args frame [.scalar (.i64 y), .scalar (.i64 x)] m = .ok (.next 3 [] frame m) := by
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
    ∃ stack, step body .bxor 0 args frame [.scalar (.i64 right), .scalar (.i64 left)] memory =
      .ok (.next 1 stack frame memory) ∧ stack = [.scalar (.i64 (left ^^^ right))] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [unrelated]
  · rfl

open CIL.Safety in
theorem bitcast_fact_stack (body : CIL.Method) (args : List Value) (frame : Frame)
    (memory : Memory) (bytes : List (BitVec 8)) (value : BitVec 256)
    (casted : bitcastValue (.aggregate 32) .vector256 (.aggregate bytes) = .ok (.v256 value)) :
    ∃ stack, step body (.memory (.bitcastValue (.aggregate 32) .vector256)) 0 args frame
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
  code := [.intrinsic (.avx2 .permute4x64) 2, .memory .store256, .ret]
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
theorem store_from_instruction_fact (body : CIL.Method) (args : List Value) (frame : Frame)
    (bits : BitVec 256) (destination : Reference) (memory final : Memory)
    (stored : memoryInstruction .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    step body (.memory .store256) 2 args frame
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
theorem store_from_static_fact (body : CIL.Method) (args : List Value) (frame : Frame)
    (bits : BitVec 256) (destination : Reference) (memory final : Memory)
    (stored : staticInstruction body 2 .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    step body (.memory .store256) 2 args frame
      [.scalar (.v256 bits), .reference (.address destination)] memory =
      .ok (.next 3 [] frame final) := by
  cil_checked_step [stored]

/--
info: 'Tests.Automation.store_from_static_fact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms store_from_static_fact

/-- Two vector stores; reached through a lookup hypothesis, so facts can name the body. -/
def twoStoresMethod : CIL.Method := {
  code := [.memory .store256, .memory .store256, .ret], locals := [], returnsValue := false }

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
example (body : CIL.Method) (args : List Value) (frame : Frame) (bits : BitVec 256)
    (destination : Reference) (memory final : Memory)
    (stored : memoryInstruction .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    step body (.memory .store256) 2 args frame
      [.scalar (.v256 bits), .reference (.address destination)] memory =
      .ok (.next 3 [] frame final) := by
  cil_checked_step [staticInstruction, stored]

open CIL.Safety in
example (body : CIL.Method) (args : List Value) (frame : Frame) (bits : BitVec 256)
    (destination : Reference) (memory final : Memory)
    (stored : memoryInstruction .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    step body (.memory .store256) 2 args frame
      [.scalar (.v256 bits), .reference (.address destination)] memory =
      .ok (.next 3 [] frame final) := by
  cil_checked_step [(stored)]

open CIL.Safety in
example (body : CIL.Method) (args : List Value) (frame : Frame) (bits : BitVec 256)
    (destination : Reference) (memory final : Memory)
    (stored : staticInstruction body 2 .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    step body (.memory .store256) 2 args frame
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
  { profile, returnsValue := true, locals := [], code := [.feature .avx2, .ret] }

theorem feature_step_from_fact (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (wide : profile.avx2 = true) (found : program[index]? = some (featureTestBody profile))
    (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke program 3 index [] memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [wide]

theorem feature_step_free_body (program : CIL.Program) (index : Nat) (body : CIL.Method)
    (wide : body.profile.avx2 = false) (code : body.code = [.feature .avx2, .ret])
    (returns : body.returnsValue = true) (found : program[index]? = some body)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) :
    CIL.Safety.run program 3 index 0 [] frame [] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i32 0)]) := by
  cil_checked_steps [wide, code, returns]

-- A literal profile decides the test with no fact.
theorem feature_step_literal_profile (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke [{ permuteStoreMethod with code := [.feature .avx2, .ret], returnsValue := true }] 3 0 []
      memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps

-- Each memory step rewrites by its own equation; no fact names `staticInstruction` or `memoryInstruction`.
open CIL.Safety in
theorem asRef_fact_stack (body : CIL.Method) (args : List Value) (frame : Frame) (memory : Memory)
    (reference : Reference) (formed : form memory reference = .ok reference) :
    ∃ stack, step body (.memory .asRef) 0 args frame [.reference (.address reference)] memory =
      .ok (.next 1 stack frame memory) ∧ stack = [.reference (.address reference)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [formed]
  · rfl

open CIL.Safety in
theorem load128_fact_stack (body : CIL.Method) (args : List Value) (frame : Frame) (memory : Memory)
    (source : ManagedReference) (value : BitVec 128)
    (loaded : loadValue memory source 16 = .ok (.v128 value)) :
    ∃ stack, step body (.memory .load128) 0 args frame [.reference source] memory =
      .ok (.next 1 stack frame memory) ∧ stack = [.scalar (.v128 value)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [loaded]
  · rfl

open CIL.Safety in
theorem add_fact_stack (body : CIL.Method) (args : List Value) (frame : Frame) (memory : Memory)
    (base result : Reference) (offset : CIL.W32)
    (moved : add memory base 8 (BitVec.ofInt 64 offset.toInt) = .ok result) :
    ∃ stack, step body (.memory (.add 8 true)) 0 args frame
      [.scalar (.i32 offset), .reference (.address base)] memory =
      .ok (.next 1 stack frame memory) ∧ stack = [.reference (.address result)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [moved]
  · rfl

-- A symbolic managed reference stays `referenceAt reference`, so the caller's fact about it applies.
open CIL.Safety in
theorem add_symbolic_reference (body : CIL.Method) (args : List Value) (frame : Frame) (memory : Memory)
    (reference : ManagedReference) (base result : Reference) (offset : CIL.W32)
    (addressed : referenceAt reference = .ok base)
    (moved : add memory base 8 (BitVec.ofInt 64 offset.toInt) = .ok result) :
    ∃ stack, step body (.memory (.add 8 true)) 0 args frame
      [.scalar (.i32 offset), .reference reference] memory =
      .ok (.next 1 stack frame memory) ∧ stack = [.reference (.address result)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [addressed, moved]
  · rfl

-- An unknown scalar keeps its guard: the equation exposes it rather than assuming it away.
open CIL.Safety in
example (body : CIL.Method) (args : List Value) (frame : Frame) (memory : Memory) (value : CIL.Value) :
    step body (.memory (.bitcastValue (.aggregate 32) .vector256)) 0 args frame [.scalar value] memory =
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
    (wide : body.profile.evaluate .avx2 = false) (code : body.code = [.feature .avx2, .ret])
    (returns : body.returnsValue = true) (found : program[index]? = some body)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) :
    CIL.Safety.run program 3 index 0 [] frame [] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i32 0)]) := by
  cil_checked_steps [wide, code, returns]

-- A supplied proof term, not just a local name, is normalized to the profile field.
theorem feature_step_evaluate_term (body : CIL.Method) (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory)
    (wide : body.profile.evaluate .avx2 = true) :
    CIL.Safety.step body (.feature .avx2) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [(show body.profile.evaluate .avx2 = true from wide)]

theorem feature_steps_evaluate_term (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (wide : profile.evaluate .avx2 = true) (found : program[index]? = some (featureTestBody profile))
    (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke program 3 index [] memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [(show profile.evaluate .avx2 = true from wide)]

-- A fact over every feature is instantiated at each constructor, so it still decides the field test.
theorem feature_step_evaluate_forall (body : CIL.Method) (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory)
    (all : ∀ f, body.profile.evaluate f = true) :
    CIL.Safety.step body (.feature .avx2) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [all]

theorem feature_steps_evaluate_forall (program : CIL.Program) (index : Nat) (body : CIL.Method)
    (all : ∀ f, body.profile.evaluate f = false) (code : body.code = [.feature .avx2, .ret])
    (returns : body.returnsValue = true) (found : program[index]? = some body)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) :
    CIL.Safety.run program 3 index 0 [] frame [] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i32 0)]) := by
  cil_checked_steps [all, code, returns]

/-- A fact about a symbolic feature rewrites the pushed test by hand: `cil_step` keeps
    `body.profile.evaluate f` folded instead of splitting on `f`. -/
theorem feature_step_symbolic_fact (body : CIL.Method) (frame : CIL.Safety.Frame)
    (memory : CIL.Safety.Memory) (feature : CIL.Feature)
    (enabled : body.profile.evaluate feature = true) :
    CIL.Safety.step body (.feature feature) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  simp only [cil_step, enabled, ite_true]
  rfl

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
    (memory : CIL.Safety.Memory) (feature : CIL.Feature)
    (disabled : body.profile.evaluate feature = false) :
    CIL.Safety.step body (.feature feature) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 0)] frame memory) := by
  expect_facts_already_normal [disabled]
  cil_checked_step [disabled]

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
    (profile : body.profile = wideProfile) :
    CIL.Safety.step body (.feature .avx2) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [profile, wideProfile_avx2]

-- A fact on a method's profile projection lands where `cil_step` reduces the projection.
theorem feature_step_projection_fact (profile : CIL.FeatureProfile) (frame : CIL.Safety.Frame)
    (memory : CIL.Safety.Memory) (wide : (featureTestBody profile).profile.evaluate .avx2 = true) :
    CIL.Safety.step (featureTestBody profile) (.feature .avx2) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [wide]

theorem feature_steps_projection_fact (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (wide : (featureTestBody profile).profile.evaluate .avx2 = true)
    (found : program[index]? = some (featureTestBody profile)) (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke program 3 index [] memory = .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [wide]

theorem feature_step_projection_field (profile : CIL.FeatureProfile) (frame : CIL.Safety.Frame)
    (memory : CIL.Safety.Memory) (wide : (featureTestBody profile).profile.avx2 = true) :
    CIL.Safety.step (featureTestBody profile) (.feature .avx2) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [wide]

-- Quantified feature facts given as proof terms or global theorems are instantiated like local ones.
theorem feature_step_forall_term (body : CIL.Method) (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory)
    (all : ∀ f, body.profile.evaluate f = true) :
    CIL.Safety.step body (.feature .avx2) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 1)] frame memory) := by
  cil_checked_step [(show ∀ f, body.profile.evaluate f = true from all)]

def bareProfile : CIL.FeatureProfile := {}

theorem bareProfile_none : ∀ f, bareProfile.evaluate f = false := by intro f; cases f <;> rfl

attribute [irreducible] bareProfile

theorem feature_step_forall_global (body : CIL.Method) (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory)
    (profile : body.profile = bareProfile) :
    CIL.Safety.step body (.feature .avx2) 0 [] frame [] memory =
      .ok (.next 1 [.scalar (.i32 0)] frame memory) := by
  cil_checked_step [profile, bareProfile_none]

-- Pointer arithmetic in the run loop steps without a `referenceAt` fact.
@[cil_code] def addBody : CIL.Method :=
  { returnsValue := true, locals := [], code := [.arg 0, .const32 8, .memory (.add 8 true), .pop, .const32 1, .ret] }

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
    step body (.memory .asRef) 0 [] frame [.reference (.address reference)] memory =
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
  { profile, returnsValue := true, locals := [], code := [.setLocal 0, .local 0, .ret] }

open CIL.Safety in
theorem step_facts_first (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (slotBody profile)) (args : List Value) (frame stored : Frame)
    (memory written : Memory) (value : CIL.W32)
    (store : step (slotBody profile) (.setLocal 0) 0 args frame [.scalar (.i32 value)] memory =
      .ok (.next 1 [] stored written))
    (load : ∀ stack, step (slotBody profile) (.local 0) 1 args stored stack written =
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
    (store : ∀ value : CIL.W32, step (slotBody profile) (.setLocal 0) 0 args frame [.scalar (.i32 value)] memory =
      .ok (.next 1 [] stored written))
    (load : ∀ stack, step (slotBody profile) (.local 0) 1 args stored stack written =
      .ok (.next 2 (.scalar (.i32 value) :: stack) stored written)) :
    run program 3 index 0 args frame [.scalar (.i32 value)] memory =
      .ok (leaveFrame stored written, [.scalar (.i32 value)]) := by
  cil_checked_steps [store value, (load)]

/-- info: 'Tests.Automation.applied_step_facts_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms applied_step_facts_first

/-- An extracted program's lookup unfolds the body to its literal, so a fact on the named body must still match. -/
@[cil_code] def slotMethod : CIL.Method :=
  { returnsValue := true, locals := [], code := [.setLocal 0, .local 0, .ret] }
@[cil_code] def slotProgram : CIL.Program := [slotMethod]

open CIL.Safety in
theorem named_body_step_facts (frame stored : Frame) (memory written : Memory) (value : CIL.W32)
    (store : step slotMethod (.setLocal 0) 0 [] frame [.scalar (.i32 value)] memory =
      .ok (.next 1 [] stored written))
    (load : ∀ stack, step slotMethod (.local 0) 1 [] stored stack written =
      .ok (.next 2 (.scalar (.i32 value) :: stack) stored written)) :
    run slotProgram 3 0 0 [] frame [.scalar (.i32 value)] memory =
      .ok (leaveFrame stored written, [.scalar (.i32 value)]) := by
  cil_checked_steps [store, load]

/-- info: 'Tests.Automation.named_body_step_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms named_body_step_facts

-- A fact quantified over the body matches the literal directly.
open CIL.Safety in
theorem quantified_body_step_facts (frame stored : Frame) (memory written : Memory) (value : CIL.W32)
    (store : ∀ body pc args, step body (.setLocal 0) pc args frame [.scalar (.i32 value)] memory =
      .ok (.next (pc + 1) [] stored written))
    (load : ∀ body pc args stack, step body (.local 0) pc args stored stack written =
      .ok (.next (pc + 1) (.scalar (.i32 value) :: stack) stored written)) :
    run slotProgram 3 0 0 [] frame [.scalar (.i32 value)] memory =
      .ok (leaveFrame stored written, [.scalar (.i32 value)]) := by
  cil_checked_steps [store, load]

/-- info: 'Tests.Automation.quantified_body_step_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms quantified_body_step_facts

open CIL.Safety in
/-- A supplied step fact is found after an earlier tactic `have` wraps the target in metadata;
    the `setLocal` equation alone cannot read the abstract frame's slot. -/
theorem step_fact_after_have (frame stored : Frame) (memory written : Memory) (value : CIL.W32)
    (store : step slotMethod (.setLocal 0) 0 [] frame [.scalar (.i32 value)] memory =
      .ok (.next 1 [] stored written)) :
    step slotMethod (.setLocal 0) 0 [] frame [.scalar (.i32 value)] memory =
      .ok (.next 1 [] stored written) := by
  have unchanged : value = value := rfl
  cil_checked_step [store]

/-- info: 'Tests.Automation.step_fact_after_have' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_fact_after_have

@[cil_code] def nonzeroMethod : CIL.Method := {
  code := [.arg 0, .brnonzero 4, .arg 1, .ret, .arg 0, .ret]
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
  code := [.const32 5, .brnonzero 4, .arg 0, .ret, .arg 1, .ret]
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
  { profile, returnsValue := true, locals := [],
    code := [if profile.avx2 then .arg 1 else .arg 0, .fieldAt 0 8, .ret] }

-- The lookup decides the feature test, so the fetched op is a constructor with a step equation.
-- A term-mode `by`, as the contract and loop tactics call it, must still assign the op.
example (profile : CIL.FeatureProfile) (scalar : profile.avx2 = false) :
    ∃ op, (featureOpBody profile).code[0]? = some op ∧ op = .arg 0 :=
  ⟨_, by cil_lookup [scalar], by with_reducible rfl⟩

open CIL.Safety in
theorem feature_op_checked (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (scalar : profile.avx2 = false) (found : program[index]? = some (featureOpBody profile))
    (frame : Frame) (memory : Memory) (left right : Reference) (limb : BitVec 64)
    (formed : form memory left = .ok left)
    (field : ∀ rest, instruction (.fieldAt 0 8) (.reference (.address left) :: rest) memory =
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
  code := [.arg 0, .arg 1, .checkedArithmetic .add false, .ret]
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
theorem bitcast_dispatch_keeps_value (body : CIL.Method) (args : List Value) (frame : Frame)
    (memory : Memory) (byte : BitVec 8) (value : BitVec 256)
    (casted : memoryInstruction (.bitcastValue (.aggregate 32) .vector256)
      [.scalar (.aggregate (List.replicate 32 byte))] memory =
        .ok (memory, [.scalar (.v256 value)])) :
    ∃ stack, step body (.memory (.bitcastValue (.aggregate 32) .vector256)) 0 args frame
      [.scalar (.aggregate (List.replicate 32 byte))] memory =
        .ok (.next 1 stack frame memory) ∧ stack = [.scalar (.v256 value)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [casted]
  · rfl

#print axioms bitcast_dispatch_keeps_value

open CIL.Safety in
/-- The same abstract result is retained for a fact at the static dispatch boundary. -/
theorem bitcast_static_keeps_value (body : CIL.Method) (args : List Value) (frame : Frame)
    (memory : Memory) (byte : BitVec 8) (value : BitVec 256)
    (casted : staticInstruction body 0 (.bitcastValue (.aggregate 32) .vector256)
      [.scalar (.aggregate (List.replicate 32 byte))] memory =
        .ok (memory, [.scalar (.v256 value)])) :
    ∃ stack, step body (.memory (.bitcastValue (.aggregate 32) .vector256)) 0 args frame
      [.scalar (.aggregate (List.replicate 32 byte))] memory =
        .ok (.next 1 stack frame memory) ∧ stack = [.scalar (.v256 value)] := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cil_checked_step [casted]
  · rfl

#print axioms bitcast_static_keeps_value

open CIL.Safety in
/-- A conjunction-wrapped dispatch fact remains usable through the generic fallback. -/
theorem store_from_wrapped_fact (body : CIL.Method) (args : List Value) (frame : Frame)
    (bits : BitVec 256) (destination : Reference) (memory final : Memory)
    (stored : True ∧ memoryInstruction .store256
      [.scalar (.v256 bits), .reference (.address destination)] memory = .ok (final, [])) :
    step body (.memory .store256) 2 args frame
      [.scalar (.v256 bits), .reference (.address destination)] memory =
      .ok (.next 3 [] frame final) := by
  cil_checked_step_normalized [stored]

#print axioms store_from_wrapped_fact

/-- Compare two words and reinterpret the result as a Boolean. -/
@[cil_code] def comparedBoolean : CIL.Method := {
  code := [.arg 0, .arg 1, .eq, .memory .bitcastByteBool, .ret]
  locals := [], returnsValue := true }

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
    step body (.memory .bitcastByteBool) 0 [] frame [.scalar (.i32 bits)] memory =
      .ok (.next 1 [.scalar (.i32 bits)] frame memory) := by
  fail_if_success cil_checked_step []
  cil_checked_step [canonical]

#print axioms unconstrained_boolean_cast

open CIL.Safety in
/-- A canonical bit stays canonical through the byte and int32 widths a field load gives it,
    so its bound steps the Boolean cast of the widened value. -/
theorem widened_boolean_cast (body : CIL.Method) (frame : Frame) (field : CIL.W64)
    (memory : Memory) (canonical : field.toNat ≤ 1) :
    step body (.memory .bitcastByteBool) 0 [] frame
        [.scalar (.i32 ((field.setWidth 8).setWidth 32))] memory =
      .ok (.next 1 [.scalar (.i32 ((field.setWidth 8).setWidth 32))] frame memory) := by
  fail_if_success cil_checked_step []
  cil_checked_step [canonical]

#print axioms widened_boolean_cast

open CIL.Safety in
/-- A value known only to be numeric loads as an argument: the fact meets the checked value
    test in the unfolded form stepping leaves it in. -/
theorem opaque_numeric_argument (body : CIL.Method) (frame : Frame) (argument : CIL.Value)
    (memory : Memory) (numeric : numericValue argument = true) :
    step body (.arg 0) 0 [.scalar argument] frame [] memory =
      .ok (.next 1 [.scalar argument] frame memory) := by
  fail_if_success cil_checked_step []
  cil_checked_step [numeric]

#print axioms opaque_numeric_argument

open CIL.Safety in
/-- The same fact passes an opaque numeric value to a call. -/
theorem opaque_numeric_call (body : CIL.Method) (frame : Frame) (argument : CIL.Value)
    (memory : Memory) (numeric : numericValue argument = true)
    (known : argument.hasUnspecified = false) :
    step body (.call 1 1) 0 [] frame [.scalar argument] memory =
      .ok (.call 1 [.scalar argument] [] memory) := by
  fail_if_success cil_checked_step [known]
  cil_checked_step [numeric, known]

#print axioms opaque_numeric_call

open CIL.Safety in
/-- A read introduced by `have name := term` states its type through an assigned
    metavariable; its load is derived like that of a hypothesis with a written type. -/
theorem inferred_read_load (memory : Memory) (limb : Reference) (word : CIL.W64)
    (loaded : read memory limb 8 1 = .ok (numberBytes word.toNat 8))
    (body : CIL.Method) (frame : Frame) :
    step body .load64 0 [] frame [.reference (.address limb)] memory =
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
/-- Fails unless no record is active or kept. -/
def recordIsEmpty : TacticM Unit := do
  let record ← getNormalNodes
  unless !record.active && record.nodes.isEmpty && record.equations.isNone &&
      record.contexts.isEmpty && record.others.isEmpty do
    throwError "a stepping record outlived its run"

/-- Adds two arguments. -/
@[cil_code] def recordBody : CIL.Method := {
  code := [.arg 0, .arg 1, .add, .ret], locals := [], returnsValue := true }

/-- The program of `recordBody`. -/
@[cil_code] def recordProgram : CIL.Program := [recordBody]

/-- Adds the arguments in the other order, so its goals differ from those of `recordBody`. -/
@[cil_code] def otherBody : CIL.Method := {
  code := [.arg 1, .arg 0, .add, .ret], locals := [], returnsValue := true }

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
    is not used for the other or after a hypothesis is added. -/
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
      -- A hypothesis outside the facts, rewritten in place, keeps its name and identity but not
      -- what it states, and a simplification may use it.
      let goal ← getMainGoal
      let declaration ← withMainContext (getLocalDeclFromUserName `one)
      let sum ← mkAppM ``HAdd.hAdd #[mkNatLit 1, mkNatLit 0]
      replaceMainGoal [← goal.replaceLocalDeclDefEq declaration.fvarId
        (← mkEq (mkNatLit 1) sum)]
      if ← recorded #[holeSecond] then throwError "a record was used after a hypothesis changed"
      evalTactic (← `(tactic| have extra : True := trivial))
      if ← recorded #[holeSecond] then throwError "a record was used after a hypothesis was added"
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

end Tests.Automation
