import CIL.Safety.SymbolicExecution

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
  change (Except.ok (CIL.Safety.leaveFrame frame memory,
    [.scalar (.i32 (CIL.NarrowKind.extend .unsigned8 (if left ^^^ right = 0 then 1 else 0)))]) :
    Except CIL.Safety.LocatedFault (CIL.Safety.Memory × List CIL.Safety.Value)) = _
  by_cases same : left = right <;>
    simp [scalarDifference, CIL.NarrowKind.extend, CIL.Safety.leaveFrame, same]

#print axioms checked_narrow_return

theorem checked_plain_return (memory : CIL.Safety.Memory) (frame : CIL.Safety.Frame)
    (value : CIL.W32) :
    CIL.Safety.run [branchMethod] 1 0 3
      [] frame [.scalar (.i32 value)] memory =
      .ok (CIL.Safety.leaveFrame frame memory, [.scalar (.i32 value)]) := by
  cil_checked_steps

#print axioms checked_plain_return

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
  cil_checked_steps [checkedValue, formValue, checkedAt, fl, fr, field]

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

/-- info: 'Tests.Automation.leaf_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms leaf_checked
/-- info: 'Tests.Automation.bound_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bound_checked
end Tests.Automation
