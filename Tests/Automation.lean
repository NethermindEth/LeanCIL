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
    CIL.Safety.ExecutionResult (CIL.Safety.Memory × List CIL.Safety.Value)) = _
  simp only [scalarDifference, CIL.NarrowKind.extend]
  split <;> rfl

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
end Tests.Automation
