import Lean
-- Only the tactic module: its checked-step fallback unfolds `CIL.step`, so it must bring the shared copies.
import CIL.Safety.SymbolicExecution

namespace Tests.InterpreterEquations
open Lean

-- A consumer macro naming a reserved equation lemma, which a quotation cannot generate itself.
macro "unfold_dispatch" : tactic => `(tactic| rw [CIL.step.eq_def])

example (returns : Bool) (pc : Nat) (args stack : List CIL.Value) (frame : Nat) (memory : CIL.Memory) :
    CIL.step .nop returns pc args frame stack memory = CIL.step .nop returns pc args frame stack memory := by
  unfold_dispatch

-- Each lemma must come from its shared module; one generated here would mean importers rebuild it.
run_cmd do
  let env ← getEnv
  for (name, owner) in [
      (`CIL.step.eq_def, `CIL.Safety.Execution), (`CIL.Safety.step.eq_def, `CIL.Safety.Execution),
      (`CIL.step.eq_1, `CIL.StepEquations),
      (`CIL.Safety.step.eq_1, `CIL.Safety.Equations), (`CIL.Safety.instruction.eq_1, `CIL.Safety.Equations),
      (`CIL.Safety.instruction.eq_def, `CIL.Safety.Equations),
      (`CIL.Safety.memoryInstruction.eq_1, `CIL.Safety.Equations),
      (`CIL.Safety.memoryInstruction.eq_def, `CIL.Safety.Equations),
      (`CIL.Safety.staticInstruction.eq_1, `CIL.Safety.Equations),
      (`CIL.Safety.staticInstruction.eq_def, `CIL.Safety.Equations),
      (`CIL.Safety.pureArity.eq_1, `CIL.Safety.Equations), (`CIL.Safety.pureArity.eq_def, `CIL.Safety.Equations),
      (`CIL.Safety.scalars.eq_1, `CIL.Safety.Equations), (`CIL.Safety.scalars.eq_def, `CIL.Safety.Equations),
      (`CIL.binary.eq_1, `CIL.Safety.Equations), (`CIL.binary.eq_def, `CIL.Safety.Equations),
      (`CIL.unary.eq_1, `CIL.Safety.Equations), (`CIL.unary.eq_def, `CIL.Safety.Equations),
      (`CIL.FeatureProfile.evaluate.eq_1, `CIL.Features)] do
    let some index := env.getModuleIdxFor? name | throwError "{name} is not stored by an import"
    let stored := env.header.moduleNames[index.toNat]!
    unless stored == owner do throwError "{name} is stored by {stored}, expected {owner}"

-- Every importer that splits `step` rebuilds each match splitter under the default heartbeat
-- budget; one match of 87 alternatives exceeded it, while 79 fit.
run_cmd do
  let mut widest := 0
  for index in [1:200] do
    let name := `CIL.Safety.step ++ Name.mkSimple s!"match_{index}"
    if let some info ← Meta.getMatcherInfo? name then widest := max widest info.numAlts
  unless widest ≤ 79 do
    throwError "a match in CIL.Safety.step has {widest} alternatives; importers cannot split it"

section FaultingArithmetic
open CIL CIL.Safety

/-- The flags each division and overflow-checked constructor stands for. -/
example : Instruction.divideKind? .rem_un = some (false, true) := rfl
example : Instruction.divideKind? .div = some (true, false) := rfl
example : Instruction.divideKind? .add_ovf = none := rfl
example : Instruction.checkedKind? .sub_ovf_un = some (.sub, false) := rfl
example : Instruction.checkedKind? .mul_ovf = some (.mul, true) := rfl
example : Instruction.checkedKind? .rem = none := rfl

private def body : Method := { returnsValue := true, locals := [], code := [] }
private def frame : Frame := { activation := 0, locals := [], owned := [] }

/-- One checked step of `op` over `x` then `y` (`y` on top). -/
private def binaryStep (op : Instruction) (x y : W32) : Except ExecutionFault FrameAction :=
  step body op 0 [] frame [.scalar (.i32 y), .scalar (.i32 x)] Memory.empty

/-- The checked step that pushes `result` and resumes at the next instruction. -/
private def pushes (result : W32) : Except ExecutionFault FrameAction :=
  .ok (.next 1 [.scalar (.i32 result)] frame Memory.empty)

private def overflows : Except ExecutionFault FrameAction := .error (.arithmetic .overflow)

-- Each operand pair separates the constructor from its signedness and quotient/remainder twins.
example : binaryStep .div 0xFFFFFFF9 2 = pushes 0xFFFFFFFD := rfl
example : binaryStep .div_un 0xFFFFFFF9 2 = pushes 0x7FFFFFFC := rfl
example : binaryStep .rem 0xFFFFFFF9 2 = pushes 0xFFFFFFFF := rfl
example : binaryStep .rem_un 0xFFFFFFF9 2 = pushes 1 := rfl
example : binaryStep .add_ovf 0x7FFFFFFF 1 = overflows := rfl
example : binaryStep .add_ovf_un 0x7FFFFFFF 1 = pushes 0x80000000 := rfl
example : binaryStep .sub_ovf 0 1 = pushes 0xFFFFFFFF := rfl
example : binaryStep .sub_ovf_un 0 1 = overflows := rfl
example : binaryStep .mul_ovf 0xFFFFFFFF 2 = pushes 0xFFFFFFFE := rfl
example : binaryStep .mul_ovf_un 0xFFFFFFFF 2 = overflows := rfl

-- An unsigned checked op zero-extends a native-int `i32`; sign extension would overflow here.
example : step body (.nativeBinary .mul_ovf_un) 0 [] frame
    [.scalar (.i32 0x80000000), .scalar (.i64 2)] Memory.empty =
      .ok (.next 1 [.scalar (.i64 0x100000000)] frame Memory.empty) := rfl

/-- One checked step of `op` over a single operand `value`. -/
private def unaryStep (op : Instruction) (value : CIL.Value) :
    Except ExecutionFault FrameAction :=
  step body op 0 [] frame [.scalar value] Memory.empty

/-- The checked step that pushes `result` from a one-operand instruction. -/
private def pushesValue (result : CIL.Value) : Except ExecutionFault FrameAction :=
  .ok (.next 1 [.scalar result] frame Memory.empty)

-- `conv.ovf.i.un` converts to 64 signed bits from an unsigned operand: 2^63 overflows, which
-- a signed operand or an unsigned target would accept, and `i32` operands zero-extend.
example : unaryStep (.conv_ovf_un .i) (.i64 0x8000000000000000) = overflows := rfl
example : unaryStep (.conv_ovf .i) (.i64 0x8000000000000000) =
    pushesValue (.i64 0x8000000000000000) := rfl
example : unaryStep (.conv_ovf_un .u) (.i64 0x8000000000000000) =
    pushesValue (.i64 0x8000000000000000) := rfl
example : unaryStep (.conv_ovf_un .i) (.i64 0x7FFFFFFFFFFFFFFF) =
    pushesValue (.i64 0x7FFFFFFFFFFFFFFF) := rfl
example : unaryStep (.conv_ovf_un .i) (.i32 0xFFFFFFFF) = pushesValue (.i64 0xFFFFFFFF) := rfl
example : unaryStep (.conv_ovf .i4) (.i64 0x80000000) = overflows := rfl
example : unaryStep (.conv_ovf .u2) (.i32 0xFFFF) = pushesValue (.i32 0xFFFF) := rfl

-- A native target's width and signedness reduce, so a fact about `convertInteger 64 true true`
-- drives the bridge for `.conv_ovf_un .i`.
example (input value : CIL.Value) (rest : List CIL.Safety.Value)
    (calculated : CIL.convertInteger 64 true true input = .ok value)
    (known : input.hasUnspecified = false)
    (checked : checkedValue Memory.empty (.scalar value) = .ok (.scalar value)) :
    step body (.conv_ovf_un .i) 0 [] frame (.scalar input :: rest) Memory.empty =
      .ok (.next 1 (.scalar value :: rest) frame Memory.empty) :=
  step_conv_ovf_un_result (target := .i) calculated known checked body 0 [] frame rest

-- `conv.i` sign-extends like `conv.i8` on the admitted 64-bit native width; `conv.u` does not.
example (value : CIL.Value) : CIL.unary .conv_i value = CIL.unary .conv_i8 value := by
  cases value <;> rfl
example : unaryStep .conv_i (.i32 0xFFFFFFFF) = pushesValue (.i64 0xFFFFFFFFFFFFFFFF) := rfl
example : unaryStep .conv_u (.i32 0xFFFFFFFF) = pushesValue (.i64 0xFFFFFFFF) := rfl

end FaultingArithmetic

-- An unsigned same-width checked step keeps its helper folded, the form the checked bridge reads.
/--
info: CIL.Safety.step_add_ovf_un_i32_i32_eq (body✝ : CIL.Method) (pc✝ : Nat) (args✝ : List CIL.Safety.Value)
  (frame✝ : CIL.Safety.Frame) (memory✝ : CIL.Safety.Memory) (rest : List CIL.Safety.Value) (b a : CIL.W32) :
  CIL.Safety.step body✝ CIL.Instruction.add_ovf_un pc✝ args✝ frame✝
      (CIL.Safety.Value.scalar (CIL.Value.i32 b) :: CIL.Safety.Value.scalar (CIL.Value.i32 a) :: rest) memory✝ =
    match
      Except.mapError CIL.Safety.ExecutionFault.arithmetic
        (CIL.checkedValues CIL.CheckedBinaryKind.add false (CIL.Value.i32 a) (CIL.Value.i32 b)) with
    | Except.error err => Except.error err
    | Except.ok v =>
      match CIL.Safety.checkedValue memory✝ (CIL.Safety.Value.scalar v) with
      | Except.error err => Except.error err
      | Except.ok v => Except.ok (CIL.Safety.FrameAction.next (pc✝ + 1) (v :: rest) frame✝ memory✝)
-/
#guard_msgs in #check CIL.Safety.step_add_ovf_un_i32_i32_eq

end Tests.InterpreterEquations
