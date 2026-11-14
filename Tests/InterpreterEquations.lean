import Lean
-- Only the tactic module: its checked-step fallback unfolds `CIL.step`, so it must bring the shared copies.
import CIL.Safety.SymbolicExecution

namespace Tests.InterpreterEquations
open Lean

-- A consumer macro naming a reserved equation lemma, which a quotation cannot generate itself.
macro "unfold_dispatch" : tactic => `(tactic| rw [CIL.step.eq_def])

example (returns : Bool) (pc : Nat) (args stack : List CIL.Value) (memory : CIL.Memory) :
    CIL.step .nop returns pc args stack memory = CIL.step .nop returns pc args stack memory := by
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

-- A `step` match wider than 79 alternatives exceeds the default heartbeat budget of an importer
-- that splits it. Finding no matcher means the names changed, and the bound would hold vacuously.
run_cmd do
  let mut widest := 0
  let mut found := 0
  for index in [1:200] do
    let name := `CIL.Safety.step ++ Name.mkSimple s!"match_{index}"
    if let some info ← Meta.getMatcherInfo? name then
      widest := max widest info.numAlts
      found := found + 1
  if found == 0 then throwError "no CIL.Safety.step.match_N matcher found below 200"
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

section Guards
variable (left right : CIL.Value) (rest : List CIL.Safety.Value)
  (leftKnown : left.hasUnspecified = false) (rightKnown : right.hasUnspecified = false)
include leftKnown rightKnown

-- Each faulting constructor's guard lemma decides its operand guard; without it `cil_guard`
-- leaves `observerCount` folded and makes no progress.
example : unspecifiedOperands (observerCount .div) (.scalar right :: .scalar left :: rest) =
    false := by
  simp only [cil_guard, leftKnown, rightKnown, Bool.or_false]
example : unspecifiedOperands (observerCount .div_un) (.scalar right :: .scalar left :: rest) =
    false := by
  simp only [cil_guard, leftKnown, rightKnown, Bool.or_false]
example : unspecifiedOperands (observerCount .rem) (.scalar right :: .scalar left :: rest) =
    false := by
  simp only [cil_guard, leftKnown, rightKnown, Bool.or_false]
example : unspecifiedOperands (observerCount .rem_un) (.scalar right :: .scalar left :: rest) =
    false := by
  simp only [cil_guard, leftKnown, rightKnown, Bool.or_false]
example : unspecifiedOperands (observerCount .add_ovf) (.scalar right :: .scalar left :: rest) =
    false := by
  simp only [cil_guard, leftKnown, rightKnown, Bool.or_false]
example : unspecifiedOperands (observerCount .add_ovf_un) (.scalar right :: .scalar left :: rest) =
    false := by
  simp only [cil_guard, leftKnown, rightKnown, Bool.or_false]
example : unspecifiedOperands (observerCount .sub_ovf) (.scalar right :: .scalar left :: rest) =
    false := by
  simp only [cil_guard, leftKnown, rightKnown, Bool.or_false]
example : unspecifiedOperands (observerCount .sub_ovf_un) (.scalar right :: .scalar left :: rest) =
    false := by
  simp only [cil_guard, leftKnown, rightKnown, Bool.or_false]
example : unspecifiedOperands (observerCount .mul_ovf) (.scalar right :: .scalar left :: rest) =
    false := by
  simp only [cil_guard, leftKnown, rightKnown, Bool.or_false]
example : unspecifiedOperands (observerCount .mul_ovf_un) (.scalar right :: .scalar left :: rest) =
    false := by
  simp only [cil_guard, leftKnown, rightKnown, Bool.or_false]

end Guards

end FaultingArithmetic

section LocalAddress
open CIL CIL.Safety

-- Taking a span local's address pushes the view the local holds, exactly as loading it does.
example (body : CIL.Method) (pc : Nat) (args stack : List CIL.Safety.Value)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) (width : Nat) (writable : Bool)
    (view : Option SpanView)
    (slot : frame.locals[0]? = some (.span width writable view)) :
    step body (.localAddr 0) pc args frame stack memory =
      step body (.local 0) pc args frame stack memory := by
  simp only [step_localAddr_eq, step_local_eq, slot, localAddress]

-- Taking a byte home's address pushes the formed home reference.
example (body : CIL.Method) (pc : Nat) (args stack : List CIL.Safety.Value)
    (frame : CIL.Safety.Frame) (memory : CIL.Safety.Memory) (kind : CIL.LocalKind)
    (home : CIL.Safety.Reference) (slot : frame.locals[0]? = some (.bytes kind home)) :
    step body (.localAddr 0) pc args frame stack memory = do
      let address ← formValue memory (.address home)
      return FrameAction.next (pc + 1) (address :: stack) frame memory := by
  simp only [step_localAddr_eq, slot, localAddress]

end LocalAddress

-- Every generated faulting and `conv.i` equation exists and uses only the allowed axioms. At
-- equal widths a faulting equation keeps its helper folded with the operand guard decided, the
-- form the checked bridge reads; an unfolded unsigned bound would expand `2 ^ width`. Mixed
-- widths fault.
run_cmd do
  let binary := ["div", "div_un", "rem", "rem_un", "add_ovf", "add_ovf_un", "sub_ovf",
    "sub_ovf_un", "mul_ovf", "mul_ovf_un"]
  let helperOf (op : String) : Name :=
    if op.startsWith "div" || op.startsWith "rem" then ``CIL.divideValues else ``CIL.checkedValues
  let folded : List (String × Name) :=
    binary.flatMap (fun op =>
      [(s!"{op}_i32_i32", helperOf op), (s!"{op}_i64_i64", helperOf op)]) ++
    ["conv_ovf", "conv_ovf_un"].flatMap fun op =>
      [(s!"{op}_i32", ``CIL.convertInteger), (s!"{op}_i64", ``CIL.convertInteger)]
  let faulting := binary.map (s!"{·}_i32_i64")
  let plain := ["conv_i_i32", "conv_i_i64"]
  let names := (folded.map (·.1) ++ faulting ++ plain).map fun suffix =>
    `CIL.Safety ++ Name.mkSimple s!"step_{suffix}_eq"
  unless names.length == 36 do throwError "expected 36 equations, listed {names.length}"
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  for equation in names do
    unless (← getEnv).contains equation do throwError "missing {equation}"
    let axioms ← collectAxioms equation
    unless axioms.all allowed.contains do throwError "{equation} depends on {axioms}"
  for (suffix, helper) in folded do
    let equation := `CIL.Safety ++ Name.mkSimple s!"step_{suffix}_eq"
    let type := (← getConstInfo equation).type
    unless (type.find? (·.isAppOf helper)).isSome do
      throwError "{equation} no longer applies {helper}"
    if (type.find? fun term => term.isAppOf ``Bool.rec ||
        term.isConstOf ``CIL.Safety.unspecifiedOperands).isSome then
      throwError "{equation} leaves the operand guard undecided"
  for suffix in faulting do
    let equation := `CIL.Safety ++ Name.mkSimple s!"step_{suffix}_eq"
    let some (_, _, rhs) := (← getConstInfo equation).type.getForallBody.eq?
      | throwError "{equation} is not an equation"
    unless rhs.isAppOf ``Except.error do throwError "{equation} does not fault: {rhs}"

end Tests.InterpreterEquations
