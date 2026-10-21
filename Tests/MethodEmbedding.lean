import CIL.Embedding.Tactic
import CIL.Safety.Embedding.Simulation
import CIL.Safety.SymbolicExecution
import Tests.MulScalarFixture

namespace Tests.MethodEmbedding

open CIL

/-- Returns argument 1 on both paths; pc 4 is reached only by the branch. -/
@[cil_code] def body : Method := {
  code := [.arg 0, .brzero 4, .arg 1, .ret, .arg 1, .ret]
  locals := [], returnsValue := true }

/-- `body` with a dead block before the branch target, as a profile-specific extraction emits it. -/
def inserted : Method := {
  code := [.arg 0, .brzero 6, .arg 1, .ret,
    .unsupported "Unreachable under selected profile", .const32 9, .arg 1, .ret]
  locals := [], returnsValue := true }

-- Each `cil_embed` proof is kernel checked against the extracted method, never against `expected`.
theorem identity : MethodEmbeds [body] 0 body := by cil_embed

theorem dead_block_inserted : MethodEmbeds [inserted] 0 body := by cil_embed

/-- An expected body that still carries a dead block the extraction no longer emits. -/
def withDeadBlock : Method := {
  code := [.arg 0, .brzero 6, .arg 1, .ret, .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile", .arg 1, .ret]
  locals := [], returnsValue := true }

theorem dead_block_removed : MethodEmbeds [body] 0 withDeadBlock := by cil_embed

-- A dead expected block may face arbitrary live actual code.
theorem dead_block_replaced : MethodEmbeds [inserted] 0 withDeadBlock := by cil_embed

theorem second_method : MethodEmbeds [{ code := [.ret], locals := [], returnsValue := false }, inserted] 1 body := by
  cil_embed

-- A behaviour proved over the literal body transfers to the extracted program with shifted targets.
theorem inserted_invocation (memory : Safety.Memory) (condition value : W32) :
    Safety.invoke [inserted] (executionBound [body] 0) 0
      [.scalar (.i32 condition), .scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) := by
  apply dead_block_inserted.invoke
  show Safety.invoke [body] _ 0 _ memory = _
  by_cases zero : condition = 0
  · have truth : truth (.i32 condition) = some false := by simp [truth, zero]
    cil_checked_steps [truth]
  · have truth : truth (.i32 condition) = some true := by simp [truth]; exact zero
    cil_checked_steps [truth]

/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 2 maps to actual pc 2
  expected: CIL.Op.arg 1 none
  actual:   CIL.Op.arg 0 none
  the instructions differ
  expected pc 1 falls through to it, so it must be actual pc 2
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [{ inserted with code := inserted.code.set 2 (.arg 0 none) }] 0 body := by cil_embed

/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 1 maps to actual pc 1
  expected: CIL.Op.brzero 4
  renamed:  CIL.Op.brzero 6
  actual:   CIL.Op.brzero 5
  code target differs: expected target 4 maps to actual pc 6, but the actual instruction targets 5; actual pc 5 (CIL.Op.const32 0x00000009#32) is not the image of any live expected pc
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [{ inserted with code := inserted.code.set 1 (.brzero 5) }] 0 body := by cil_embed

-- The branch reaches an inserted live instruction, so the extracted method can return 9.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 1 maps to actual pc 1
  expected: CIL.Op.brzero 4
  renamed:  CIL.Op.brzero 6
  actual:   CIL.Op.brzero 4
  code target differs: expected target 4 maps to actual pc 6, but the actual instruction targets 4; actual pc 4 (CIL.Op.const32 0x00000009#32) is not the image of any live expected pc
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [{ body with code := [.arg 0, .brzero 4, .arg 1, .ret, .const32 9, .ret, .arg 1, .ret] }] 0 body := by
  cil_embed

-- The fallthrough of the branch reaches an inserted instruction.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 2 maps to actual pc 2
  expected: CIL.Op.arg 1 none
  actual:   CIL.Op.const32 0x00000009#32
  the instructions differ
  expected pc 1 falls through to it, so it must be actual pc 2
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [{ body with code := [.arg 0, .brzero 5, .const32 9, .arg 1, .ret, .arg 1, .ret] }] 0 body := by
  cil_embed

/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
non-code field differs (left: expected, right: actual)
field locals: first difference at index 0 (left length 0, right length 1)
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [{ inserted with locals := [.i32 0] }] 0 body := by cil_embed

/--
error: cil_embed: the expected body does not embed into the extracted method
method index 3: the program has 1 methods
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [inserted] 3 body := by cil_embed

section MulScalar

open Tests.MulScalarFixture

/-- The int256 scalar multiply as extracted under the scalar profile, with two dead blocks. -/
def mulScalar : Program := [actual]

-- The literal body the consumer proof was written against omits the 12 dead instructions.
theorem mulscalar_embeds : MethodEmbeds mulScalar 0 expected := by cil_embed

-- The same body naming a different callee changes reachable behaviour.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 188 maps to actual pc 200
  expected: CIL.Op.call 8 5
  actual:   CIL.Op.call 7 5
  the instructions differ
-/
#guard_msgs (substring := true) in
example : MethodEmbeds mulScalar 0 (fullBody profile 9 5 8) := by cil_embed

end MulScalar

-- Tactic proofs and the transport theorems use only the standard axioms.
/-- info: 'Tests.MethodEmbedding.mulscalar_embeds' depends on axioms: [propext] -/
#guard_msgs in #print axioms mulscalar_embeds

/-- info: 'Tests.MethodEmbedding.dead_block_inserted' depends on axioms: [propext] -/
#guard_msgs in #print axioms dead_block_inserted

/-- info: 'CIL.Safety.step_relabel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Safety.step_relabel

/-- info: 'CIL.Safety.run_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Safety.run_refines

/-- info: 'CIL.MethodEmbeds.invoke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MethodEmbeds.invoke

/-- info: 'CIL.MethodEmbeds.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MethodEmbeds.certificate

end Tests.MethodEmbedding
