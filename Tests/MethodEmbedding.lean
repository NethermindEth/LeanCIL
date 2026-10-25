import CIL.Embedding.Tactic
import CIL.Safety.Embedding.DeadLocals
import CIL.Safety.Embedding.Simulation
import CIL.Safety.SymbolicExecution
import Tests.MulScalarFixture

namespace Tests.MethodEmbedding

open CIL

private def byteHomeBody : Method := {
  locals := [.v128 0], localKinds := [.vector128], returnsValue := false,
  code := [.local 0, .pop, .ret] }
private def opaqueHomeBody : Method := { byteHomeBody with opaqueVectorLocals := [0] }

example : CIL.MethodBinding.embedFailure byteHomeBody byteHomeBody [0, 1, 2] = none := by decide +kernel
example : (CIL.MethodBinding.embedFailure byteHomeBody opaqueHomeBody [0, 1, 2]).isSome = true := by decide +kernel
example : ¬ Embeds byteHomeBody opaqueHomeBody [0, 1, 2] := by
  intro embedded
  have metadata := embedded.opaqueVectorLocals
  change ([0] : List Nat) = [] at metadata
  cases metadata
example : MethodEmbeds [opaqueHomeBody] 0 opaqueHomeBody := by cil_embed

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

section DeadLocals

/-- Reads its one local, a null reference, then returns argument 0. -/
@[cil_code] def stored : Method := {
  code := [.local 0, .pop, .arg 0, .ret]
  locals := [.nullRef], localKinds := [.reference], returnsValue := true }

/-- `stored` as extracted with two unused reference locals after its own, as a profile-specific
    extraction emits them. -/
def storedDead : Method := {
  stored with
  locals := [.nullRef, .nullRef, .unmodeled]
  localKinds := [.reference, .reference, .reference] }

/-- The dead references are root slots, so dropping them keeps every allocation in place. -/
theorem stored_dead_embeds : MethodEmbedsDeadLocals [storedDead] 0 stored := by cil_embed

/-- With no dead locals the relation holds as for `MethodEmbeds`. -/
theorem stored_embeds : MethodEmbedsDeadLocals [stored] 0 stored := by cil_embed

/-- One stepped proof about `stored`: it returns its argument and leaves memory alone. -/
theorem stored_invocation (memory : Safety.Memory) (value : W32) :
    Safety.invoke [stored] (executionBound [stored] 0) 0 [.scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) := by
  cil_checked_steps

/-- `stored_invocation` covers the extraction without dead locals. -/
theorem stored_returns (memory : Safety.Memory) (value : W32) :
    Safety.invoke [stored] (executionBound [stored] 0) 0 [.scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) :=
  stored_embeds.invoke (stored_invocation memory value)

/-- The same `stored_invocation` covers the extraction with the dead locals. -/
theorem stored_dead_returns (memory : Safety.Memory) (value : W32) :
    Safety.invoke [storedDead] (executionBound [stored] 0) 0 [.scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) :=
  stored_dead_embeds.invoke (stored_invocation memory value)

/-- Jumps to a throw. -/
def thrower : Method :=
  { code := [.branch 1, .throw "Overflow"], locals := [], returnsValue := false }

/-- `thrower` as extracted with a dead block before the throw and an unused null reference. -/
def throwerDead : Method := {
  code := [.branch 2, .unsupported "Unreachable under selected profile", .throw "Overflow"]
  locals := [.nullRef], localKinds := [.reference], returnsValue := false }

/-- A throw of the expected body is raised by the extraction with the dead local. -/
theorem thrower_dead_raises (memory : Safety.Memory) :
    Safety.Raises [throwerDead] 0 [] memory "Overflow" :=
  have embeds : MethodEmbedsDeadLocals [throwerDead] 0 thrower := by cil_embed
  embeds.raises ⟨2, _, rfl, rfl⟩

/-- The relocated fault names the throw's pc in the extraction, past the dead block. -/
theorem thrower_dead_fault (memory : Safety.Memory) :
    Safety.invoke [throwerDead] 2 0 [] memory = .error ⟨0, 2, .thrown "Overflow"⟩ := by
  have embeds : EmbedsDeadLocals thrower throwerDead [0, 2] := by
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    constructor <;> rfl
  exact embeds.invoke_raise (index := 0) rfl (fault := ⟨0, 1, .thrown "Overflow"⟩) rfl rfl

-- A dead numeric local allocates a home and shifts later allocation identities.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
a dropped local is not a reference, and only reference dead locals are supported
-/
#guard_msgs (substring := true) in
example : MethodEmbedsDeadLocals
    [{ stored with locals := [.nullRef, .unmodeled], localKinds := [.reference, .word64] }] 0
    stored := by
  cil_embed

-- A span local allocates nothing either, but is not yet covered.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
a dropped local is not a reference, and only reference dead locals are supported
-/
#guard_msgs (substring := true) in
example : MethodEmbedsDeadLocals
    [{ stored with locals := [.nullRef, .nullRef], localKinds := [.reference, .span 4 false] }]
    0 stored := by
  cil_embed

-- A dead local before a kept one would renumber the kept local.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
actual locals do not start with the expected locals
-/
#guard_msgs (substring := true) in
example : MethodEmbedsDeadLocals
    [{ stored with locals := [.unmodeled, .nullRef], localKinds := [.word32, .reference] }] 0
    stored := by
  cil_embed

-- Frame entry rejects a reference initialized to anything but null or unmodeled.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
a dropped reference local has an initializer frame entry rejects
-/
#guard_msgs (substring := true) in
example : MethodEmbedsDeadLocals
    [{ stored with locals := [.nullRef, .i32 0], localKinds := [.reference, .reference] }] 0
    stored := by
  cil_embed

-- Frame entry rejects kinds and initializers of different lengths.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
the dropped locals have 0 kinds for 1 initializers
-/
#guard_msgs (substring := true) in
example : MethodEmbedsDeadLocals
    [{ stored with locals := [.nullRef, .nullRef], localKinds := [.reference] }] 0 stored := by
  cil_embed

-- An opaque local past the kept ones would make frame entry reject a dropped reference.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
an opaque vector local is not among the kept locals
-/
#guard_msgs (substring := true) in
example : MethodEmbedsDeadLocals
    [{ storedDead with opaqueVectorLocals := [1] }] 0
    { stored with opaqueVectorLocals := [1] } := by
  cil_embed

-- Parameter homes follow the locals in the frame, so padding would move them.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
the actual method has parameter homes
-/
#guard_msgs (substring := true) in
example : MethodEmbedsDeadLocals
    [{ storedDead with parameterHomes := [(0, .word32)] }] 0
    { stored with parameterHomes := [(0, .word32)] } := by
  cil_embed

/-- Returns argument 0 past an opaque 128-bit vector local it never reads. -/
@[cil_code] def vectorKept : Method := {
  code := [.arg 0, .ret]
  locals := [.unmodeled], localKinds := [.vector128], opaqueVectorLocals := [0]
  returnsValue := true }

/-- `vectorKept` as extracted with an unused reference local after its opaque one. -/
def vectorDead : Method := {
  vectorKept with
  locals := [.unmodeled, .nullRef]
  localKinds := [.vector128, .reference] }

/-- An opaque local is kept in place while a trailing dead reference is dropped. -/
theorem vector_dead_embeds : MethodEmbedsDeadLocals [vectorDead] 0 vectorKept := by cil_embed

/-- `vectorKept` returns its argument; its opaque local allocates nothing. -/
theorem vector_invocation (memory : Safety.Memory) (value : W32) :
    Safety.invoke [vectorKept] (executionBound [vectorKept] 0) 0 [.scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) := by
  cil_checked_steps

/-- Frame entry with opaque locals pads the same way, so the invocation transfers. -/
theorem vector_dead_returns (memory : Safety.Memory) (value : W32) :
    Safety.invoke [vectorDead] (executionBound [vectorKept] 0) 0 [.scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) :=
  vector_dead_embeds.invoke (vector_invocation memory value)

-- A live instruction that differs is still reported under dead locals.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 2 maps to actual pc 2
  expected: CIL.Op.arg 0 none
  actual:   CIL.Op.arg 1 none
  the instructions differ
-/
#guard_msgs (substring := true) in
example : MethodEmbedsDeadLocals
    [{ storedDead with code := [.local 0, .pop, .arg 1, .ret] }] 0 stored := by
  cil_embed

/-- A numeric dead local fails the kernel-checked condition itself, not only the tactic. -/
theorem numeric_dead_rejected : ¬ MethodEmbedsDeadLocals
    [{ stored with locals := [.nullRef, .unmodeled], localKinds := [.reference, .word64] }] 0
    stored := by
  rintro ⟨actual, map, found, embeds⟩
  cases found
  exact absurd embeds.dead (by decide)

-- `MethodEmbeds` still demands equal locals.
example : ¬ MethodEmbeds [storedDead] 0 stored := by
  rintro ⟨actual, map, found, embedded⟩
  cases found
  have locals := embedded.locals
  simp [storedDead, stored] at locals

end DeadLocals

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

/-- info: 'Tests.MethodEmbedding.stored_dead_returns' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stored_dead_returns

/-- info: 'Tests.MethodEmbedding.stored_dead_embeds' depends on axioms:
  [propext] -/
#guard_msgs (whitespace := lax) in #print axioms stored_dead_embeds

/-- info: 'Tests.MethodEmbedding.stored_embeds' depends on axioms:
  [propext] -/
#guard_msgs (whitespace := lax) in #print axioms stored_embeds

/-- info: 'Tests.MethodEmbedding.stored_invocation' depends on axioms:
  [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stored_invocation

/-- info: 'Tests.MethodEmbedding.stored_returns' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stored_returns

/-- info: 'Tests.MethodEmbedding.thrower_dead_raises' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms thrower_dead_raises

/-- info: 'Tests.MethodEmbedding.thrower_dead_fault' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms thrower_dead_fault

/-- info: 'CIL.MethodEmbedsDeadLocals.method_holds' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CIL.MethodEmbedsDeadLocals.method_holds

/-- info: 'CIL.MethodEmbedsDeadLocals.holds' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CIL.MethodEmbedsDeadLocals.holds

/-- info: 'Tests.MethodEmbedding.vector_dead_returns' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms vector_dead_returns

/-- info: 'Tests.MethodEmbedding.vector_dead_embeds' depends on axioms:
  [propext] -/
#guard_msgs (whitespace := lax) in #print axioms vector_dead_embeds

/-- info: 'Tests.MethodEmbedding.vector_invocation' depends on axioms:
  [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms vector_invocation

/-- info: 'Tests.MethodEmbedding.numeric_dead_rejected' depends on axioms:
  [propext] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_dead_rejected

end Tests.MethodEmbedding
