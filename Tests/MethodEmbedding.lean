import CIL.Embedding.Tactic
import CIL.Safety.Embedding.DeadLocals
import CIL.Safety.Embedding.Simulation
import CIL.Safety.Embedding.Contracts
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
  code := [.arg 0, .brfalse 4, .arg 1, .ret, .arg 1, .ret]
  locals := [], returnsValue := true }

/-- `body` with a dead block before the branch target, as a profile-specific extraction emits it. -/
def inserted : Method := {
  code := [.arg 0, .brfalse 6, .arg 1, .ret,
    .unsupported "Unreachable under selected profile", .ldc_i4 9, .arg 1, .ret]
  locals := [], returnsValue := true }

-- Each `cil_embed` proof is kernel checked against the extracted method, never against `expected`.
theorem identity : MethodEmbeds [body] 0 body := by cil_embed

theorem dead_block_inserted : MethodEmbeds [inserted] 0 body := by cil_embed

/-- A placed canonical suffix reuses its proof at the checked embedding's new position. -/
theorem relocated_suffix (frame : Safety.Frame) (memory : Safety.Memory) (value : W32) :
    Safety.CodeAt inserted 6 [.arg 1, .ret] ∧
    Safety.WP (Safety.Execution (fun fuel => Safety.run [inserted] fuel 0 6
      [.scalar (.i32 0), .scalar (.i32 value)] frame [] memory))
      (fun (final, values) => final = Safety.leaveFrame frame memory ∧
        values = [.scalar (.i32 value)]) := by
  refine ⟨rfl, ?_⟩
  have placed : Safety.CodeAt body 4 [.arg 1, .ret] := rfl
  have canonical : Safety.WP (Safety.Execution (fun fuel =>
      Safety.run ([inserted].set 0 body) fuel 0 4
      [.scalar (.i32 0), .scalar (.i32 value)] frame [] memory))
      (fun (final, values) => final = Safety.leaveFrame frame memory ∧
        values = [.scalar (.i32 value)]) := by
    cil_contract_steps [placed]
    exact ⟨rfl, rfl⟩
  have embedded : Embeds body inserted [0, 1, 2, 3, 6, 7] := by constructor <;> rfl
  exact canonical.of_embedded_run rfl embedded

#print axioms relocated_suffix

/-- An expected body that still carries a dead block the extraction no longer emits. -/
def withDeadBlock : Method := {
  code := [.arg 0, .brfalse 6, .arg 1, .ret, .unsupported "Unreachable under selected profile",
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
  expected: CIL.Instruction.arg 1 none
  actual:   CIL.Instruction.arg 0 none
  the instructions differ
  expected pc 1 falls through to it, so it must be actual pc 2
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [{ inserted with code := inserted.code.set 2 (.arg 0 none) }] 0 body := by cil_embed

/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 1 maps to actual pc 1
  expected: CIL.Instruction.brfalse 4
  renamed:  CIL.Instruction.brfalse 6
  actual:   CIL.Instruction.brfalse 5
  code target differs: expected target 4 maps to actual pc 6, but the actual instruction targets 5; actual pc 5 (CIL.Instruction.ldc_i4 0x00000009#32) is not the image of any live expected pc
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [{ inserted with code := inserted.code.set 1 (.brfalse 5) }] 0 body := by
  cil_embed

-- The branch reaches an inserted live instruction, so the extracted method can return 9.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 1 maps to actual pc 1
  expected: CIL.Instruction.brfalse 4
  renamed:  CIL.Instruction.brfalse 6
  actual:   CIL.Instruction.brfalse 4
  code target differs: expected target 4 maps to actual pc 6, but the actual instruction targets 4; actual pc 4 (CIL.Instruction.ldc_i4 0x00000009#32) is not the image of any live expected pc
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [{ body with code := [.arg 0, .brfalse 4, .arg 1, .ret, .ldc_i4 9, .ret, .arg 1, .ret] }] 0 body := by
  cil_embed

-- The fallthrough of the branch reaches an inserted instruction.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 2 maps to actual pc 2
  expected: CIL.Instruction.arg 1 none
  actual:   CIL.Instruction.ldc_i4 0x00000009#32
  the instructions differ
  expected pc 1 falls through to it, so it must be actual pc 2
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [{ body with code := [.arg 0, .brfalse 5, .ldc_i4 9, .arg 1, .ret, .arg 1, .ret] }] 0 body := by
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

/-- A four-limb scalar multiply as extracted under the scalar profile, with two dead blocks. -/
def mulScalar : Program := [actual]

-- The literal body the consumer proof was written against omits the 12 dead instructions.
theorem mulscalar_embeds : MethodEmbeds mulScalar 0 expected := by cil_embed

-- The same body naming a different callee changes reachable behaviour.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 188 maps to actual pc 200
  expected: CIL.Instruction.call 8 5
  actual:   CIL.Instruction.call 7 5
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
  { code := [.br 1, .throw "Overflow"], locals := [], returnsValue := false }

/-- `thrower` with a dead block before the throw and unused reference and span locals. -/
def throwerDead : Method := {
  code := [.br 2, .unsupported "Unreachable under selected profile", .throw "Overflow"]
  locals := [.nullRef, .nullRef], localKinds := [.reference, .span 1 false], returnsValue := false }

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
a dropped local is not a reference or span, and only these dead locals are supported
-/
#guard_msgs (substring := true) in
example : MethodEmbedsDeadLocals
    [{ stored with locals := [.nullRef, .unmodeled], localKinds := [.reference, .word64] }] 0
    stored := by
  cil_embed

/-- Both readonly empty spans and uninitialized writable spans allocate no frame storage. -/
def storedDeadSpans : Method := {
  stored with
  locals := [.nullRef, .nullRef, .unmodeled]
  localKinds := [.reference, .span 4 false, .span 8 true] }

/-- Dead spans preserve the same frame and allocation identities as the kept method. -/
theorem stored_dead_spans_embeds : MethodEmbedsDeadLocals [storedDeadSpans] 0 stored := by
  cil_embed

#print axioms stored_dead_spans_embeds

/-- The original invocation proof transfers across both kinds of dead span slots. -/
theorem stored_dead_spans_returns (memory : Safety.Memory) (value : W32) :
    Safety.invoke [storedDeadSpans] (executionBound [stored] 0) 0 [.scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) :=
  stored_dead_spans_embeds.invoke (stored_invocation memory value)

#print axioms stored_dead_spans_returns

/-- Primitive, aggregate and vector span widths permit both empty initializers. -/
theorem dead_span_kinds_supported :
    ([1, 2, 3, 4, 8, 16, 24, 32, 48, 64].all fun width => [false, true].all fun writable =>
      [.nullRef, .unmodeled].all (rootLocal (.span width writable))) = true := by decide

#print axioms dead_span_kinds_supported

-- Invalid span widths must not turn a rejected frame entry into a padded successful one.
/--
error: cil_embed: the expected body does not embed into the extracted method
method index 0
a dropped local has a kind or initializer frame entry rejects
-/
#guard_msgs (substring := true) in
example : MethodEmbedsDeadLocals
    [{ stored with locals := [.nullRef, .nullRef], localKinds := [.reference, .span (2^64) false] }]
    0 stored := by cil_embed

/-- The kernel rejects unsupported widths and nonempty scalar initializers independently. -/
theorem invalid_dead_spans_rejected :
    rootLocal (.span (2^64) false) .nullRef = false ∧
    rootLocal (.span 0 true) .unmodeled = false ∧
    rootLocal (.span 4 true) (.i32 0) = false := by decide

#print axioms invalid_dead_spans_rejected

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
a dropped local has a kind or initializer frame entry rejects
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

/-- `vectorKept` with unused reference and span locals after its opaque one. -/
def vectorDead : Method := {
  vectorKept with
  locals := [.unmodeled, .nullRef, .unmodeled]
  localKinds := [.vector128, .reference, .span 2 true] }

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
  expected: CIL.Instruction.arg 0 none
  actual:   CIL.Instruction.arg 1 none
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

/-- An unsupported span width fails the embedding condition in the kernel itself. -/
theorem invalid_span_dead_rejected : ¬ MethodEmbedsDeadLocals
    [{ stored with locals := [.nullRef, .nullRef], localKinds := [.reference, .span (2^64) false] }]
    0 stored := by
  rintro ⟨actual, map, found, embeds⟩
  cases found
  exact absurd embeds.dead (by decide)

#print axioms invalid_span_dead_rejected

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

/-! Declared signatures, environments and link tables are embedding fields: an embedding that
    differs in any of them is rejected, and the diagnostic names the first one. -/
namespace Tests.MethodEmbedding.Metadata

open CIL

/-- Calls method 1 at pc 1 and enters a virtual table at pc 3. -/
def caller : Method := {
  code := [.arg 0, .call 1 1, .pop, .callVirtual [(.void, 2)] 1, .ret]
  locals := [], returnsValue := false }

/-- The pc map of a body onto itself. -/
private def identityMap : List Nat := [0, 1, 2, 3, 4]

theorem caller_links :
    linksOfCode caller.code = [(1, .direct 1), (3, .virtual [(.void, 2)])] := rfl

#print axioms caller_links

/-- Only linking instructions have entries, keyed by their pc. -/
example : linksOfCode [.nop, .call 1 2, .arg 0, .newAggregate 4 0 8, .ret] =
    [(1, .direct 1), (3, .aggregate 4 8)] := rfl

/-- A table written out in a literal wins over the default. -/
example : ({ caller with links := [] } : Method).linkAt 1 = none := rfl

/-- The first entry for a pc wins, as in `step`. -/
example : ({ code := [], locals := [], returnsValue := false, links :=
    [(2, .direct 5), (2, .direct 6)] } : Method).linkAt 2 = some (.direct 5) := rfl

example : caller.linkAt 0 = none := rfl
example : caller.linkAt 1 = some (.direct 1) := rfl

/-- Copying a body with new code keeps its table, so a rewrite of the code states its links. -/
example : ({ caller with code := [] } : Method).links = caller.links := rfl

/-- The declared type of a 32-bit integer parameter. -/
def int32 : Extraction.TypeExpr := .atom Extraction.runtimeScope "System.Int32"

/-- An instance method's declared types start after `this`. -/
def instanceSignature : DeclaredSignature := {
  receiver := some .object, parameters := [int32], returnType := .void }

example : instanceSignature.argumentType 0 = none := rfl
example : instanceSignature.argumentType 1 = some int32 := rfl
example : instanceSignature.argumentType 2 = none := rfl

/-- A static method's first argument is its first declared parameter. -/
example : { instanceSignature with receiver := none }.argumentType 0 =
    some int32 := rfl
example : { instanceSignature with receiver := none }.argumentType 1 = none := rfl

theorem caller_embeds : MethodEmbeds [caller] 0 caller := by cil_embed

#print axioms caller_embeds

/-- caller with another declared signature. -/
private def otherSignature : Method := { caller with declared := instanceSignature }
/-- caller with other layout tables. -/
private def otherEnvironment : Method :=
  { caller with environment := { layouts := #[⟨⟨4, []⟩, 4⟩] } }
/-- caller with another link for its call. -/
private def otherLink : Method :=
  { caller with links := [(1, .direct 9), (3, .virtual [(.void, 2)])] }

theorem declared_rejected : ¬ Embeds caller otherSignature identityMap :=
  fun embedded => absurd embedded.declared (by decide)

theorem environment_rejected : ¬ Embeds caller otherEnvironment identityMap :=
  fun embedded => absurd embedded.environment (by decide)

theorem links_rejected : ¬ Embeds caller otherLink identityMap :=
  fun embedded => absurd embedded.links (by decide +kernel)

/-- info: 'Tests.MethodEmbedding.Metadata.declared_rejected' does not depend on any axioms -/
#guard_msgs in #print axioms declared_rejected
/-- info: 'Tests.MethodEmbedding.Metadata.environment_rejected' depends on axioms:
  [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms environment_rejected
/-- info: 'Tests.MethodEmbedding.Metadata.links_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms links_rejected

/-- The diagnostic of a link difference names the actual pc of the call. -/
example : (MethodBinding.embedFailure caller otherLink identityMap).map Prod.snd =
    some (some 1) := by decide +kernel

example : (MethodBinding.embedFailure caller otherSignature identityMap).map Prod.snd =
    some none := by decide +kernel

example : (MethodBinding.embedFailure caller otherEnvironment identityMap).map Prod.snd =
    some none := by decide +kernel

example : MethodBinding.embedFailure caller caller identityMap = none := by decide +kernel

/-- A literal that does not bind is told which field differs, and what each side has. -/
example : (MethodBinding.methodDifferences caller otherSignature).length = 1 := by
  decide +kernel
example : (MethodBinding.methodDifferences caller otherEnvironment).length = 1 := by
  decide +kernel
example : (MethodBinding.methodDifferences caller otherLink).length = 1 := by decide +kernel

example : (MethodBinding.methodDifferences caller otherSignature).head?.map
    (·.startsWith "field declared:") = some true := by decide +kernel
example : (MethodBinding.methodDifferences caller otherEnvironment).head?.map
    (·.startsWith "field environment:") = some true := by decide +kernel
example : (MethodBinding.methodDifferences caller otherLink).head?.map
    (·.startsWith "field links:") = some true := by decide +kernel

/-- What an extraction emits when a dead block puts the call at pc 3. -/
def moved : Method := {
  code := [.arg 0, .br 3, .unsupported "Unreachable under selected profile", .call 1 1, .ret]
  locals := [], returnsValue := true }

/-- The body a proof uses, with its call at pc 2. `withCode` gives it that pc's link. -/
def viaWithCode : Method := moved.withCode [.arg 0, .br 2, .call 1 1, .ret]

/-- The same code through a structure update, which keeps the link table of the call at pc 3. -/
def viaUpdate : Method := { moved with code := [.arg 0, .br 2, .call 1 1, .ret] }

theorem with_code_embeds : MethodEmbeds [moved] 0 viaWithCode := by cil_embed

#print axioms with_code_embeds

example : viaWithCode.linkAt 2 = some (.direct 1) := rfl
example : viaWithCode.linkAt 3 = none := rfl
example : viaUpdate.linkAt 2 = none := rfl

/-- The update leaves the link at pc 3, so its call has no link and the embedding fails. -/
theorem update_rejected : ¬ Embeds viaUpdate moved [0, 1, 3, 4] :=
  fun embedded => absurd embedded.links (by decide +kernel)

#print axioms update_rejected

-- The diagnostic of the rejected update names `withCode`.
#guard ((MethodBinding.embedFailure viaUpdate moved [0, 1, 3, 4]).map fun failure =>
    (failure.1.splitOn "withCode").length) == some 2

#guard ((MethodBinding.methodDifferences moved viaWithCode).map fun line =>
    (line.splitOn "withCode").length) == [1, 2]

/-- The static field the fixtures below read. -/
def staticField : StaticDescriptor :=
  { identity := 1, fieldName := "Fixture::Value", bytes := List.replicate 8 0 }

/-- What an extraction emits when a dead block puts a static read at pc 2. -/
def staticMoved : Method := {
  code := [.branch 2, .unsupported "Unreachable under selected profile",
    .memory (.staticAddress (List.replicate 8 0)), .pop, .ret]
  locals := [], returnsValue := false, staticSites := [(2, staticField)] }

/-- The body a proof uses, with its static read at pc 1; `withCode` leaves it no static sites. -/
def staticWritten : Method :=
  staticMoved.withCode [.branch 1, .memory (.staticAddress (List.replicate 8 0)), .pop, .ret]

/-- Whether the first embedding failure of `expected` contains each of `phrases`. -/
def failureMentions (expected : Method) (phrases : List String) : Bool :=
  match MethodBinding.embedFailure expected staticMoved [0, 2, 3, 4] with
  | some (message, _) => phrases.all fun phrase => (message.splitOn phrase).length > 1
  | none => false

-- Without sites the descriptor lists differ, and the message says what to supply.
#guard failureMentions staticWritten ["static descriptors", "staticSites :="]

-- A site kept at the extraction's pc resolves no descriptor at the body's read.
#guard failureMentions { staticWritten with staticSites := [(2, staticField)] }
  ["different static descriptor", "staticSites :="]

theorem static_sites_embed :
    MethodEmbeds [staticMoved] 0 { staticWritten with staticSites := [(1, staticField)] } := by
  cil_embed

#print axioms static_sites_embed

/-- A table whose keys do not ascend, with a repeated pc whose first entry wins. -/
def unsortedTable : List (Nat × Link) := [(3, .direct 1), (1, .direct 2), (3, .direct 9)]

/-- The table takes the scan, since its keys do not ascend. -/
example : Extraction.linkKeysAscend 0 unsortedTable = false := by decide

/-- The scan answers each query with the first entry for it, in query order. -/
example : Extraction.linkReads unsortedTable [1, 3, 2] =
    [some (.direct 2), some (.direct 1), none] := by decide

/-- The walk over this table would stop at `(3, .direct 1)` for pc 1 and miss `(1, .direct 2)`,
    which is why a table whose keys do not ascend takes the scan. -/
example : Extraction.linkWalk unsortedTable unsortedTable 0 [1] ≠
    [1].map (linkLookup unsortedTable) := by decide

/-- An ascending table read with decreasing queries, as a map that reorders blocks gives: the
    walk starts again from the head at pc 1, below pc 3, and finds the entry it had passed. -/
example : Extraction.linkReads [(1, .direct 2), (3, .direct 1)] [3, 1, 2] =
    [some (.direct 1), some (.direct 2), none] := by decide

/-- A table with a link at every even pc. -/
def evenTable : List (Nat × Link) := (List.range 20).map fun index => (2 * index, .direct index)

/-- Queries that descend at every other step, below and above each key, read as scans would. -/
example : Extraction.linkWalk evenTable evenTable 0
      [7, 2, 30, 0, 39, 38, 1, 12, 11, 40, 5, 4] =
    [7, 2, 30, 0, 39, 38, 1, 12, 11, 40, 5, 4].map (linkLookup evenTable) := by decide

/-- Fully descending queries read as scans would. -/
example : Extraction.linkWalk evenTable evenTable 0 (List.range 42).reverse =
    (List.range 42).reverse.map (linkLookup evenTable) := by decide

/-- An extraction that places the block the head branches to before the block after the head. -/
def reorderedExtraction : Method := {
  code := [.branch 1, .arg 1, .call 2 1, .pop, .ret, .arg 0, .call 1 1, .pop, .ret]
  locals := [], returnsValue := false }

/-- The body a proof uses, with the blocks in source order. -/
def reorderedWritten : Method :=
  reorderedExtraction.withCode
    [.branch 5, .arg 0, .call 1 1, .pop, .ret, .arg 1, .call 2 1, .pop, .ret]

-- The map sends the second block back to pc 1, so the link reads descend once.
#guard MethodBinding.alignLive reorderedWritten.code.toArray reorderedExtraction.code.toArray ==
  #[0, 5, 6, 7, 8, 1, 2, 3, 4]

theorem reordered_embeds : MethodEmbeds [reorderedExtraction] 0 reorderedWritten := by cil_embed

#print axioms reordered_embeds

/-- Where the walk never descends it answers as the scan does. -/
example : Extraction.linkReads [(1, .direct 2), (3, .direct 1)] [1, 2, 3] =
    [1, 2, 3].map (linkLookup [(1, .direct 2), (3, .direct 1)]) := by decide

/-- Whichever branch runs, the reads are the per-query lookups. -/
example : Extraction.linkReads unsortedTable [1, 3, 2] =
    [1, 3, 2].map (linkLookup unsortedTable) :=
  Extraction.linkReads_eq unsortedTable _

end Tests.MethodEmbedding.Metadata
