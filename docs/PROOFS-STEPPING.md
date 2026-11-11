# Instruction composition and proof reduction

Reference for the stepping tactics: which tactic steps which goal, the facts each instruction
family needs, the goals a tactic leaves, and how loops, segments and `WP` goals compose. Read it
when a stepping tactic stops or leaves a goal you did not expect. [Contracts](PROOFS-CONTRACTS.md)
covers calls through `MethodContract`.

Use `CIL.Safety.invoke` for specifications that include checked memory execution. State the
mathematical contract and its input and memory preconditions independently of the implementation.
The [soundness boundary](SOUNDNESS.md) describes what a successful checked execution establishes.

## Compose instructions

Import `CIL.Safety.SymbolicExecution` and mark definitions used for instruction lookup with
`@[cil_code]`. This example executes eight instructions on symbolic inputs and preserves arbitrary
caller memory:

```lean
import CIL.Safety.SymbolicExecution

namespace ProofGuide

@[cil_code] def arithmeticMethod : CIL.Method := {
  code := [.arg 0, .arg 1, .const32 1, .shl, .add, .const32 0, .gtu, .ret]
  locals := [], returnsValue := true }

theorem checked_arithmetic (memory : CIL.Safety.Memory) (left right : CIL.W32) :
    CIL.Safety.invoke [arithmeticMethod] 9 0
      [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (if left + (right <<< 1) > 0 then 1 else 0))]) := by
  cil_checked_steps
#print axioms checked_arithmetic

end ProofGuide
```

This body is handwritten. A proof about an assembly must bind its body to the generated program
(see [Bind bodies to the extraction](PROOFS-BINDING.md#bind-bodies-to-the-extraction)) and pass
verification.

`cil_checked_steps` composes `invoke_of_run`, `run_next`, `run_return` and `run_call_of_invoke`. It
checks method and instruction lookups, frame setup and the returned values, and infers
intermediate states. Apply the lemmas by hand from
[StepComposition](../CIL/Safety/StepComposition.lean) and
[CallComposition](../CIL/Safety/CallComposition.lean).

### Choose a stepping tactic

The fact list holds proved facts the steps depend on: hypotheses, lemmas or applied terms.

| Goal | Tactic | Notes |
| --- | --- | --- |
| An `invoke` or `run` equality, to a result or a located fault | `cil_checked_steps [facts]` | The list is optional. Crosses any number of calls |
| The same, stopping early | `cil_checked_steps n [facts]` | Takes exactly `n` steps and leaves the residual `run` equation; errors unless all `n` are taken |
| One fetched instruction's `step` equation | `cil_checked_step [facts]` | |
| `WP`, or an existential successful execution | `cil_contract_steps [facts]` | Applies callee contracts; see [contract stepping](PROOFS-CONTRACTS.md#step-a-caller-through-its-callees) |
| The same, stopping early | `cil_contract_steps n [facts]`, or `[facts] until continuation` | Takes at most `n` steps and stops without an error when one fails |
| One contract step | `cil_contract_step [facts]` | `cil_contract_step_normalized [facts]` is the same step over facts a walk has already prepared |
| A `Raises` goal | `cil_raise_steps [facts]` | See [exceptional outcomes](PROOFS-CONTRACTS.md#name-exceptional-outcomes) |
| Numeric local stores and loads over symbolic memory | `cil_checked_steps (snapshots := snapshots) [facts]`, `cil_contract_steps (snapshots := snapshots) [facts]` | See [snapshot walks](PROOFS-CONTRACTS.md#walk-local-stores-and-loads-with-snapshots) |
| A `Segment` or `SegmentRun` boundary | `cil_segment n [facts]`, `cil_segment_steps [facts]` | See [segments](#place-code-and-compose-segments) |
| A loop path | `cil_loop_steps`, `cil_loop_advance`, `cil_loop_recurse`, `cil_loop_call`, `cil_loop_finish` | See [loops](#step-loops) |

In every counted form a call counts as one step: the callee runs to its return and the residual
starts at the caller's next instruction. `cil_checked_steps`, `cil_contract_steps` and
`cil_raise_steps` fail when they cannot take a first step, instead of returning the goal unchanged.

### Goals the tactics accept

- A goal `∃ fuel, invoke program fuel method args memory = result` is opened with
  `CIL.executionBound program method` as its fuel, so a proof states none. Fuel that is already a
  term is left as written.
- `cil_checked_steps` and `cil_contract_steps` unfold the `args`, `results`, `pre`, `footprint`
  and `post` of each defined contract, at entry and in each call's continuation, so a goal needs
  no `dsimp only [contract]` first. A contract variable and `Returns` stay folded, as does a goal
  a proof enters by hand.
- An existential `run` budget can come from a method-body lookup hypothesis or from a `CodeAt`
  placement beginning at its starting pc. The remaining code length supplies a candidate budget;
  the proof must establish that it suffices. Use `WP` and a proved suffix when composing code
  with independent call or loop budgets.
- A located-fault goal `invoke p fuel m args memory = .error ⟨m, pc, fault⟩` enters through
  `invoke_of_run_fault` and steps the same way. At the stated `pc` the tactic first tries
  `run_fault`, which closes the goal when the fetched step raises exactly `fault`; other steps
  continue through `run_next`. Pass the fact that makes the step fail, such as
  `divRemBits_zero true left` for a zero divisor, with implicit widths given when its premise
  cannot fix them. A goal already stated over `run` tries neither entry lemma, and a goal stating
  a successful result never tries a fault lemma.
  [MathDivRemQuotient](../Examples/Proofs/MathDivRemQuotient.lean) proves its success and both
  `div` faults this way.
- A run-to-run goal `run p (fuel + n) m 0 .. = run p fuel m n ..` closes with
  `cil_checked_steps` when the stepped state is syntactically the target: symbolic `fuel` stops
  stepping there. With literal fuel and a target equal only up to rewriting, use
  `cil_checked_steps n [facts]` and prove the residual `run` equation.
  `MemoryBelow.frame_round_trip` carries caller memory across `enterFrame` and `leaveFrame` when
  the callee body keeps it.

### Lookups

Every stepping, call and loop tactic closes method and instruction lookups with
`cil_lookup [facts]`: by evaluation of an `@[cil_code]` extraction, by `rfl`, from a lookup
hypothesis such as `found : program[index]? = some (body profile)`, or by rewriting feature tests
in a profile-dependent body with the facts. A proof over an abstract `program` therefore steps
like one over `Extracted.program`.

- A computed position such as `base + stride * index.val` for `index : Fin n` resolves with a
  closed bound of at most 64; each finite case uses the same instruction equations or `CodeAt`
  placement as a literal lookup. A quantified lookup theorem is applied directly, and its index
  domain need not satisfy that bound.
- Named method indices reduce normally.
- A closed position outside a concrete body reports its position and the body length.
- A lookup at a program counter that holds an undecided branch condition fails with
  `cil_lookup: undecided branch` and is not evaluated.

### Facts read from the context

A named `LoopFrame` in the context supplies local addresses and remembered values to straight-line
stepping, by the fact-gathering rules of the loop tactics. Unknown homes provide storage and
address facts only; a checked write or helper postcondition must establish their contents.

The stepping tactics read object evidence from the context, so a fact list does not repeat it. A
hypothesis is recognized by the head of its statement, also as one side of a conjunction, when the
goal names its object:

| Hypothesis | Facts read |
| --- | --- |
| `live : LiveObject memory object` | `live.formed` |
| `Readable`, `Owned` or `Holds` of a scalar field | `readable.live.formed`, `readable.located` and the unsigned load of `readable.facts`, which pushes the field's value |
| `Readable`, `Owned` or `Holds` of a reference or array field | `readable.live.formed` and `readable.located` |
| `ReferenceArray.Live`, `Readable`, `Owned` or `Holds` | `live.formed` and `live.located` |

Pass a fact that takes a further premise yourself: `readable.facts held targetLive` for the load of
a reference field, `readable.signedFacts` for a signed narrow load, and the equation a store
returns. A checked reference load also makes its target's object evidence reachable, including
when its equation is supplied through a projection such as `readable.facts held live`. Evidence
for an unrelated object or memory is excluded. A fact passed explicitly is used as given and not
read again. Each fact read is added to the goal as a hypothesis, so a goal the tactics leave
shows it.

### Supply step facts

`cil_checked_step [facts]` first tries each supplied step fact for the fetched opcode: a fact
whose conclusion is `step body op pc args frame stack memory = result`, given as a hypothesis, a
lemma, or an applied term such as `store value`. The fact is applied at reducible-and-instances
transparency, then retried with the `@[cil_code]` definitions in its type unfolded, so a fact
stated on the named body matches both a body reached through a lookup hypothesis and the literal
body that an extracted program's lookup produces. Otherwise the opcode selects the closing
strategy:

| Opcode | Strategy |
| --- | --- |
| Pure scalar operations | `rfl`, even when facts are supplied |
| Memory operations, local operations, instruction-dispatcher arms and branches | `cil_step` equations and the supplied facts, which keeps memory results in the form their facts name and resolves a branch condition before the next program counter is chosen |
| Unknown opcode heads | The equation path |

`cil_contract_step [facts]` prepares `facts` as `cil_checked_step` does, so a supplied `read` steps
a `.loadAggregate` through a managed-reference address there as well.

Pass facts about formation and successful memory operations, not evaluator definitions or monadic
binds. The tactics accept these fact forms:

| Situation | Fact |
| --- | --- |
| A branch on a symbolic condition | `v = 0` or `Not (v = 0)` on the condition value; no `CIL.truth` restatement is needed. A literal condition, such as the `1` a decided feature test pushes, decides itself and continues at a numeral program counter |
| An opcode index stated as closed arithmetic, such as `.local (↑(6 : Fin 10) + 1)` | Fact preparation also states it at the numeral, `.local 7`, the form a fetched opcode has |
| A read stated at a closed width, such as `read memory home (localWidth (.aggregate 32)) 1` | Fact preparation derives its load at the numeral width an opcode carries |
| A value known only as `argument : CIL.Value`, loaded as an argument or passed to a call | `numericValue argument = true`; preparation also states it over the unfolded definition, the form the checked value test has when the step reaches it |
| `bitcastByteBool`, whose operand must be `0` or `1` | None for a comparison result `if c then 1 else 0`; for any other int32, `bits.toNat ≤ 1`. The fact may bound a value inside width changes, as `field.toNat ≤ 1` does for the operand `(field.setWidth 8).setWidth 32` |
| A symbolic reference | Its formation equation; the equation stays usable without splitting the reference |

A branch whose condition the facts do not decide leaves the condition in the program counter,
`run p fuel m (if c then target else next) ..`, and stepping stops there. `split` gives both
successors and each resumes with the stepping tactic.

After each step the tactics evaluate closed literal operands with the `cil_literal` simp set: a
width conversion, sign extension or `toNat` of a bit-vector numeral, and a remainder of numerals
such as a masked shift count. A symbolic operand stays as stated, and `simp only [cil_literal]`
gives a hand-written step the same form. A `localResult kind value` whose constructors decide it
is stated as the value the load pushes, so a `.vector128` load of `.v128 bits` leaves `.v128 bits`
for the next fact; `cil_local_results` does the same for a hand-written step.

[Fact preparation](PROOFS-CONTRACTS.md#supply-facts-to-the-stepping-tactics) describes how local
facts are normalised and instantiated.

### Calls and returns

`cil_checked_side` closes the frame-entry and return premises (checked arguments, frame setup and
checked results) for the stepping, contract, outcome and loop tactics. It normalizes with the
closed `cil_side`, `cil_checked` and `cil_guard` sets plus supplied facts, the side-condition
rules the instruction equations also use.

At a call, including `callvirt` and the constructor call of `newobj`, `cil_checked_steps` proves
the callee by stepping it or from an invocation fact in context, then keeps stepping the caller
from the cleaned `returned ++ rest` stack. Over symbolic caller memory, frame setup of a method
with numeric locals is not a closed term; `bind_entry ... allocating` supplies its setup equation
and home facts instead (see [loop
scaffolding](PROOFS-BINDING.md#generate-loop-entry-and-cutpoint-scaffolding)).

At a fetched `.ret`, narrow returns included, the tactic leaves the equation between the computed
checked result and the stated result as a goal over the returned values, with no unexecuted `run`.
The goal closes automatically only when `with_reducible rfl` succeeds after frame cleanup, list
normalization and literal shift-count reduction. Cleanup also drops the narrowing of an `if p then
1 else 0` result, and the closing `simp` drops it from a comparison already decided to `1` or `0`,
so a narrow Boolean return needs no unfolding of `NarrowKind.extend`. Other mathematical results
can need a separate `simp` or case split. `cil_contract_steps` likewise leaves the return
postcondition as a goal, stated of the memory the body left when the returning frame is a literal
that owns no allocation.

### Instruction families

Intrinsic steps expose `checkedIntrinsic` and apply proved `@[cil_eval]` lemmas before unfolding
the intrinsic evaluator. Register consumer lemmas in the form
`CIL.evalIntrinsic operation operands = some result` with `BitVec.ofNat` operands, because
nonnegative `BitVec.ofInt` literals become `BitVec.ofNat` literals before matching. A supplied
evaluation fact may instead use a numeral operand, such as `.i32 27`: a second pass then respells
literal `BitVec.ofNat n k` operands as numerals and leaves symbolic `BitVec.ofNat n x` values
unchanged. The tactic keeps the lemma's result form, then removes literal stack `take`, `drop`,
`reverse` and append expressions before the next step. These rewrites do not simplify consumer
arithmetic or unfold consumer value definitions.

Value-only operations (checked arithmetic, conversions and division) have one equation per i32/i64
operand shape, generated by `cil_value_steps` when the library builds. The stepper has no
dispatcher-unfolding fallback for them. For a hand-written step, use the corresponding equation
directly or `simp only [cil_step, facts]`.

Reference and field instructions have one `@[cil_instruction_step]` equation per operand shape in
[InstructionSteps](../CIL/Safety/InstructionSteps.lean), which rewrites a step to checked memory
and formation operations. They cover the `instruction` arms of `load64`, `store64` and
`storeScalar` through a reference, `fieldAt` and `fieldAddress` on an address, `setFieldAt` of
width 1, 2, 4 or 8, `fieldAt` of width 4 or 8 on a struct value, `asRef`, `skipInit` and `initobj`.

- Supply successful encoded byte reads and writes directly: the stepper derives the scalar or
  vector bridge before stepping. Narrow scalar reads support signed and unsigned results. Facts
  may be quantified or nested in conjunctions.
- `CIL.Safety.CheckedMemoryFacts` exposes the vector load and store bridges for direct use.
- The bridges retain the operation's exact memory, reference, width and initialization checks;
  write authority alone does not establish a readable snapshot.
- When a supplied equation states the matching `instruction` result, the stepper selects that
  abstraction directly.
- The set is separate from `cil_step`: a hand-written `simp only [cil_step, facts]` stops at
  `instructionStep`. A `.call` step has its own `cil_step` equation, so a call checks its
  arguments without unfolding the dispatcher.

Aggregate loads and stores use the address-shape equations in
[AggregateMemorySteps](../CIL/Safety/AggregateMemorySteps.lean). A checked `readSnapshot` supplies
the actual initialization mask; it does not establish that every byte is initialized. Initialized
byte reads and writes reuse the corresponding snapshot bridges. Null faults retain the
instruction's requested width.

Each `.memory` operation has one equation per operand shape in `CIL.Safety.MemorySteps`. Supply
checked `read`, `write`, `add` and formation equations instead of evaluator definitions.

- A `memoryInstruction` or `staticInstruction` equation is usable when its complete operation,
  stack and memory match.
- Quantified and conjunction-wrapped equations are supported; an earlier memory's result cannot
  select the strategy for a later memory.
- The stepper chooses the matching abstraction or the opcode equation before simplification,
  without retrying dispatcher unfolds.
- Reference shapes `.null` and `.address r` normalize in the shared closed set, so a successful
  `add` fact on a known address needs no extra reference-conversion fact.
- Manual proofs can apply the matching opcode or operation equation directly.

A `.feature f` step pushes `body.profile.evaluate f`. For a known feature,
`cil_step` reduces that expression to the profile field; a symbolic `f` stays
`body.profile.evaluate f`, so a fact about it applies as stated. `cil_step` unfolds a method
definition or literal only as far as its profile, so a fact such as `profile.avx2 = true` decides
the test. Inside `cil_checked_step`, `cil_checked_steps`, `cil_contract_steps` and the loop
tactics, a local fact, proof term or global theorem stated through `evaluate` or a method's
profile projection, including one quantified over every feature, is normalized to that form.
Elsewhere, including `simp only [cil_step, facts]` and `cil_checked_step_equations`, state the
fact on the field or first run `simp only [CIL.Safety.reduceMethodProfile, cil_feature] at h`.

### Consumer stepping regressions

The public tactics handle store and load facts, branch conditions, memory operations, profile
lookups, intrinsic facts, comparisons and widening over symbolic values and memory, with no
consumer-specific execution rules. The [proof automation
regressions](VALIDATION-PROOFS.md#consumer-stepping-regressions) name the proof that pins each
case and its heartbeat budget.

### State goals with WP

`WP execution post` states that one finite budget and result satisfy an execution relation and
`post`. Import `CIL.Safety.WeakestPrecondition` for the predicate and its structural rules.
For successful checked execution, use `WP (Execution (fun fuel => invoke ...)) post`, with
`post : Memory × List Value → Prop`; `fun (final, values) => ...` names its two components, and
`Function.uncurry post` adapts a postcondition written as `Memory → List Value → Prop`.
`Execution` is equality to the interpreter's successful result, so every fault, including fuel
exhaustion, is rejected. `cil_contract_steps` accepts this form directly. `MethodContract.Holds`,
`LoopTerminates`, `Segment` and `LoopReaches` all use `WP`.

| Rule | Use |
| --- | --- |
| `WP.step` | Composes a fetched checked instruction |
| `WP.call` | Composes an actual helper invocation |
| `WP.sequence` | Composes two execution relations using their budget-composition law |
| `WP.of_prefix` | Transfers a successful suffix across an exact interpreter prefix |
| `WP.consequence` | Weakens the postcondition by an implication |
| `WP.frame` | Carries an assertion only when its preservation is proved for the execution relation; it never infers preservation from read or write permission |
| `WP.enter` | Requires actual checked arguments and frame allocation |
| `WP.returned` | Requires frame exit and checked returned values |
| `WP.adequate` | Exposes the underlying finite execution when an assembly certificate needs the raw interpreter equation |
| `WP.exists_execution` | Turns the existential execution goal a partial `cil_contract_steps` proof leaves into a `WP` goal, so a `WP` rule applies; its postcondition is inferred |
| `WP.of_embedded_run` | Transports a successful suffix through `CIL.Embeds`, reusing the checked embedding simulation |

`cil_contract_steps [facts] until suffix` accepts a `WP` suffix directly. For
`WP.of_embedded_run`, `CodeAt` identifies the suffix; embedding also checks instruction targets
and method metadata, since equal instruction lists alone do not justify relocating absolute
branches. `MethodContract.Holds.of_embeds` transports the complete contract through
`CIL.MethodEmbeds`, including its footprint and precondition.

### Place code and compose segments

A segment theorem over an abstract body states where its code sits with `CodeAt body start segment`
([CodeAt](../CIL/Safety/CodeAt.lean)) instead of `body.code = leading ++ segment ++ tail` and
`leading.length = start`. Pass `placed` directly to `cil_checked_steps [found, placed]`:

- `cil_lookup` uses the placement to fetch literal offsets, including both `start + 1 + 1` and
  `start + 2`. It also finds local placement hypotheses without listing them and accepts supplied
  placement expressions such as `region.append_left`.
- The fetched instruction must be inside the segment and agree with its code.
- `append`, `middle`, `take` and `drop` move a placement between a region and its segments, and
  `rfl` closes a concrete one.

`Segment program method start finish pre post` packages a checked prefix as a composable
contract. Assertions take the unchanged arguments and a `SegmentState` containing the frame, stack
and memory. Each admitted input supplies an output state and a cost, with an exact `run (fuel +
cost) = run fuel` equation for every continuation fuel. Both witnesses precede the universal
continuation budget; they cannot vary with it. The relation retains successful results, exhaustion
and located faults.

| Name | Use |
| --- | --- |
| `Segment.adequate` | States the exact equivalence |
| `Segment.trans` | Composes adjacent contracts and adds their costs |
| `Segment.run_exists` | Composes a suffix stated with `WP` |
| `Segment.consequence` | Changes assertions by proved implications |
| `SegmentState.exact` | Describes a known state |
| `cil_segment 3 [found, placed, facts]` | Proves the boundary of an exact-state contract with `cil_checked_steps`; fails unless the complete equation closes |
| `cil_segment_steps [facts]` | Proves a `SegmentRun` boundary directly |

Neither tactic invents a memory or availability premise. `LoopReaches` uses the same prefix
relation with an exact-target postcondition.

For numeric-local framing, record successful write equations in `SegmentLocalEffects`. The
destinations must occur in `segmentStores code`, read from the placed instructions.
`Segment.frameLocals` combines these effects with the initial `LocalSnapshots` and `WritableHomes`
to derive snapshots for `untouchedLocals code known`. Effects compose through `append` or `trans`;
one frame-rule application replaces separate disjoint-read proofs for all retained locals. The
numeric slot identities must remain fixed, and the frame-rule placement must belong to the running
method and end at the contract boundary. Indirect writes and calls need a proved memory effect;
absence of a direct `setLocal` is not evidence that an aliased byte-backed local keeps its value.

## Step loops

Import [LoopAutomation](../CIL/Safety/LoopAutomation.lean) for `cil_loop_steps [facts]`, which
composes an execution segment, and [LoopScaffold](../CIL/Safety/LoopScaffold.lean) for
`cil_loop_finish [facts]`, which proves an exit path and its postcondition. Supply an invariant and
a decreasing measure to the loop termination theorem; these tactics do not infer termination. See
[Countdown](../Examples/Proofs/Countdown.lean).

The fact list is optional: both tactics add the facts
[`gatherLoopFacts`](../CIL/Safety/LoopFacts.lean) finds, described under [loop verification
conditions](#loop-verification-conditions), so the list carries only invariant equations, the
positive side of a case split and other facts of no recognized shape. A case split's negative
side, such as `¬count = value`, is gathered and decides the branch. A step equation in the
context, quantified or not, is used whenever its instruction is reached. The exit closes with the
normalised facts, then again after unfolding `leaveFrame` and narrow extension, so a fact about
the exited frame's memory is tried before cleanup rewrites past it.

The loop tactics step one fetched instruction at a time and simplify literal stack `drop`, `take`,
`reverse` and append after each step. A tactic that cannot go on fails instead of leaving a goal,
and its message names the pc. Messages, and the loop goals a walk hands back, write each pc as a
literal, such as `18` rather than `17 + 1`. Goals print a bit-vector literal of `2 ^ 16` or more
in hexadecimal, such as `0x80000000` or `0x80000000#32`
([LiteralDisplay](../CIL/LiteralDisplay.lean)), and smaller ones in decimal. The failures are:
- `cannot step pc N (op) at memory M` shows the step and what is left of it after the step
  equations and gathered facts, and names the fact that residual lacks: a span's validity, a
  slice, an element's address, an `Unsafe.Add` result, a `form` fact, a load's value, or a
  `LoopFrame` or store equation;
- `pc N is a call (op); cross it with cil_loop_call` stops `cil_loop_steps` and `cil_loop_finish`
  at a call;
- `target state not matched at pc N` names the frame, stack or memory that differs when the path
  reaches the target's pc in another state, in the reached form and the target's;
- an undecided pc asks for a fact deciding the branch condition.

### Write bit-vector literals in simp-normal form

Write the literals of a bit-vector hypothesis passed to default `simp` in simp-normal form:
`0#32`, `1#64` or `0x80000000#32`. Use the same form in definitions that the proof unfolds.
Default `simp` normalizes ordinary numerals in the goal, so a supplied hypothesis written as
`value ≠ 0` can fail to match `value ≠ 0#32`:

```lean
import CIL

example (value : CIL.W32) (nonzero : value ≠ 0#32) : value ≠ 0#32 := by
  simp [nonzero]
```

[CopyUntilZero](../Examples/Proofs/CopyUntilZero.lean) uses this form in its list predicate and
branch hypotheses. Natural-number lengths, offsets and fuel remain ordinary numerals. For a
hypothesis that uses an ordinary numeral, pass its canonical restatement:

```lean
import CIL

example (value : CIL.W32) (nonzero : value ≠ 0) : value ≠ 0#32 := by
  simp [show value ≠ 0#32 from nonzero]
```

### Compose a helper call inside a loop

A loop body that calls a helper composes through the helper's `MethodContract`
([LoopContract](../CIL/Safety/LoopContract.lean)). A contract's existential fuel cannot supply the
one cost `LoopSegment` fixes for every continuation budget, so `loop_terminates_induction` asks
each iteration for `LoopTerminates` at its own state while assuming it at every invariant state of
smaller measure.

| Rule | Use |
| --- | --- |
| [`invoke_loop_induction`](../CIL/Safety/LoopContract.lean) | Joins `loop_terminates_induction` with frame entry. From the lookup, checked arguments, `setup`, the configuration, invariant and measure, it leaves two goals: the entry state terminates given that every invariant head state does, and the iteration. Its result is the `∃ fuel final, invoke ... = .ok (final, values) ∧ kept final` of `invoke_loop_results` |
| [`invoke_loop_satisfies`](../CIL/Safety/LoopContract.lean) | Takes the same arguments for any postcondition on the final memory and results, so it closes a `CIL.Safety.Ensures` goal once its premises are introduced; the outlines `leancil new-proof` writes start from it |
| [`loop_terminates_then`](../CIL/Safety/LoopContract.lean) | Enters a later loop in sequence: given that loop's configuration, invariant and measure, it leaves the path to that loop's first head, which may assume every invariant head of it terminates, and that loop's iteration |
| `loop_terminates_call_formed` | Gives the continuation, after the call's `CallResult`, its `FrameInvariants` (`formed`, `staticWorld` and `classes`) when a proof composes the call by hand |

The tactics of [LoopFrameSteps](../CIL/Safety/LoopFrameSteps.lean), which
`CIL.Safety.LoopScaffold` imports, walk these goals while keeping the loop's `LoopFrame` current.
All gather facts as the other loop tactics do, so their lists are optional:

- `cil_loop_advance [facts]` steps to a call or return and `cil_loop_finish [facts]` through a
  return to its postcondition. Each takes a struct zeroing, field store or numeric local store on
  the way as `cil_loop_recurse` does and fails as `cil_loop_steps` does on anything else. At the
  return `cil_loop_finish` names what leaving the frame keeps, `exitConfined` and `exitBelow`
  (`LoopFrame.leave`), carries the caller-buffer facts to the exit memory, and closes each
  conjunct of the postcondition that a hypothesis, a carried `Filled` fact's contents or the
  facts prove; the rest are left as goals, tagged by their place among the conjuncts (see
  [obligation tags](#obligation-tags)), with those facts in context.
- `cil_loop_call holds input at site [facts]` applies the contract (`loop_terminates_call`) at
  the `bind_call` site or, without `at site`, at the fetched call. It leaves the precondition,
  tagged `precondition.<callee>`, unless `trivial` or a hypothesis proves it, then continues with
  these names in context: the returned memory `called`, the typed output `output` and, from the
  call's `CallResult`, its invocation `invoked`, footprint fact `confined` and postcondition
  `returned`, each with the contract unfolded; the callee's `WellFormed` (`calledFormed`); and
  the frame at the returned memory (`calledFrame`, through `LoopFrame.after_confined`). An output
  the postcondition states as an equation is substituted, unless `cil_loop_call keeping` keeps it
  as `output`. Caller-buffer facts cross the call: write authority always, contents when `omega`
  shows them apart from the callee's footprint. The tactic fails naming the pc and instruction
  when the goal is not at a call, the argument check and the fact it needs when the call does not
  step, the contract's arguments beside the stack when they differ, and the side condition when
  the callee's footprint is not shown inside the frame's footprint or below the caller's
  watermark by the facts or a hypothesis such as `WritableSpan.covered` for a lent span.
- `cil_loop_recurse hypothesis values [facts]` steps to the loop head of `hypothesis`, the entry
  goal's or the iteration's statement that every (smaller) invariant head state terminates. It
  takes each struct zeroing, field store and numeric local store on the way through
  `LoopFrame.zero_aggregate`, `store_field` and `store`, naming the memory each produces, and
  applies `hypothesis` at the head state with loop values `values`, the reached memory and its
  frame, through `LoopFrame.set_local` when a span, reference or object slot changed. The
  invariant and the decrease are left as goals tagged `invariant` and `measure`; a state that is
  not the head's at `values` fails, showing the reached state.

Each store names its memory, step and frame (`stored`, `storing`, `storedFrame`, `storedBelow`),
and the walk restates each `Contents`, `Filled` and `Writable` hypothesis about the stored-over
memory, or about the caller's, at the new one under the same name, so an invariant reads them at
the memory it is stated at.

[CountCalls](../Examples/Proofs/CountCalls.lean) proves a counted loop this way without unfolding
the helper or naming its fuel.

### Obligation tags

Every goal a loop or contract tactic leaves for the author carries a tag naming its purpose
([Obligations](../CIL/Safety/Obligations.lean)), so a proof selects it with `case <tag> =>` and
the infoview shows it. A tag is goal metadata: it prints nothing and does no proof work. A goal a
tactic only continues, such as the loop path after `cil_loop_advance` or the continuation after
`cil_loop_call`, keeps the tag it had.

| Tag | Obligation | Left by |
| --- | --- | --- |
| `invariant`, `invariant.part<n>` | the loop head's invariant at the reached state, or its `n`th part | `cil_loop_recurse`, `cil_loop_continue` |
| `measure` | the measure's decrease at a back edge | `cil_loop_recurse`, `cil_loop_continue` |
| `precondition.<callee>` | the callee contract's precondition | `cil_loop_call`, `cil_loop_outcome_call`, `cil_loop_outcome_raise`, `cil_contract_call`, `cil_formed_call`, `cil_certified_call`, `cil_contract_certified_call`, `cil_outcome_call`, `cil_formed_outcome_call`, `cil_outcome_raise`, `cil_contract_steps`, `cil_contract_construct` |
| `wellFormed` | the caller memory's `WellFormed` | `cil_formed_call`, `cil_formed_outcome_call`, `cil_contract_certified_call`, `cil_contract_construct` |
| `staticWorld` | the caller memory's static world | `cil_contract_certified_call` |
| `raises` | the callee's `raises` equation | `cil_loop_outcome_call`, `cil_loop_outcome_raise`, `cil_outcome_call`, `cil_formed_outcome_call`, `cil_outcome_raise` |
| `postcondition`, `postcondition.part<n>` | the postcondition at a return, or its `n`th conjunct | `cil_loop_finish`, `cil_contract_steps` |

Tag naming rules:

- The callee part of a precondition tag is the last component of the callee's constant, such as
  `precondition.stamp` for a `bind_callee stamp`; a callee given as a literal index leaves the
  bare `precondition`. `case precondition` selects either, since `case` also matches a tag's
  prefix.
- `cil_loop_finish` numbers the conjuncts it leaves by their place among all the postcondition's
  conjuncts, `postcondition.part2` for the second, so a conjunct keeps its tag whichever others
  the exit facts close, and `case postcondition` selects the first left. A postcondition that is
  not a conjunction is left as `postcondition`.
- A loop head hypothesis with one condition leaves `invariant`, as the entry hypothesis of
  `invoke_loop_induction` does. One with more leaves its last, the back edge's decrease, as
  `measure`, and the others as the invariant's parts: `invariant` for one, as in the iteration
  hypothesis, and `invariant.part1`, `invariant.part2`, ... for several.
- A mistyped tag is Lean's `Case tag ... not found` error, which lists the tags of the open
  goals. A loop tactic handed a tagged obligation instead of a loop path says which obligation
  the main goal is and how to select it.

The tag names and their numbering are fixed:

```lean
import CIL.Safety.Obligations

open CIL.Safety

example : obligationTags =
    [`invariant, `measure, `precondition, `wellFormed, `staticWorld, `raises, `postcondition] :=
  rfl
#guard obligationOf? `postcondition.part2 == some `postcondition
#guard numberedTags `postcondition 2 == #[`postcondition.part1, `postcondition.part2]
#guard recurseConditionTags 3 == #[`invariant.part1, `invariant.part2, `measure]
#guard obligationOf? `precondition.stamp == some `precondition
#guard obligationOf? `refine_2 == none
```

The iteration of [TallyTwice](../Examples/Proofs/TallyTwice.lean) crosses the call and closes
both recursion obligations by name:

```lean excerpt Examples/Proofs/TallyTwice.lean
cil_loop_call addTwo_holds sum at addTwoSite
cil_loop_recurse recurse (count + 1, sum + 2)
case invariant =>
  show sum + 2 = 2 * (count + 1)
  rw [doubled]
  bv_omega
case measure =>
  show (value - (count + 1)).toNat < (value - count).toNat
  bv_omega
```

### Compose a helper that can raise

A loop whose helper has an `OutcomeContract` composes both of its outcomes
([LoopOutcome](../CIL/Safety/LoopOutcome.lean)). `LoopOutcome post raises state` is `LoopTerminates
post state` when `raises` is `none` (`loop_outcome_none`) and `RunRaises` of exactly that exception
otherwise (`loop_outcome_some`), so the proof fixes which outcome the loop reaches before stepping
it, typically as a function of the inputs that the invariant ties to each head state.
`loop_outcome_induction` mirrors `loop_terminates_induction`: only a continuing iteration needs an
invariant state of smaller measure.

| Step | Use |
| --- | --- |
| Walk the path | `cil_loop_outcome_advance [facts]` |
| Continue past a callee whose contract returns | `cil_loop_outcome_call holds input at site [facts]` (`loop_outcome_call`, or `loop_outcome_call_formed`), which leaves the precondition, the `raises` equation and the continuation in either outcome |
| Exit by the callee's exception, once `raises` is rewritten to it | `cil_loop_outcome_raise holds input at site [facts]` (`loop_outcome_call_raises`); this exit has no invariant or measure obligation |
| Exit at the loop's own `throw` | `loop_outcome_throw` |
| Compose paths in either outcome | `loop_outcome_next`, `loop_reaches_outcome` |
| Lift the head outcome through frame setup | `ensures_outcome_of_loop`, to `EnsuresOutcome pre post raises`, which names the outcome of every permitted input; with `raises` constantly `none` it is `Ensures` (`ensures_outcome_none`) |
| Refute an expected exception | `loop_outcome_some_refuted`, from any settled run that does not throw it |

The normal-only rules are the `none` instances of the outcome rules. Unsupported execution,
invalid state and fuel exhaustion never satisfy an expected loop exception.
[CountUntil](../Examples/Proofs/CountUntil.lean) propagates its helper's exception after earlier
successful calls.

### Loop verification conditions

[`invoke_loop_vc`](../CIL/Safety/LoopVC.lean) proves a method's `invoke` from its lookup, checked
arguments, frame-setup equation, a loop configuration, invariant and measure, the first loop state,
a checked path to it and the invariant there. The one remaining goal is the progress rule of
`loop_terminates`: each invariant state exits through a path satisfying the postcondition, or
reaches a next state that keeps the invariant with a smaller measure.
[`invoke_loop_returns`](../CIL/Safety/LoopVC.lean) states the result as `∃ fuel, invoke ... =
.ok (final, values)` and [`invoke_loop_results`](../CIL/Safety/LoopVC.lean) as `∃ fuel final,
invoke ... = .ok (final, values) ∧ kept final`, so `refine` against a theorem of that shape fixes
the postcondition. Inside the progress goal, `cil_loop_continue next [facts]` checks the path with
`cil_loop_steps`, infers its cost and leaves only invariant preservation and strict measure
decrease, and `cil_loop_finish [facts]` proves an exit.

[`gatherLoopFacts`](../CIL/Safety/LoopFacts.lean) selects context hypotheses by the head of their
type, so an unrelated context adds nothing to simp. It gathers:

- the declarations in scope with the `cil_loop_unfold` simp attribute, which `bind_cutpoint`
  gives its state and `bind_entry` its frame and normalized result and memory;
- equations, possibly quantified or conjoined, about `step`, `instruction`, `memoryInstruction`,
  `staticInstruction`, `loadLocal`, `storeLocal`, `loadValue`, `storeValue`, `form`, `add` and
  the span `element`, `slice`, `validate`, `width` and `writable` checks;
- for a [`CheckedSpan`](../CIL/Safety/SpanContents.lean), its `facts`, `length_nil` or
  `length_cons` when its values are `[]` or a cons, and, for each `LoopFrame` from its memory
  with that memory's `WellFormed` in context, its validity, width and mode in the frame's memory
  ([`CheckedSpan.valid_within`](../CIL/Safety/LoopCallerFacts.lean));
- for a `form`, `add` or span `validate`, `element` or `slice` equation at the caller's memory of
  a `LoopFrame` with that memory's `WellFormed`, the equation at the frame's memory
  (`LoopFrame.caller_form` and its kind), and for an `add` result or an `access` check, the
  `form` fact of the reference it gives. These, and the facts of a span only a kept equation
  such as a slice produces, are read only by instructions that use a reference or span, so a
  step over scalars and locals does not carry them;
- the [object evidence](#facts-read-from-the-context) the straight-line tactics read, at a memory
  a state of the goal holds;
- `elementWidth` of a `SpanContents`;
- for a [`LoopFrame`](../CIL/Safety/LoopFrames.lean) over `knownLocals` of a list, and for the
  entry frame `bind_entry ... allocating` proves for every footprint, the `form` of each home
  (`LoopFrame.form_home`), so `ldloca` steps, and the load of each remembered home through
  `LoopFrame.load`, with `localResult`;
- for a struct local remembered as `.aggregate (layout.encode fields)`, the read of each field by
  value (`ldloc` then `ldfld`, [`step_fieldAt_encode`](../CIL/Safety/FieldValues.lean)) and by
  address (`LoopFrame.load_field`), as that field's value;
- [`LoopFrame.leave_kept`](../CIL/Safety/LoopFrames.lean) of each `LoopFrame []` with the entry's
  `setup` equation, when the goal is an exit;
- `numericOfWidth` and `BitVec.ofNat_toNat` when a gathered fact loads at a literal width.

Only hypotheses reachable by name are read: a shadowed state of an earlier iteration and
hygienic hypotheses are skipped. A fact is kept only when stepping can meet every variable it is
about. [`loopGoalScope`](../CIL/Safety/LoopFacts.lean) starts from the goal's states and
postcondition, and from the method arguments only when the program reads one with `.arg`; the
right side of each kept equation then extends it. A derived fact must be about variables reached
without an equation. A fact about a memory that no state of the goal holds and no kept equation
produces, such as the caller's memory once the frame has stored, is dropped; a frame fact at a
memory that a kept store or call produces is kept, and so are the caller facts that frame
carries, such as a span's validity, so a span local loads after a word local's store. Derived
facts are added as hygienic hypotheses, and a statement already gathered is not added again.
`SpanSum` names no fact but its invariant equation.

Each instruction is given only the facts it can read: home forms reach only `ldloca`, field reads
only `ldfld`, and the negative sides of case splits only instructions that test or compute on
data, while `ret` reads them all.

A loop over symbolic caller memory keeps the frame part of its state as the
[`LoopFrame`](../CIL/Safety/LoopFrames.lean) that `bind_entry ... allocating` returns, in a
`FrameState`; [frame facts](PROOFS-BUFFERS.md#carry-frame-facts-through-a-loop) describes its
lemmas. `frame.store index value rfl` stores into a home and gives the step's store equation and
the frame after the store, without composing `MemoryBelow` by hand. Its remembered locals are a
literal list, as after the loop tactics' stores, so either frame feeds the next step. The loop
tactics derive `LoopFrame.load` and, for any exited frame with the entry's owned identities,
`LoopFrame.leave_kept` from the state's frame. [SpanSum](../Examples/Proofs/SpanSum.lean) stores
through its frame this way, and its loop steps name no frame or span fact;
[Countdown](../Examples/Proofs/Countdown.lean) leaves its stores to `cil_loop_recurse`.

## See what the tactics did

The [`observer`](../CIL/Observe.lean) linter of `CIL.Observe` reads each declaration's
elaborated proof after it is checked and reports on it. No tactic runs any of its code, so
importing it does not change how a proof elaborates. Import it and set an option:

| Option | Reports |
| --- | --- |
| `trace.CIL.step` | Each step the proof takes |
| `set_option cil.diagnostics true` | A failure record for each error a `cil_` tactic raised and each goal one left unsolved |
| `set_option cil.goals true` | The goal at each `sorry`, failing tactic and unsolved goal |

A traced step is any application of a lemma to a `step ... = ...` premise, whichever tactic or
hand-written term took it, so `cil_loop_steps`, `cil_checked_steps`, `cil_contract_steps`, the
outcome and return tactics and `run_next` by hand are all traced. Each step message gives the pc
and instruction, the source line from `ExtractedSymbols` when the proof imports it, the lemma
applied and the one that proved its step, each hypothesis the step's proof used, and the parts of
the state that changed. A hypothesis whose statement is a `SpanApart`, `Writable`, `Filled` or
`CheckedSpan` fact also says what it establishes, such as that the footprints are disjoint. Each
`cil_` tactic the proof names then logs how many steps it took and the obligation tags of the
goals it left; a step no such tactic took is logged at its tactic block as taken outside one. A
block whose goal states a run of a method but whose proof applies no step lemma, such as one that
evaluates the method with `rfl` or `decide`, logs that it took no step to trace.

Each failure record is a message starting `[LeanCIL failure v1] `, followed by a
JSON object of the method, pc and instruction reached, the reached and expected state, the kind
of fact the step lacks, the obligation the tactic was handed and the position of the error it
explains, each unknown field with its reason. The kind is the one the loop tactics name in their
errors, read by [`missingFactOf`](../CIL/Safety/MissingFacts.lean) from the step rewritten as far
as the step equations and the result facts in scope go; a stuck step on a class instance lacks
`objectForm`, `objectSlot` or `objectAllocation`. A stepping goal under the existentials of a
contract's run, as `cil_contract_steps` leaves one at a call, is read as the run it states. The
error itself is unchanged.

With `cil.goals`, the observer logs the goal at each `sorry` written in the source, as a term or a
tactic, the goal before each tactic that raised an error and each goal of an `unsolved goals`
error, once each and in source order, as a message starting `[LeanCIL goal v1] ` and `sorry`,
`error` or `unsolved`, followed by the goal as Lean prints it.

`leancil verify --trace`, `--goals` and `--format json` add the import to the start of the
proof's first import line, which moves no other line or column, set these options and report the
steps, goals and records apart from the proof's messages.

## Read control flow off one step

`CIL.Safety.StepFlow` says where a successful `step` can go without unfolding it.
`step_next_target` proves that an action that stays in the frame resumes at `pc + 1` of a
continuing instruction or at one of `op.targets`. Given a successful action and its selected
callee, `step_callee` proves membership in `Op.callees`: a singleton for a direct call or
construction, or all authenticated targets for an indirect call. Tail transfers enter a callee
without continuing in the current frame. `step_call_action` and `step_newVector256_action` /
`step_newAggregate_action` separate a call from a construction. The module imports only the step
simulation, so a consumer reasoning about reachable pcs does not compile the import and linking
layers.

## Keep proof work local

Prefer a small `change` or an instruction equation over repeatedly unfolding `run`,
`CIL.Safety.step` and `CIL.step`. For generic opcode proofs, split the opcode and stack shape before
splitting operand constructors, and close definitionally equal cases early. Share the remaining
family-level reasoning. For concrete execution, compose steps first and simplify the resulting value
equation separately when needed.

To compare the cost of two versions of a proof, measure each with fresh Lean processes and
prebuilt dependencies, alternating the runs serially on the same machine. Record elapsed time, CPU
time, `.olean` bytes, peak process memory and kernel replay separately. A smaller artifact can
require expensive elaboration or cause callers to repeat work; peak memory also includes imported
environments. Keep kernel replay and the axiom audit enabled.
