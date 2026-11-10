# Instruction composition and proof reduction

Use `CIL.Safety.invoke` for specifications that include checked memory execution. State the
mathematical contract and its input/memory preconditions independently of the implementation. The
[soundness boundary](SOUNDNESS.md) describes what a successful checked execution establishes.

## Compose instructions

Import `CIL.Safety.SymbolicExecution` and mark definitions used for instruction lookup with
`@[cil_code]`. This complete example executes eight instructions on symbolic inputs and preserves
arbitrary caller memory:

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

The [proof automation regressions](VALIDATION-PROOFS.md#proof-automation) check this pattern and
symbolic branch proofs. This handwritten body demonstrates the tactic; a proof about an assembly
must bind its body to the generated program, as described in [Bind bodies to the
extraction](PROOFS-BINDING.md#bind-bodies-to-the-extraction), and pass verification.

`cil_checked_steps` composes `invoke_of_run`, `run_next`, `run_return` and `run_call_of_invoke`. It
checks method/instruction lookups and frame setup, infers intermediate states, and checks the
returned values. These lemmas are also available directly from
[StepComposition](../CIL/Safety/StepComposition.lean) and
[CallComposition](../CIL/Safety/CallComposition.lean) for manual proofs.

A goal `∃ fuel, invoke program fuel method args memory = result` is opened with
`CIL.executionBound program method` as its fuel, so a proof states none; fuel that is already a
term is left as written. `cil_checked_steps` and `cil_contract_steps` also state the goal with the
`args`, `results`, `pre`, `footprint` and `post` of each defined contract unfolded, at entry and in
each call's continuation, so a goal they step needs no `dsimp only [contract]` first. A contract
variable and `Returns` stay folded, as does a goal a proof enters by hand.

The stepping tactics read object evidence from the context, so a fact list does not repeat it. A
hypothesis is recognized by the head of its statement, also as one side of a conjunction, when the
goal names its object:

| Hypothesis | Facts read |
| --- | --- |
| `live : LiveObject memory object` | `live.formed` |
| `Readable`, `Owned` or `Holds` of a scalar field | `readable.live.formed`, `readable.located` and the unsigned load of `readable.facts`, which pushes the field's value |
| `Readable`, `Owned` or `Holds` of a reference or array field | `readable.live.formed` and `readable.located` |
| `ReferenceArray.Live`, `Readable`, `Owned` or `Holds` | `live.formed` and `live.located` |

A fact that takes a further premise is still passed: `readable.facts held targetLive` for the
load of a reference field, `readable.signedFacts` for a signed narrow load, and the equation a
store returns. So are the facts of an object the goal does not name when the tactic starts, such
as the target a reference field's load pushes on the way. A fact passed explicitly is used as
given and not read again. Each fact read is
added to the goal as a hypothesis, as the loop tactics add theirs, so it is elaborated once and
not at every step, and a goal the tactics leave shows it.

After each step the tactics evaluate the closed literal operands the state holds with the
`cil_literal` simp set: a width conversion, sign extension or `toNat` of a bit-vector numeral, and
a remainder of numerals, as a masked shift count is. The set fires on numerals only, so a symbolic
operand stays as stated, and `simp only [cil_literal]` gives a hand-written step the same form.

A goal stating a located fault, `invoke p fuel m args memory = .error ⟨m, pc, fault⟩`, enters
through `invoke_of_run_fault` and steps the same way. At the stated `pc` the tactic first tries
`run_fault`, which closes the goal when the fetched step raises exactly `fault`; other steps
continue through `run_next`. A goal already stated over `run` tries neither entry lemma, so
run-to-run goals and call continuations pay no failed unification. Pass the fact that makes the step fail, such as
`divRemBits_zero true left` for a zero divisor, with implicit widths given when its premise
cannot fix them. Goals stating a successful result never try either fault lemma. The [Math.DivRem quotient](../Examples/Proofs/MathDivRemQuotient.lean) proves its
success and both `div` faults this way.

The frame-entry and return premises (checked arguments, frame setup and checked results) close by
`rfl`, by `simp` with the supplied facts, or by also unfolding `checkedValue`, `numericValue`,
`formValue`, `checkedAt` and the `Except` bind, which the step closer unfolds too. The contract,
outcome and loop tactics share this closer, `cil_checked_side`. Pass only the facts a step needs,
such as `form memory r = .ok r` or a `loadValue` result; these definitions, and the `cil_guard`
names `observerCount`, `unspecifiedOperands`, `hasUnspecified` and `argumentCount`, need not be
listed. At a call, including `callvirt` and the constructor call of `newobj`, the tactic proves the
callee by stepping it or from an invocation fact in context, then keeps stepping the caller from
the cleaned `returned ++ rest` stack; one `cil_checked_steps` crosses any number of calls, and
`cil_checked_steps n` counts each call as one step.
Over symbolic caller memory, frame setup of a method with numeric locals is not a closed term;
`bind_entry ... allocating` supplies its setup equation and home facts instead (see [loop
scaffolding](PROOFS-BINDING.md#generate-loop-entry-and-cutpoint-scaffolding)).

At a return, the tactic leaves the equation between the computed checked result and the stated
result as a proof goal. It closes that equation automatically only when `with_reducible rfl`
succeeds after frame cleanup, list normalization and literal shift-count reduction. Cleanup also
drops the narrowing of an `if p then 1 else 0` result, and the closing `simp` drops it from a
comparison already decided to `1` or `0`, so a narrow Boolean return needs no unfolding of
`NarrowKind.extend`. A follow-up `simp [leaveFrame, NarrowKind.extend]; split <;> rfl` after such
a return fails with "no goals" and must be deleted. Other mathematical results can need a separate
`simp` or case split. The remaining goal contains the returned values, rather than an unexecuted
`run`. `cil_contract_steps` likewise leaves the return postcondition as a goal, stated of the
memory the body left when the returning frame is a literal that owns no allocation.

A run-to-run goal `run p (fuel + n) m 0 .. = run p fuel m n ..` closes with `cil_checked_steps` when
the stepped state is syntactically the target: symbolic `fuel` stops stepping there. With literal
fuel and a target equal only up to rewriting, `cil_checked_steps n [facts]` takes exactly `n` steps
and leaves the residual `run` equation. A call counts as one step: the callee runs to its return and
the residual starts at the caller's next instruction. Unlike `cil_contract_steps n`, which takes at
most `n` steps and stops silently when one fails, it errors unless all `n` steps are taken, since a
residual at the wrong pc would not match the target. `MemoryBelow.frame_round_trip` carries caller
memory across `enterFrame` and `leaveFrame` when the callee body keeps it.

The single-step helper, `cil_checked_step [facts]`, first tries each supplied step fact for the
fetched opcode: a fact whose conclusion is `step body op pc args frame stack memory = result`, given
as a hypothesis, a lemma, or an applied term such as `store value`. It is applied at
reducible-and-instances transparency, then retried with the `@[cil_code]` definitions in its type
unfolded, so a fact stated on the named body matches both a body reached through a lookup hypothesis
and the literal body that an extracted program's lookup produces. Otherwise the helper selects its
closing strategy from the opcode. Pure scalar operations try `rfl` even when facts are supplied.
Memory operations, local operations, instruction-dispatcher arms and branches use `cil_step`
equations and the supplied facts. This keeps memory results in the form named by their facts, and
resolves branch conditions before choosing the next program counter. Unknown opcode heads use the
equation path.

Intrinsic steps expose `checkedIntrinsic` and apply proved `@[cil_eval]` lemmas before unfolding the
intrinsic evaluator. Register consumer lemmas in the form `CIL.evalIntrinsic operation operands =
some result`. Nonnegative `BitVec.ofInt` literals become `BitVec.ofNat` literals so these equations
can match, so state `@[cil_eval]` lemmas with `BitVec.ofNat` operands. A supplied evaluation fact
may instead use a numeral operand, such as `.i32 27`: when one is supplied, a second pass respells
literal `BitVec.ofNat n k` operands as numerals and leaves symbolic `BitVec.ofNat n x` values
unchanged. The tactic keeps the lemma's result form. It then removes literal stack `take`, `drop`,
`reverse` and append expressions before the next step. These rewrites do not simplify consumer
arithmetic or unfold consumer value definitions.

Value-only ops also have one equation per i32/i64 operand shape, generated by `cil_value_steps` when
the library builds. Only an op with no equation falls back to unfolding the dispatcher. For a
hand-written step, use `simp only [cil_step, facts]`.

The `instruction` arms of `load64`, `store64` and `storeScalar` through a reference, `fieldAt`
and `fieldAddress` on an address, `setFieldAt` of width 1, 2, 4 or 8, `fieldAt` of width 4 or 8 on a
struct value, `asRef`, `skipInit` and `initobj` have one `@[cil_instruction_step]` equation per
operand shape in [InstructionSteps](../CIL/Safety/InstructionSteps.lean). They rewrite a step to
`loadValue`, `storeValue`, `add`, `write`, `referenceAt` or `formValue`, so state facts there
rather than passing `instruction`. When a supplied fact is about `instruction`, or names
`CIL.Safety.instruction`, the step is first tried with `instruction` folded, keeping that
abstraction; a step these equations leave open is retried the same way. The set is separate from
`cil_step`: a hand-written `simp only [cil_step, facts]` still stops at `instructionStep`. A
`.call` step has its own `cil_step` equation, so a call checks its arguments without unfolding
the dispatcher.

Each `.memory` operation has one equation per operand shape in `CIL.Safety.MemorySteps`. It rewrites
a step to the operation's own body, such as `formValue`, `loadValue`, `storeValue` or `add`, so
state facts at that level rather than passing `staticInstruction` or `memoryInstruction` to unfold.
Only the static-field operations still go through `staticInstruction`. A fact stated at the
`memoryInstruction` or `staticInstruction` level is tried before the per-shape equation when its
operation constructor matches. This preserves a supplied abstract result instead of expanding its
bytes and forcing later goals to recover the abstraction. Other simp-usable dispatch facts,
including wrapped conjunctions, retain the fallback after the per-shape equation fails. Every
attempt restores the proof state on failure; a failed step reports the per-shape goal. This
dispatch-fact handling is part of `cil_checked_step`, `cil_checked_steps` and `cil_contract_steps`
(and the loop tactics built on them) only: a hand-written memory step, or
`cil_checked_step_equations`, with such a fact must `rw [CIL.Safety.step_memory_eq]` first, and for
a `memoryInstruction` fact also unfold `CIL.Safety.staticInstruction`, or restate the fact at the
`formValue`, `loadValue`, `storeValue` or `add` level. The memory step simp set of those tactics
rewrites `referenceAt` on `.null` and `.address r`, so pointer arithmetic on a known reference needs
no extra fact, and a `referenceAt r = .ok a` fact about a symbolic `ManagedReference` applies;
through `cil_checked_step_equations` an `add`, `spanItem`, `copyBlock` or `initBlock` step needs
`CIL.Safety.referenceAt_address` passed as a fact. A `.feature f` step pushes `body.profile.evaluate
f`. For a known feature, `cil_step` reduces that expression to the profile field; a symbolic `f`
stays `body.profile.evaluate f`, so a fact about it applies as stated. `cil_step` unfolds a method
definition or literal only as far as its profile, so a fact such as `profile.avx2 = true` decides
the test. Inside `cil_checked_step`, `cil_checked_steps`, `cil_contract_steps` and the loop tactics,
a local fact, proof term or global theorem stated through `evaluate` or a method's profile
projection, including one quantified over every feature, is normalized to that form. Elsewhere,
including `simp only [cil_step, facts]` and `cil_checked_step_equations`, state the fact on the
field or first run `simp only [CIL.Safety.reduceMethodProfile, cil_feature] at h`.

### Consumer stepping regressions

The public tactics, with symbolic values and memory and no consumer-specific execution rules, handle
these cases that consumer proofs rely on:

- supplied store and load facts take priority over generic equations;
- zero, nonzero and literal branch conditions decide the next program counter;
- memory operations use their own equations;
- profile facts decide instruction lookup;
- intrinsic evaluation facts normalize the next stack;
- signed, unsigned and loaded-limb comparisons, and signed or unsigned widening in both argument
  orders, step within fixed heartbeat budgets.

The [proof automation regressions](VALIDATION-PROOFS.md#consumer-stepping-regressions) name the
proof that pins each case and its budget.

Every stepping, call and loop tactic closes lookups with `cil_lookup [facts]`: by evaluation of an
`@[cil_code]` extraction, by `rfl`, from a lookup hypothesis such as `found : program[index]? = some
(body profile)`, or by rewriting feature tests in a profile-dependent body with the facts. A proof
stated over an abstract `program` therefore steps exactly like one over `Extracted.program`.
`cil_checked_steps`, `cil_contract_steps` and `cil_raise_steps` fail when they cannot take a first
step, instead of returning the goal unchanged.

`WP execution post` states that a checked execution terminates successfully with a final memory
and returned values satisfying `post`. Import `CIL.Safety.WeakestPrecondition` for the predicate
and its structural rules. `execution` is a function from fuel to the existing checked `invoke`
or `run`; the predicate hides the fuel witness and intermediate result. `cil_contract_steps`
accepts this form directly. `MethodContract.Holds` and `LoopTerminates` use the same predicate.

`WP.step` composes a fetched checked instruction, `WP.call` composes an actual helper invocation,
and `WP.sequence` composes an exact prefix with its successful suffix. `WP.consequence` weakens
the postcondition by an implication. `WP.frame` carries a memory assertion only when its
preservation is proved for successful execution; it never infers content preservation from
read or write permission. `WP.enter` requires actual checked arguments and frame allocation,
and `WP.returned` requires frame exit and checked returned values. `WP.adequate` exposes the
underlying finite execution when an assembly certificate needs the raw interpreter equation.

A segment theorem over an abstract body states where its code sits with `CodeAt body start segment`
([CodeAt](../CIL/Safety/CodeAt.lean)) instead of `body.code = leading ++ segment ++ tail` and
`leading.length = start`. Pass `placed` directly to `cil_checked_steps [found, placed]`:
`cil_lookup` uses the placement to fetch literal offsets, including both `start + 1 + 1` and `start
+ 2`. It also finds local placement hypotheses without listing them and accepts supplied placement
expressions such as `region.append_left`. The fetched instruction must be inside the segment and
agree with its code. `append`, `middle`, `take` and `drop` move a placement between a region and its
segments, and `rfl` closes a concrete one. `Segment program method start finish pre post`
packages a checked prefix as a composable contract. Assertions take the unchanged arguments and a `SegmentState` containing the frame, stack
and memory. Each admitted input supplies an output state and a cost, with an exact `run (fuel +
cost) = run fuel` equation for every continuation fuel. `Segment.trans` composes adjacent contracts
and adds their costs; `Segment.run_exists` composes a suffix stated with `WP`. `Segment.consequence`
changes assertions by proved implications. `SegmentState.exact` describes a known state. For these
exact-state contracts, `cil_segment 3 [found, placed, facts]` proves the boundary using
`cil_checked_steps` and fails unless the complete equation closes. `cil_segment_steps [facts]`
proves a `SegmentRun` boundary directly. Neither tactic invents a memory or availability premise.

For numeric-local framing, record successful write equations in `SegmentLocalEffects`. The
destinations must occur in `segmentStores code`, read from the placed instructions.
`Segment.frameLocals` combines these effects with the initial `LocalSnapshots` and `WritableHomes`
to derive snapshots for `untouchedLocals code known`. Effects compose through `append` or `trans`;
one frame-rule application replaces separate disjoint-read proofs for all retained locals. The
numeric slot identities must remain fixed, and the frame-rule placement must belong to the running
method and end at the contract boundary. Indirect writes and calls need a proved memory effect;
absence of a direct `setLocal` is not evidence that an aliased byte-backed local keeps its value.
The [proof automation regressions](VALIDATION-PROOFS.md#proof-automation) step a placed segment and
compose vector-input stages with these rules.

For steps depending on hypotheses, use `cil_checked_steps [facts]` with the relevant proved facts.
Branches always use equations before reflexivity, so a fact can decide the next program counter
before the next lookup. A branch condition is decided from `v = 0` or `Not (v = 0)` on the condition
value, or from a literal condition, so no `CIL.truth` restatement is needed. Both straight-line and
loop-exit automation try return proofs only for fetched `.ret` instructions, including narrow
returns, so other opcodes do not incur failed return-step simplification.

For loops, import [LoopAutomation](../CIL/Safety/LoopAutomation.lean) for `cil_loop_steps [facts]`,
which composes an execution segment, and [LoopScaffold](../CIL/Safety/LoopScaffold.lean) for
`cil_loop_finish [facts]`, which proves an exit path and its postcondition. The list is optional:
both tactics add the facts
[`gatherLoopFacts`](../CIL/Safety/LoopFacts.lean) finds, described under [loop verification
conditions](#loop-verification-conditions), so the list carries only invariant equations, the
positive side of a case split and other facts of no recognized shape.
A case split's negative side, such as `¬count = value`, is gathered and decides the branch. A step equation in the context, quantified or not,
is used whenever its instruction is reached, allowing the run to continue past that instruction. The exit closes with the normalised facts, then again
after unfolding `leaveFrame` and narrow extension, so a fact about the exited frame's memory is
tried before cleanup rewrites past it. Supply an invariant and decreasing measure to the loop
termination theorem; these tactics do not infer termination. See the [countdown
proof](../Examples/Proofs/Countdown.lean).

The loop tactics step one fetched instruction at a time, simplifying the stack with the `drop`,
`take`, `reverse` and append lemmas after each step. When one cannot go on it fails instead of
leaving a goal, and the message names the pc. Every state, step and residual a message shows
writes its pc as a literal, such as `18` rather than `17 + 1`, as does a loop goal a walk hands
back. Goals print a bit-vector literal of `2 ^ 16` or more in hexadecimal, such as `0x80000000`
or `0x80000000#32` ([LiteralDisplay](../CIL/LiteralDisplay.lean)), and smaller ones in decimal:

- `cannot step pc N (op) at memory M` shows the step and what is left of it after the step
  equations and gathered facts, and names the fact that residual lacks: a span's validity, a
  slice, an element's address, an `Unsafe.Add` result, a `form` fact, a load's value, or a
  `LoopFrame` or store equation;
- `pc N is a call (op); cross it with cil_loop_call` stops `cil_loop_steps` and `cil_loop_finish`
  at a call;
- `target state not matched at pc N` names the frame, stack or memory that differs when the path
  reaches the target's pc in another state, in the reached form and the target's;
- an undecided pc asks for a fact deciding the branch condition.

When a bit-vector hypothesis will be passed to default `simp`, write its literals in
simp-normal form: `0#32`, `1#64` or `0x80000000#32`. Use the same form in definitions that
the proof unfolds. Default `simp` normalizes ordinary numerals in the goal, but a supplied
hypothesis written as `value ≠ 0` can then fail to match `value ≠ 0#32`.
For example:

```lean
import CIL

example (value : CIL.W32) (nonzero : value ≠ 0#32) : value ≠ 0#32 := by
  simp [nonzero]
```

The [copy-until-zero proof](../Examples/Proofs/CopyUntilZero.lean) uses this convention in its
list predicate and branch hypotheses, so ordinary `simp` handles the nonzero case without a
literal-normalization override. Natural-number lengths, offsets and fuel remain ordinary numerals.
For an existing hypothesis using an ordinary numeral, pass its canonical restatement:

```lean
import CIL

example (value : CIL.W32) (nonzero : value ≠ 0) : value ≠ 0#32 := by
  simp [show value ≠ 0#32 from nonzero]
```

A loop body that calls a helper composes through the helper's `MethodContract`
([LoopContract](../CIL/Safety/LoopContract.lean)). `LoopSegment` fixes one cost for every
continuation budget, which a contract's existential fuel cannot supply, so
`loop_terminates_induction` asks each iteration for `LoopTerminates` at its own state while assuming
it at every invariant state of smaller measure.
[`invoke_loop_induction`](../CIL/Safety/LoopContract.lean) joins it with frame entry. From the
lookup, checked arguments, `setup`, the configuration, invariant and measure, it leaves two
goals: the entry state terminates given that every invariant head state does, and the iteration.
Its result is the `∃ fuel final, invoke ... = .ok (final, values) ∧ kept final` of
`invoke_loop_results`.
[`invoke_loop_satisfies`](../CIL/Safety/LoopContract.lean) takes the same arguments for any
postcondition on the final memory and results, so it closes a `CIL.Safety.Ensures` goal once its
premises are introduced; the outlines `leancil new-proof` writes start from it. A later loop in
sequence is entered with [`loop_terminates_then`](../CIL/Safety/LoopContract.lean): given that
loop's configuration, invariant and measure, it leaves the path to that loop's first head, which may
assume every invariant head of it terminates, and that loop's iteration.

The tactics of [LoopFrameSteps](../CIL/Safety/LoopFrameSteps.lean), which
`CIL.Safety.LoopScaffold` imports, walk these goals while keeping the loop's `LoopFrame` current:

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
  tagged `precondition.<callee>`, unless `trivial` or a hypothesis proves it, then continues: it
  names the returned memory `called`, the typed output `output` and, read by field from the call's
  `CallResult`, its invocation `invoked`, footprint fact `confined` and postcondition `returned`,
  unfolds the contract in them, substitutes an output its postcondition states as an equation
  (unless `cil_loop_call keeping`, which keeps it as `output`), names the callee's `WellFormed`
  (`calledFormed`) and proves the frame at the
  returned memory (`calledFrame`, through `LoopFrame.after_confined`), and carries the
  caller-buffer facts across the call: write authority always, contents when `omega` shows them
  apart from the callee's footprint. It fails naming the pc and instruction when the goal is not at a call, the argument
  check and the fact it needs when the call does not step, the contract's arguments beside the
  stack when they differ, and the side condition when the callee's footprint is not shown inside
  the frame's footprint or below the caller's watermark, from the facts or a hypothesis stating it,
  such as `WritableSpan.covered` for a lent span.
- `cil_loop_recurse hypothesis values [facts]` steps to the loop head of `hypothesis`, the entry
  goal's or the iteration's statement that every (smaller) invariant head state terminates. It
  takes each struct zeroing, field store and numeric local store on the way through
  `LoopFrame.zero_aggregate`, `store_field` and `store`, naming the memory each produces, and
  applies `hypothesis` at the head state with loop values `values`, the reached memory and its
  frame, through `LoopFrame.set_local` when a span, reference or object slot changed. The
  invariant and the decrease are left as goals tagged `invariant` and `measure`; a state that is
  not the head's at `values` fails, showing the reached state.

#### Obligation tags

Every goal a loop or contract tactic leaves for the author carries a tag naming its purpose
([Obligations](../CIL/Safety/Obligations.lean)), so a proof selects it with `case <tag> =>` and
the infoview shows it. Tagging is goal metadata: it prints nothing and does no proof work. The goal a tactic only continues, such as the loop path
after `cil_loop_advance` or the continuation after `cil_loop_call`, keeps the tag it had.

| Tag | Obligation | Left by |
| --- | --- | --- |
| `invariant`, `invariant.part<n>` | the loop head's invariant at the reached state, or its `n`th part | `cil_loop_recurse`, `cil_loop_continue` |
| `measure` | the measure's decrease at a back edge | `cil_loop_recurse`, `cil_loop_continue` |
| `precondition.<callee>` | the callee contract's precondition | `cil_loop_call`, `cil_loop_outcome_call`, `cil_loop_outcome_raise`, `cil_contract_call`, `cil_formed_call`, `cil_certified_call`, `cil_contract_certified_call`, `cil_outcome_call`, `cil_formed_outcome_call`, `cil_outcome_raise`, `cil_contract_steps`, `cil_contract_construct` |
| `wellFormed` | the caller memory's `WellFormed` | `cil_formed_call`, `cil_formed_outcome_call`, `cil_contract_certified_call`, `cil_contract_construct` |
| `staticWorld` | the caller memory's static world | `cil_contract_certified_call` |
| `raises` | the callee's `raises` equation | `cil_loop_outcome_call`, `cil_loop_outcome_raise`, `cil_outcome_call`, `cil_formed_outcome_call`, `cil_outcome_raise` |
| `postcondition`, `postcondition.part<n>` | the postcondition at a return, or its `n`th conjunct | `cil_loop_finish`, `cil_contract_steps` |

The callee part of a precondition tag is the last component of the callee's constant, such as
`precondition.stamp` for a `bind_callee stamp`; a callee given as a literal index leaves the bare
`precondition`. `case precondition` selects either, since `case` also matches a tag's prefix.
`cil_loop_finish` numbers the conjuncts it leaves by their place among all the postcondition's
conjuncts, `postcondition.part2` for the second, so a conjunct keeps its tag whichever others the
exit facts close, and `case postcondition` selects the first left; a postcondition that is not a
conjunction is left as `postcondition`. A loop head hypothesis with one condition leaves
`invariant`, as the entry hypothesis of `invoke_loop_induction` does; one with more leaves its
last, the back edge's decrease, as `measure`, and the others as the invariant's parts,
`invariant` for one, as in the iteration hypothesis, and `invariant.part1`, `invariant.part2`,
... for several. A mistyped tag is Lean's `Case tag ... not found` error, which lists the tags
of the open goals. A loop tactic handed a tagged obligation instead of a loop path says
which obligation the main goal is and how to select it. The tags are the proof API:

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

The iteration of the [struct-local loop proof](../Examples/Proofs/TallyTwice.lean) crosses the
call and closes both recursion obligations by name:

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

Each store names its memory, step and frame (`stored`, `storing`, `storedFrame`,
`storedBelow`), and the walk re-states each `Contents`, `Filled` and `Writable` hypothesis about
the stored-over memory, or about the caller's, at the new one under the same name, so an
invariant reads them at the memory it is stated at. All gather facts as the other loop tactics
do, so the lists are optional.
`loop_terminates_call_formed` gives the continuation, after the call's `CallResult`, its
`FrameInvariants` (`formed`, `staticWorld` and `classes`) when a proof composes the call by hand.
The [counted-loop proof](../Examples/Proofs/CountCalls.lean) never unfolds the helper or names its
fuel; the loop suite reuses it unedited for a reimplemented helper and requires it to reject a discarded helper
result and a broken count. On the correct build, a nondecreasing measure and an invariant that holds
at entry and exit but is not preserved each fail at exactly that obligation.

A loop whose helper has an `OutcomeContract` composes both of its outcomes
([LoopOutcome](../CIL/Safety/LoopOutcome.lean)). `LoopOutcome post raises state` is `LoopTerminates
post state` when `raises` is `none` (`loop_outcome_none`) and `RunRaises` of exactly that exception
otherwise (`loop_outcome_some`), so the proof fixes which outcome the loop reaches before stepping
it, typically as a function of the inputs that the invariant ties to each head state.
`loop_outcome_induction` mirrors `loop_terminates_induction`: only a continuing iteration needs an
invariant state of smaller measure. Step with `cil_loop_outcome_advance [facts]` and continue past a
callee whose contract returns with `cil_loop_outcome_call holds input at site [facts]`
(`loop_outcome_call`, or `loop_outcome_call_formed`), which leaves the precondition, the `raises`
equation and the continuation in either outcome. Once `raises` is rewritten to the callee's
exception, exit with `cil_loop_outcome_raise holds input at site [facts]`
(`loop_outcome_call_raises`); that exit has no invariant or measure obligation. `loop_outcome_throw`
exits at the loop's own `throw`, and `loop_outcome_next` and `loop_reaches_outcome` compose paths in
either outcome. `ensures_outcome_of_loop` lifts the head outcome through frame setup to
`EnsuresOutcome pre post raises`, which names the outcome of every permitted input; with `raises`
constantly `none` it is `Ensures` (`ensures_outcome_none`). `loop_outcome_some_refuted` refutes an
expected exception from any settled run that does not throw it.

The [outcome loop proof](../Examples/Proofs/CountUntil.lean) propagates its helper's exception after
earlier successful calls. The loop suite reuses it unedited for a reimplemented helper and rejects a
helper that raises another type; on the correct build, a nondecreasing measure, a non-inductive
invariant and a wrong specified exception each fail at that obligation. The normal-only rules are
the `none` instances of the outcome rules, and unsupported execution, invalid state and fuel
exhaustion never satisfy an expected loop exception.

### Loop verification conditions

[`invoke_loop_vc`](../CIL/Safety/LoopVC.lean) proves a method's `invoke` from its lookup, checked
arguments, frame-setup equation, a loop configuration, invariant and measure, the first loop state,
a checked path to it and the invariant there. The one remaining goal is the progress rule of
`loop_terminates`: each invariant state exits through a path satisfying the postcondition, or
reaches a next state that keeps the invariant with a smaller measure.
[`invoke_loop_returns`](../CIL/Safety/LoopVC.lean) states the result as `∃ fuel, invoke ... =
.ok (final, values)` and [`invoke_loop_results`](../CIL/Safety/LoopVC.lean) as `∃ fuel final,
invoke ... = .ok (final, values) ∧ kept final`, so `refine` against a theorem of that shape fixes
the postcondition. Inside the progress goal, `cil_loop_continue next [facts]` leaves only
preservation and decrease, and `cil_loop_finish [facts]` proves an exit.

The loop tactics take their facts from the proof context as well as from the optional list.
[`gatherLoopFacts`](../CIL/Safety/LoopFacts.lean) selects hypotheses by the head of their type, so
an unrelated context adds nothing to simp:

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
- the [object evidence](#compose-instructions) the straight-line tactics read, at a memory a state
  of the goal holds;
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
carries, such as a span's validity, so a span local loads after a word local's store. Derived facts are added as hygienic
hypotheses, so the stepper looks them up by name instead of elaborating a proof term at every
step, and a statement already gathered is not added again. `SpanSum` names no fact but its
invariant equation.

The stepping tactics give each instruction only the facts it can read. Home forms reach only
`ldloca`, field reads only `ldfld`, and the negative sides of case splits only instructions that
test or compute on data, while `ret` reads them all; each group is added and normalised the first time such an
instruction is reached. Stack lemmas join the rewrite only when the goal holds a stack operation.

A loop over symbolic caller memory keeps the frame part of its state as the
[`LoopFrame`](../CIL/Safety/LoopFrames.lean) that `bind_entry ... allocating` returns, in a
`FrameState`. `frame.store index value rfl` stores into a home and gives the step's store
equation and the frame after the store, without composing `MemoryBelow` by hand. Its remembered
locals are a literal list, as after the loop tactics' stores, so either frame feeds the next step.
`LoopFrame.load` reads a home at a loop head, and `LoopFrame.leave_kept` `setup` is the exit's
`MemoryBelow` fact for a frame confined to no caller storage, for any exited frame with the
entry's owned identities, closing a postcondition such as `SpanSum`'s; the loop tactics derive
both from the state's frame. [SpanSum](../Examples/Proofs/SpanSum.lean) stores through its frame
this way, and its loop steps name no frame or span fact;
[Countdown](../Examples/Proofs/Countdown.lean) leaves its stores to `cil_loop_recurse`.

### See what the tactics did

The [`observer`](../CIL/Observe.lean) linter of `CIL.Observe` reads each declaration's
elaborated proof after it is checked and reports on it; no tactic runs any of its code, so a
proof that does not import it
elaborates exactly as before. Import it and set `trace.CIL.step` to log each step the proof
takes, whichever tactic or hand-written term took it: any application of a lemma to a
`step ... = ...` premise counts, so `cil_loop_steps`, `cil_checked_steps`, `cil_contract_steps`,
the outcome and return tactics and `run_next` by hand are all traced. Each step message gives
the pc and instruction, the source line from `ExtractedSymbols` when the proof imports it, the
lemma applied and the one that proved its step, each hypothesis the step's proof used, and the
parts of the state that changed. A hypothesis whose statement is a `SpanApart`, `Writable`,
`Filled` or `CheckedSpan` fact also says what it establishes, such as that the footprints are
disjoint. Each `cil_` tactic the proof names then logs how many steps it took and the obligation
tags of the goals it left; a step no such tactic took is logged at its tactic block as taken
outside one. A block whose goal states a run of a method but whose proof applies no step lemma,
such as one that evaluates the method with `rfl` or `decide`, logs that it took no step to trace.

With `set_option cil.diagnostics true`, the observer logs a failure record for each error a `cil_`
tactic raised, and for each goal one left that Lean reports as unsolved, as a message starting
`[LeanCIL failure v1] `: a JSON object of the method, pc and instruction reached, the reached and
expected state, the kind of fact the step lacks, the obligation the tactic was handed and the
position of the error it explains, each unknown field with its reason. The kind is the one the
loop tactics name in their errors, read by [`missingFactOf`](../CIL/Safety/MissingFacts.lean) from
the step rewritten as far as the step equations and the result facts in scope go; a stuck step on
a class instance lacks `objectForm`, `objectSlot` or `objectAllocation`. A stepping goal under the
existentials of a contract's run, as `cil_contract_steps` leaves one at a call, is read as the run
it states. The error itself is
unchanged.

With `set_option cil.goals true`, the observer logs the goal at each `sorry` written in the
source, as a term or a tactic, the goal before each tactic that raised an error and each goal of
an `unsolved goals` error, once each and in source order, as a message starting
`[LeanCIL goal v1] ` and `sorry`, `error` or `unsolved`, followed by the goal as Lean prints it.

`leancil verify --trace`, `--goals` and `--format json` add the import to the start of the
proof's first import line, which moves no other line or column, set these options and report the
steps, goals and records apart from the proof's messages.

## Read control flow off one step

`CIL.Safety.StepFlow` says where a successful `step` can go without unfolding it.
`step_next_target`: an action that stays in the frame resumes at `pc + 1` of a continuing
instruction or at one of `op.targets`. Given a successful action and its selected callee,
`step_callee` proves membership in `Op.callees`: a singleton for a direct call or construction, or
all authenticated targets for an indirect call. Tail transfers enter a callee without continuing in
the current frame. `step_call_action` and `step_newVector256_action` / `step_newAggregate_action`
separate a call from a construction. The module imports only the step simulation, so a consumer
reasoning about reachable pcs does not compile the import and linking layers.

## Keep proof work local

Prefer a small `change` or an instruction equation over repeatedly unfolding `run`,
`CIL.Safety.step` and `CIL.step`. For generic opcode proofs, split the opcode and stack shape before
splitting operand constructors, and close definitionally equal cases early. Share the remaining
family-level reasoning. For concrete execution, compose steps first and simplify the resulting value
equation separately when needed.

Measure changes with fresh Lean processes and prebuilt dependencies on both revisions. Alternate
baseline and candidate runs serially on the same machine, and include downstream consumers. Record
elapsed time, CPU time, `.olean` bytes, peak process memory and kernel replay separately. A smaller
artifact can still require expensive elaboration or cause callers to repeat work; peak memory also
includes imported environments. Keep kernel replay and the axiom audit enabled.

The [validation guide](VALIDATION-PROOFS.md#proof-automation) describes the regression coverage and
commands for checking the proof tactics.
