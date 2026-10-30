# Instruction composition and proof reduction

## Preparation and shared infrastructure

`CIL.Safety.step_return_properties` proves declared return arity and the absence of unspecified SIMD
lanes together. `step_return_length` and `step_return_known` project the two results, so the checked
dispatcher is analyzed once. Run traces preserve the declared arity across tail calls, whose callees
must have the same return arity. A tail call retires the current frame before rechecking its
arguments and entering the callee; pointers into that frame's local storage therefore cannot escape
through a tail call, even if the callee ignores them. `run_success_return_trace` and
`run_success_live_return_trace` expose the terminal method and arguments as existential witnesses:
after a tail call, the final `ret` belongs to the callee. `run_return_length` and invocation
result-validity guarantees apply to the original invocation. The return proof uses an explicit
simplification set: unrestricted `simp_all` repeatedly tries to discharge irrelevant dispatcher
exclusions. Keep that set narrow when extending the proof. The callee proof reduces each fixed
opcode before splitting the remaining dispatcher matches, avoiding repeated case analysis of
branches already excluded by that opcode. Successful binds supply their successful result directly,
so their impossible error branches are never expanded. Trailing-local proofs normalize maps over
monadic binds before trying congruence, so shared computations need not be split into their possible
results to prove the continuation unchanged. They also discharge dispatcher-tail cases before
inspecting an irrelevant second operand.

Relabeling proofs close unary and invalid-first-operand cases before inspecting a second operand.
Their local `stack_cases => ...` helper tries the instruction's proof after each operand split,
avoiding duplicate dispatcher-tail proofs for irrelevant stack shapes. The success and
named-exception statements, interpreter definitions and allowed axioms are unchanged.

Ordinary allocation-renaming instructions share the proof of `Memory.Renamed.instructionResult`.
Reference-aware subtraction, comparisons and branches share `Memory.Renamed.stepReference` and
`FixedStepFamily.reference`. These replace `stepSubtract`, `stepCompare`, `stepUnsignedBranch` and
`stepEqualityBranch`, and their four separate family constructors. `stepTransport` and its
successful/exceptional execution guarantees retain their statements. The ordinary instruction proof
normalizes mapped stack constructors with a single simplifier pass, avoiding repeated traversal of
the dispatcher. Later normalization retains full simplification. The execution-invariant dispatcher
applies contract lemmas before searching for their success hypotheses, and uses an explicit simp set
to establish scalar-stack validity. The precomputed intrinsic signature-byte table is checked
against its original strings with `decide +kernel`, avoiding expensive whole-table definitional
equality while retaining an axiom-free equality theorem.

Certificate validation streams fallthrough states and uses balanced indexes for branch destinations.
`FeatureFlowValid`, `ScalarFlowValid`, their transfer/emission checks and feature-edge predicates
take an explicit array of raw layouts. Generated certificates pass `rawLayouts.toArray`; standalone
fixtures without aggregate queries pass `#[]`. The enclosing translation certificate validates that
same layout table, binding reference-content queries to their aggregate identities.
`FeatureFlowValid_iff_list` and `ScalarFlowValid_iff_list` recover the original list-indexed rules
without changing their entry, reachability, opcode or bounds requirements. `foldEntry` takes the
optional lookup result, so a list-based caller writes `foldEntry roles[target]?`. Missing entries
retain the original permissive fold-role result; the successor-state check independently rejects a
target missing from its certificate.

Division intrinsic validation classifies each emitted intrinsic once and removes the common assembly
scope once when recognizing a raw call's family. Its signature-byte table is generated from the
existing signature strings at elaboration time; a kernel-checked equality proves the table exact
without adding axioms. `DivisionIntrinsicsValid_iff_original` proves equivalence to the original
signature lookup, malformed-family rejection, arity, reachability, profile availability and length
checks for arbitrary raw metadata, including non-ASCII identities.

Feature getter validation likewise checks the common assembly/type prefix once, then compares
literal UTF-8 suffixes. `featureGetter_eq_original` proves equality with the original lookup for
every raw call site; a separate kernel-checked equality validates the generated suffix table. Prefix
truncation, trailing bytes, non-ASCII names and call-shape mismatches remain rejected. This changes
certificate checking cost, not the admitted feature getters.

Generated managed-call certificates use `cil_managed_calls` to prove the unchanged
`ManagedCallsValid` proposition. The tactic unfolds the supplied generated definitions and proves
identical scoped types and generic arguments by reflexivity. Remaining checks use kernel decision;
unsupported proof shapes fall back to the original complete decision. The validator still checks
targets, method tokens, type arguments, exact parameter and return types, instance metadata,
reachability and argument counts. This changes proof construction; source binding, certificate
audits and kernel replay are unchanged.

Generated primitive and generic-constructor types reference `Extraction.runtimeScope` only when
their full assembly identity matches it exactly. Its materialized UTF-8 bytes are definitionally
equal to the original string, as proved by `runtimeScope_eq`. Version, culture and public-key token
remain part of the identity; all other scopes retain their literal values. This representation
avoids decoding the same string during each certificate decision.

Each distinct reachable external-call identity similarly receives one generated byte constant. Its
`Bytes_eq` theorem proves exact equality with the original full string's UTF-8 bytes by reflexivity.
The string's UTF-8 validity proof and its equality theorem reuse that checked equality; neither
introduces axioms. Repeated occurrences of an identical target, including across original and
specialized metadata, share the constant. Validators still parse and compare the full identity,
including assembly version, culture, public-key token, declaring type, method and signature.
Pruned-only calls retain literals, and call-free extractions emit no additional declarations. This
changes data representation, not scalar, division, specialization or admission rules.

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

end ProofGuide
```

The [automation regression](../Tests/Automation.lean) checks this pattern and symbolic branch
proofs. This handwritten body demonstrates the tactic; a proof about an assembly must bind its body
to the generated program, as described in in [Bind bodies to the
extraction](PROOFS-BINDING.md#bind-bodies-to-the-extraction), and pass verification.

`cil_checked_steps` composes `invoke_of_run`, `run_next`, `run_return` and `run_call_of_invoke`. It
checks method/instruction lookups and frame setup, infers intermediate states, and checks the
returned values. These lemmas are also available directly from
[StepComposition](../CIL/Safety/StepComposition.lean) and
[CallComposition](../CIL/Safety/CallComposition.lean) for manual proofs.

A goal stating a located fault, `invoke p fuel m args memory = .error ⟨m, pc, fault⟩`, enters
through `invoke_of_run_fault` and steps the same way. At the stated `pc` the tactic first tries
`run_fault`, which closes the goal when the fetched step raises exactly `fault`; other steps
continue through `run_next`. Pass the fact that makes the step fail, such as
`divRemBits_zero true left` for a zero divisor, with implicit widths given when its premise
cannot fix them. Goals stating a successful result never try either fault lemma. The [Math.DivRem quotient](../Examples/Proofs/MathDivRemQuotient.lean) proves its
success and both `div` faults this way.

The frame-entry and return premises (checked arguments, frame setup and checked results) close by
`rfl`, by `simp` with the supplied facts, or by also unfolding `checkedValue`, `numericValue`,
`formValue`, `checkedAt` and the `Except` bind, which the step closer unfolds too. The contract,
outcome and loop tactics share this closer, `cil_checked_side`. Pass only the facts a step needs,
such as `form memory r = .ok r` or a `loadValue` result; these definitions, and the `cil_guard`
names `observerCount`, `unspecifiedOperands`, `hasUnspecified` and `argumentCount`, need not be
listed. A closed call steps its caller's continuation from the cleaned `returned ++ rest` stack.
Over symbolic caller memory, frame setup of a method with numeric locals is not a closed term;
`bind_entry ... allocating` supplies its setup equation and home facts instead (see [loop
scaffolding](PROOFS-BINDING.md#generate-loop-entry-and-cutpoint-scaffolding)).

At a return, the tactic leaves the equation between the computed checked result and the stated
result as a proof goal. It closes that equation automatically only when `with_reducible rfl`
succeeds after frame cleanup, list normalization and literal shift-count reduction. Cleanup also
drops the narrowing of an `if p then 1 else 0` result, so a narrow Boolean return needs no unfolding
of `NarrowKind.extend`. A follow-up `simp [leaveFrame, NarrowKind.extend]; split <;> rfl` after such
a return fails with "no goals" and must be deleted. Other mathematical results can need a separate
`simp` or case split. The remaining goal contains the returned values, rather than an unexecuted
`run`. `cil_contract_steps` likewise leaves the return postcondition as a goal.

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

The consumer failures reported in #252 are covered by the following proofs. These use the public
tactics with symbolic values and memory; they do not replace the checked interpreter with
consumer-specific execution rules.

| Case | Regression |
| --- | --- |
| Supplied store/load facts take priority over generic equations | `Tests.Automation.step_facts_first`, `applied_step_facts_first` |
| Zero, nonzero and literal branch conditions | `Tests.Automation.branch_from_zero`, `branch_from_nonzero`, `literal_branch` |
| Memory operations use their own equations | `Tests.Automation.asRef_fact_stack`, `load128_fact_stack`, `add_fact_stack` |
| Profile facts decide instruction lookup | `Tests.Automation.feature_op_checked`, `Tests.MethodContract.feature_op_contract_steps` |
| Intrinsic evaluation facts normalize the next stack | `Tests.Automation.evaluated_then_stored`, `evaluated_by_applied_hypothesis` |
| Signed, unsigned and loaded-limb comparisons | `Tests.MethodContract.loaded_signed_branch`, `loaded_unsigned_branch`, `loaded_limb_branch` |
| Signed/unsigned widening and both argument orders | `Tests.MethodContract.ordered_widening` |

Each comparison proof has a 2,000-heartbeat budget. The widening proof handles all eight
combinations of signed conversion, scalar position and reversed arguments in 12,000 heartbeats,
using one `cil_contract_steps 3` invocation per case. Its arbitrary continuation preserves the
actual widened stack and memory, rather than merely checking that some execution exists. These
budgets detect elaboration regressions independently of machine speed; they are not wall-clock
benchmarks. `ordered_widening_returns` composes that prefix with a concrete suffix which discards
both operands and returns zero, proving that the continuation premise is satisfiable for every case.
The widened value is checked by the prefix theorem.

Every stepping, call and loop tactic closes lookups with `cil_lookup [facts]`: by evaluation of an
`@[cil_code]` extraction, by `rfl`, from a lookup hypothesis such as `found : program[index]? = some
(body profile)`, or by rewriting feature tests in a profile-dependent body with the facts. A proof
stated over an abstract `program` therefore steps exactly like one over `Extracted.program`.
`cil_checked_steps`, `cil_contract_steps` and `cil_raise_steps` fail when they cannot take a first
step, instead of returning the goal unchanged.

A segment theorem over an abstract body states where its code sits with `CodeAt body start segment`
([CodeAt](../CIL/Safety/CodeAt.lean)) instead of `body.code = leading ++ segment ++ tail` and
`leading.length = start`. Pass `placed` directly to `cil_checked_steps [found, placed]`:
`cil_lookup` uses the placement to fetch literal offsets, including both `start + 1 + 1` and `start
+ 2`. It also finds local placement hypotheses without listing them and accepts supplied placement
expressions such as `region.append_left`. The fetched instruction must be inside the segment and
agree with its code. `append`, `middle`, `take` and `drop` move a placement between a region and its
segments, and `rfl` closes a concrete one. [Tests/CodeAt](../Tests/CodeAt.lean) steps a segment this
way. `Segment program method start finish pre post` packages a checked prefix as a composable
contract. Assertions take the unchanged arguments and a `SegmentState` containing the frame, stack
and memory. Each admitted input supplies an output state and a cost, with an exact `run (fuel +
cost) = run fuel` equation for every continuation fuel. `Segment.trans` composes adjacent contracts
and adds their costs; `Segment.run_exists` applies a successful continuation. `Segment.consequence`
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
[Tests/Segment](../Tests/Segment.lean) composes the UInt256 Add Vector128 reference prefix and
Multiply AVX2 vector-input stages with these rules.

For steps depending on hypotheses, use `cil_checked_steps [facts]` with the relevant proved facts.
Branches always use equations before reflexivity, so a fact can decide the next program counter
before the next lookup. A branch condition is decided from `v = 0` or `Not (v = 0)` on the condition
value, or from a literal condition, so no `CIL.truth` restatement is needed. Both straight-line and
loop-exit automation try return proofs only for fetched `.ret` instructions, including narrow
returns, so other opcodes do not incur failed return-step simplification.

For loops, import [LoopAutomation](../CIL/Safety/LoopAutomation.lean). `cil_loop_steps [facts]`
composes an execution segment and `cil_loop_finish [facts]` proves an exit path and its
postcondition. Supply an invariant and decreasing measure to the loop termination theorem; these
tactics do not infer termination. See the [countdown proof](../Examples/Proofs/Countdown.lean).

A loop body that calls a helper composes through the helper's `MethodContract`
([LoopContract](../CIL/Safety/LoopContract.lean)). `LoopSegment` fixes one cost for every
continuation budget, which a contract's existential fuel cannot supply, so
`loop_terminates_induction` asks each iteration for `LoopTerminates` at its own state while assuming
it at every invariant state of smaller measure. Step to the call with `cil_loop_advance [facts]`,
apply the contract with `cil_loop_call holds input at site [facts]` (`loop_terminates_call`, or
`loop_terminates_call_formed` for `WellFormed` and the static world), re-establish the invariant
from `Returns` and `Confined` in the continuation, reach the next head with `cil_loop_steps`, and
close with `loop_reaches_terminates` and the assumption. The [counted-loop
proof](../Examples/Proofs/CountCalls.lean) never unfolds the helper or names its fuel; the loop
suite reuses it unedited for a reimplemented helper and requires it to reject a discarded helper
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
invariant and a wrong specified exception each fail at that obligation. `Tests/LoopOutcome.lean`
derives the normal-only rules as the `none` instances and proves that unsupported execution, invalid
state and fuel exhaustion never satisfy an expected loop exception.

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
