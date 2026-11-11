# Writing checked proofs

This entry page for writing a Lean proof about extracted .NET code with the `CIL` library gives
the workflow, then tables that map a task or a goal shape to the interface, tactic and guide to
use. The detail is in [stepping](PROOFS-STEPPING.md), [contracts](PROOFS-CONTRACTS.md),
[binding](PROOFS-BINDING.md) and [buffers](PROOFS-BUFFERS.md).

State the property independently of the emitted instructions, with explicit input quantifiers,
initial-memory assumptions and permitted writes. Use `CIL.Safety.invoke`, `WP`, `Ensures`,
`MethodContract` or `OutcomeContract` when the claim includes checked execution.

## Author workflow

1. State the specification over every input and memory the contract allows. A check of a few
   concrete calls does not prove a claim about all inputs.
2. Extract the assembly and bind the proof's method body to the generated program with the
   [body-binding API](PROOFS-BINDING.md#bind-bodies-to-the-extraction). A theorem about a
   handwritten instruction list alone does not establish an assembly property.
3. Step straight-line code with `cil_checked_steps`. Supply facts for symbolic branches and
   memory operations whose conditions are not definitionally true. The
   [worked instruction example](PROOFS-STEPPING.md#compose-instructions) is a complete theorem
   over symbolic inputs and arbitrary caller memory.
4. Apply a helper's proved contract at each call site
   ([call contracts](PROOFS-CONTRACTS.md#compose-calls-through-contracts)). For a loop, state an
   invariant at its checked cutpoint and a measure that decreases on every continuing iteration
   ([loop cutpoints](PROOFS-BINDING.md#loop-heads-and-call-sites)); a finite successful sample
   does not establish termination for arbitrary input.
5. End each theorem with `#print axioms`, then run `leancil verify` on the extracted artifact
   with `--proof`. Verification checks the extraction binding and replays the compiled proof;
   elaboration alone is insufficient.

The [addition walkthrough](GETTING-STARTED.md) shows the extraction, proof and verification
commands. [Soundness](SOUNDNESS.md) states the trust boundary.

## Choose a proof interface

Select the smallest interface that expresses the result.

| Task | Guide | Executable example |
| --- | --- | --- |
| Execute a short method symbolically | [Instruction composition](PROOFS-STEPPING.md#compose-instructions) | [Add](../Examples/Proofs/Add.lean) |
| Carry existing theorems about a Lean model to compiled code | [Model proofs](../skills/leancil/references/bridge-model-proof.md) | [AddModel](../Examples/Proofs/AddModel.lean) |
| Call a helper through its proved contract | [Contract composition](PROOFS-CONTRACTS.md#compose-calls-through-contracts) | [CountCalls](../Examples/Proofs/CountCalls.lean) |
| Step through numeric local stores and loads over symbolic memory | [Snapshot walks](PROOFS-CONTRACTS.md#walk-local-stores-and-loads-with-snapshots) | The guide's reference tables |
| Pass byref buffers that may overlap | [ValidCall](PROOFS-CONTRACTS.md#pass-byref-arguments-with-validcall) | The guide's reference tables |
| Prove a loop terminates | [Loop examples](EXAMPLES.md) and [loop cutpoints](PROOFS-BINDING.md#loop-heads-and-call-sites) | [Countdown](../Examples/Proofs/Countdown.lean) |
| Store and load struct fields through a layout | [Struct field views](PROOFS-BUFFERS.md#view-struct-fields) | [Struct](../Examples/Proofs/Struct.lean) |
| Name class fields in contracts and frame them across calls | [Class instances](PROOFS-CONTRACTS.md#frame-class-instances) | [DepositBoth](../Examples/Proofs/DepositBoth.lean) |
| Walk a linked list to null in a loop | [Class instances](PROOFS-CONTRACTS.md#frame-class-instances) | [PoolIdle](../Examples/Proofs/PoolIdle.lean) |
| Describe what a span or array holds | [Span contents](PROOFS-BUFFERS.md#describe-span-contents) | [SpanSum](../Examples/Proofs/SpanSum.lean) |
| Establish buffer contents and preserve neighbours | [Buffer predicates](PROOFS-BUFFERS.md#describe-buffer-contents) | [FillWords](../Examples/Proofs/FillWords.lean) |
| Keep frame facts out of a loop invariant | [Loop frames](PROOFS-BUFFERS.md#carry-frame-facts-through-a-loop) | [FillWords](../Examples/Proofs/FillWords.lean) |
| Construct a struct through its constructor's contract | [Struct construction](PROOFS-CONTRACTS.md#construct-structs-through-contracts) | The guide's checked `pair_constructs` snippet |
| Specify normal and exceptional outcomes | [Outcome contracts](PROOFS-CONTRACTS.md#name-exceptional-outcomes) | [CountUntil](../Examples/Proofs/CountUntil.lean) |
| Publish a smaller public guarantee | [Contract consequence](PROOFS-CONTRACTS.md#derive-public-contracts) | The guide's checked `increment_refines` snippet |
| Give a forwarding wrapper its callee's contract | [Forwarders](PROOFS-CONTRACTS.md#inherit-a-callees-contract-in-a-forwarder) | The guide's forwarding snippet |
| Bind or transport a proof to extracted code | [Binding and transport](PROOFS-BINDING.md) | [CountCalls](../Examples/Proofs/CountCalls.lean) |
| Prove one body for several hardware profiles | [Profile templates](PROOFS-BINDING.md#generated-profile-templates) and [reprofiling](PROOFS-CONTRACTS.md#carry-a-contract-across-profiles) | The guides' commands and manifest |
| Select the goals a tactic leaves by purpose | [Obligation tags](PROOFS-STEPPING.md#obligation-tags) | [TallyTwice](../Examples/Proofs/TallyTwice.lean) |
| Import a separately proved interface | [Imported contracts](PROOFS-CONTRACTS.md#compose-through-imported-contracts) | [Interface guide](CONTRACT-INTERFACES.md) |
| Find why a tactic stopped | [Observer](PROOFS-STEPPING.md#see-what-the-tactics-did) | `leancil verify --trace` |

## Choose a tactic

`[facts]` is a list of proved facts the steps depend on. `holds` is a proved contract, `input` its
input and `site` a `bind_call` name.

| Goal or situation | Tactic | Guide |
| --- | --- | --- |
| `invoke` or `run` equals a result or a located fault | `cil_checked_steps [facts]` | [Stepping](PROOFS-STEPPING.md#choose-a-stepping-tactic) |
| The same, but stop after exactly `n` steps | `cil_checked_steps n [facts]` | [Stepping](PROOFS-STEPPING.md#choose-a-stepping-tactic) |
| `WP` or `∃ fuel` success, with calls through contracts | `cil_contract_steps [facts]`, with `n` or `until continuation` to stop early | [Contract stepping](PROOFS-CONTRACTS.md#step-a-caller-through-its-callees) |
| The path stores or loads numeric locals in symbolic memory | `cil_contract_steps (snapshots := snapshots) [facts]`, `cil_checked_steps (snapshots := snapshots) [facts]` | [Snapshot walks](PROOFS-CONTRACTS.md#walk-local-stores-and-loads-with-snapshots) |
| Apply one contract at a call and keep its precondition as a goal | `cil_contract_call holds input at site [facts]`; `cil_formed_call` to also receive `FrameInvariants` | [One call](PROOFS-CONTRACTS.md#apply-a-contract-at-one-call) |
| Keep the callee's `InvocationCertificate` | `cil_certified_call`, `cil_contract_certified_call` | [One call](PROOFS-CONTRACTS.md#apply-a-contract-at-one-call) |
| A `newobj` of a struct with a constructor contract | `cil_contract_construct holds constructs input [facts]` | [Struct construction](PROOFS-CONTRACTS.md#construct-structs-through-contracts) |
| A `Raises` goal | `cil_raise_steps [facts]` | [Outcomes](PROOFS-CONTRACTS.md#name-exceptional-outcomes) |
| A call whose callee has an `OutcomeContract` | `cil_outcome_call`, `cil_formed_outcome_call`, `cil_outcome_raise` | [Outcomes](PROOFS-CONTRACTS.md#name-exceptional-outcomes) |
| A loop path to the next head | `cil_loop_recurse hypothesis values [facts]` | [Loops](PROOFS-STEPPING.md#compose-a-helper-call-inside-a-loop) |
| A loop path to a call or return | `cil_loop_advance [facts]` | [Loops](PROOFS-STEPPING.md#compose-a-helper-call-inside-a-loop) |
| A call inside a loop | `cil_loop_call holds input at site [facts]` | [Loops](PROOFS-STEPPING.md#compose-a-helper-call-inside-a-loop) |
| A loop exit and its postcondition | `cil_loop_finish [facts]` | [Loops](PROOFS-STEPPING.md#step-loops) |
| The progress goal of a loop verification condition | `cil_loop_continue next [facts]`, `cil_loop_finish [facts]` | [Loop VCs](PROOFS-STEPPING.md#loop-verification-conditions) |
| A loop whose helper can raise | `cil_loop_outcome_advance`, `cil_loop_outcome_call`, `cil_loop_outcome_raise` | [Raising helpers](PROOFS-STEPPING.md#compose-a-helper-that-can-raise) |
| An element write's authority, bound and footprint membership | `cil_loop_obligation [defs]` | [Caller facts](PROOFS-BUFFERS.md#caller-facts-in-frame-memory) |
| A `Segment` boundary | `cil_segment n [facts]`, `cil_segment_steps [facts]` | [Segments](PROOFS-STEPPING.md#place-code-and-compose-segments) |
| A method or instruction lookup | `cil_lookup [facts]` | [Lookups](PROOFS-STEPPING.md#lookups) |
| `Extracted.program[i]? = some body` | `cil_body` | [Body binding](PROOFS-BINDING.md#bind-bodies-to-the-extraction) |
| The same when a profile inserts dead code or dead locals | `cil_embed` | [Dead code](PROOFS-BINDING.md#bodies-modulo-dead-code) |

Commands that name parts of an extraction:

| Name | Command | Guide |
| --- | --- | --- |
| A method by signature | `bind_method` | [Methods by signature](PROOFS-BINDING.md#methods-by-signature) |
| A callee of a bound method | `bind_callee` | [Methods by signature](PROOFS-BINDING.md#methods-by-signature) |
| A call site or loop head | `bind_call`, `bind_loop` | [Loop heads and call sites](PROOFS-BINDING.md#loop-heads-and-call-sites) |
| An imported method's slot | `bind_import` | [Imported contracts](PROOFS-CONTRACTS.md#compose-through-imported-contracts) |
| A checked frame entry and a loop cutpoint | `bind_entry`, `bind_cutpoint` | [Loop scaffolding](PROOFS-BINDING.md#generate-loop-entry-and-cutpoint-scaffolding) |
| A local by its C# name | `local_named sum "carry"` | [PDB names](PROOFS-BINDING.md#pdb-local-names-and-source-locations) |
| Per-pc instruction equations of a parametric body | `cil_instruction_equations` | [Instruction equations](PROOFS-BINDING.md#instruction-equations-for-parametric-bodies) |

## Public proof surface

`import CIL` is the supported import for a consumer proof and exports the interfaces below. It
also imports embedding and renaming metatheory; there is no narrower proof facade and no
import-closure size guarantee. Import these separately when a proof uses them:
`CIL.Safety.LoopScaffold` (`bind_entry`, `bind_cutpoint`), `CIL.Observe` and
`CIL.Safety.AllocationRefinement`.

| Purpose | Consumer interfaces |
| --- | --- |
| State checked execution | `step`, `run`, `invoke`, `Execution`, `WP`, `Ensures` |
| Compose instruction and segment proofs | `cil_checked_step`, `cil_checked_steps`, `CodeAt`, `Segment`, `Segment.trans`, `cil_segment` |
| Use a proved helper | `MethodContract`, `CallResult`, `FrameInvariants`, `run_call_of_contract_formed`, `cil_contract_steps` |
| Describe byref arguments and overlap | `ArgumentView`, `ValidCall`, the `CallingFields` lemmas |
| Preserve mixed local contents | `LocalSnapshots`, `LoopFrame`, `LoopFrame.after_local_write` |
| Prove checked loop paths | `LoopReaches`, `LoopSpec`, `cil_loop_steps` |
| Supply symbolic operation evidence | Checked read, write and snapshot equalities, vector operation equalities |

Select call evidence by field name: `result.post` and `result.framed` from `CallResult`,
`preserved.formed` from `FrameInvariants`, and `call.wellFormed`, `call.readable` and
`call.writable` from a `ValidCall`. Do not destructure preservation records positionally, so
that an additional preservation fact does not require rewriting the continuation.

`WP` relates a finite budget to one result. Use `Execution` for successful interpreter returns
and `WP.adequate` at the raw `invoke` boundary. Exact segment relations retain all continuation
budgets and faults; their budget is chosen before the continuation budget. The
[composition guide](PROOFS-STEPPING.md) describes these forms and their structural rules.

Post-step expressions are part of this proof interface:

- A vector operation with a literal control stays directly rewritable by a theorem stated with
  that literal.
- A computed segment composes at its stated stack and memory boundary.
- Intrinsic Boolean results expose their scalar constructor for checked returns while retaining
  the symbolic condition.
- Aggregate snapshot maps retain their composition for post-step rewriting.
- Supplied checked arithmetic and conversion results avoid expanding the corresponding range
  checks.

The `core` [suite](VALIDATION.md#suites) checks these forms. A change to one of them is a change
to the documented interface.

Interpreter dispatch helpers and their unfolding equations are implementation details. Do not
name them in a `simp` list; step with `cil_checked_steps` and pass a fact about the operation
instead. The [documentation checks](CI.md#documentation-checks) reject them in examples and
checked documentation.

## Keep proof work local

- Reuse the checked stepping, memory readback and contract composition lemmas. Do not unfold a
  helper body when its contract suffices.
- [Stepping and reduction](PROOFS-STEPPING.md) is a reference for reduction behaviour and the
  simplification interfaces. A first proof does not need it.
