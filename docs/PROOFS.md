# Writing checked proofs

State the property independently of the emitted instructions. Use `CIL.Safety.invoke`,
`WP`, `Ensures`, `MethodContract` or `OutcomeContract` when the claim includes checked execution.
Make input quantifiers, initial-memory assumptions and permitted writes explicit.

## Author workflow

1. **State the specification.** Quantify over the inputs and memory allowed by the contract.
   For addition, the result must equal the sum for every pair of input words; checking a few
   concrete calls does not prove that claim.
2. **Bind the method.** Extract the assembly and bind the proof's method body to the generated
   program with the [body-binding API](PROOFS-BINDING.md#bind-bodies-to-the-extraction).
   A theorem about a handwritten instruction list alone does not establish an assembly property.
3. **Step straight-line code.** Use `cil_checked_steps` to compose checked execution steps.
   Supply facts for symbolic branches and memory operations when their conditions are not
   definitionally true. The [worked instruction example](PROOFS-STEPPING.md#compose-instructions)
   shows a complete theorem over symbolic inputs and arbitrary caller memory.
4. **Compose calls and loops.** Apply a helper's proved contract at a call site. For a loop,
   state an invariant at its checked cutpoint and a measure that decreases on every continuing
   iteration. See [call contracts](PROOFS-CONTRACTS.md#compose-calls-through-contracts) and
   [loop cutpoints](PROOFS-BINDING.md#loop-heads-and-call-sites).
5. **Verify the assembly-bound proof.** Inspect `#print axioms`, then run `leancil verify` on
   the extracted artifact with `--proof`. Verification checks the extraction binding and replays the
   compiled proof; elaboration alone is insufficient.

Follow the [addition walkthrough](GETTING-STARTED.md) for the extraction, proof and verification
commands, then select the smallest proof interface that expresses the result:

## Choose a proof interface

| Task | Guide | Executable example |
| --- | --- | --- |
| Execute a short method symbolically | [Instruction composition](PROOFS-STEPPING.md#compose-instructions) | [Add](../Examples/Proofs/Add.lean) |
| Carry existing theorems about a Lean model to compiled code | [Model proofs](../skills/leancil/references/bridge-model-proof.md) | [AddModel](../Examples/Proofs/AddModel.lean) |
| Call a helper through its proved contract | [Contract composition](PROOFS-CONTRACTS.md#compose-calls-through-contracts) | [CountCalls](../Examples/Proofs/CountCalls.lean) |
| Prove a loop terminates | [Loop examples](EXAMPLES.md) and [loop cutpoints](PROOFS-BINDING.md#loop-heads-and-call-sites) | [Countdown](../Examples/Proofs/Countdown.lean) |
| Store and load struct fields through a layout | [Struct field views](PROOFS-BUFFERS.md#view-struct-fields) | [Struct](../Examples/Proofs/Struct.lean) |
| Name class fields in contracts and frame them across calls | [Class instances](PROOFS-CONTRACTS.md#frame-class-instances) | [DepositBoth](../Examples/Proofs/DepositBoth.lean) |
| Walk a linked list to null in a loop | [Class instances](PROOFS-CONTRACTS.md#frame-class-instances) | [PoolIdle](../Examples/Proofs/PoolIdle.lean) |
| Establish buffer contents and preserve neighbours | [Buffer predicates](PROOFS-BUFFERS.md#describe-buffer-contents) | [FillWords](../Examples/Proofs/FillWords.lean) |
| Keep frame facts out of a loop invariant | [Loop frames](PROOFS-BUFFERS.md#carry-frame-facts-through-a-loop) | [FillWords](../Examples/Proofs/FillWords.lean) |
| Specify normal and exceptional outcomes | [Outcome contracts](PROOFS-CONTRACTS.md#name-exceptional-outcomes) | [CountUntil](../Examples/Proofs/CountUntil.lean) |
| Publish a smaller public guarantee | [Contract consequence](PROOFS-CONTRACTS.md#derive-public-contracts) | The guide's checked `increment_refines` snippet |
| Bind or transport a proof to extracted code | [Binding and transport](PROOFS-BINDING.md) | [CountCalls](../Examples/Proofs/CountCalls.lean) |
| Select the goals a tactic leaves by purpose | [Obligation tags](PROOFS-STEPPING.md#obligation-tags) | [TallyTwice](../Examples/Proofs/TallyTwice.lean) |
| Import a separately proved interface | [Imported contracts](PROOFS-CONTRACTS.md#compose-through-imported-contracts) | [Interface guide](CONTRACT-INTERFACES.md) |

## Public proof surface

`import CIL` is the supported umbrella for a consumer proof. It exports the interfaces below;
the guides link their definitions and worked examples. The umbrella also imports embedding and
renaming metatheory. There is no separate narrow proof facade or import-closure size guarantee.

| Purpose | Consumer interfaces |
| --- | --- |
| State checked execution | `step`, `run`, `invoke`, `Execution`, `WP`, `Ensures` |
| Compose instruction and segment proofs | `cil_checked_step`, `cil_checked_steps`, `CodeAt`, `Segment`, `Segment.trans`, `cil_segment` |
| Use a proved helper | `MethodContract`, `CallResult`, `FrameInvariants`, `run_call_of_contract_formed`, `cil_contract_steps` |
| Describe byref arguments and overlap | `ArgumentView`, `ValidCall`, the `CallingFields` lemmas |
| Preserve mixed local contents | `LocalSnapshots`, `LoopFrame`, `LoopFrame.after_local_write` |
| Prove checked loop paths | `LoopReaches`, `LoopSpec`, `cil_loop_steps` |
| Supply symbolic operation evidence | Checked read, write and snapshot equalities, vector operation equalities |

Select call evidence by field name: `result.post` and `result.framed` from `CallResult`, and
`preserved.formed` from `FrameInvariants`. Do not destructure preservation records positionally;
an additional preservation fact should not require rewriting the continuation. Similarly, use
`call.wellFormed`, `call.readable` and `call.writable` for a `ValidCall`.

`WP` relates a finite budget to one result. Use `Execution` for successful interpreter returns
and `WP.adequate` at the raw `invoke` boundary. Exact segment relations retain all continuation
budgets and faults; their budget is chosen before the continuation budget. The
[composition guide](PROOFS-STEPPING.md) describes these forms and their structural rules.

Post-step expressions are part of this proof interface. A vector operation with a literal control
must remain directly rewritable by a theorem stated with that literal; a computed segment must
compose at its stated stack and memory boundary. The `core` suite checks these forms together with
named call continuations, overlapping byrefs, mixed local snapshots and a checked loop cutpoint.
Intrinsic Boolean results expose their scalar constructor for checked returns while retaining the
symbolic condition. Aggregate snapshot maps retain their composition for post-step rewriting.
Supplied checked arithmetic and conversion results avoid expanding the corresponding range checks.
Changes to those forms require updating the documented interface and its consumer proofs together.
Interpreter dispatch helpers and their unfolding equations are implementation details. The
documentation checker rejects their direct use in the consumer fixture and their use in evaluator
simp lists in examples and checked documentation.

## Keep proof work local

Reuse checked stepping, memory readback and contract composition lemmas. Avoid unfolding helper
bodies when their contracts suffice. Loop invariants must describe the state at a checked
cutpoint, and continuing iterations must decrease an explicit measure. A finite successful
sample does not establish termination for arbitrary input.

`ValidCall memory inputs outputs` gives named `wellFormed`, `readable` and `writable` facts.
Inputs may overlap each other and the outputs arbitrarily. Outputs need write access but need
not be initialized. With `CIL.Safety.CallingFields`, the stepping tactics derive formed
references and eight-byte field reads from this evidence, including fields indexed by a finite
bound of at most 64. `input_snapshot` records current bytes; `output_slice` supplies write access
to an in-range slice. `after_write` preserves call validity, but does not preserve old input
contents when a write overlaps them. Read all needed input fields before an overlapping write,
or prove the required contents separately.

Use `MethodContract` for byref wrappers, with `ValidCall memory inputs outputs` in `pre`.
The result encoding describes returned values; `post` independently states their meaning and
the memory guarantees, while `footprint` bounds the permitted changes.

| Wrapper result | `results` encoding | Calling requirements |
| --- | --- | --- |
| Read-only scalar | `[.scalar (.i64 word)]` | Readable input views, no output views; empty footprint |
| Reporting flag | `[.scalar (.i32 (if flag then 1 else 0))]` | Readable inputs and any writable output views |
| Aggregate value | `[.scalar (.aggregate bytes)]` | Readable inputs and any writable output views |

`MethodContract.withArgs` changes only the argument encoding. `MethodContract.Holds.forward`
proves an argument-loading wrapper from the helper's checked contract, keeping its precondition,
postcondition, footprint and exact results. A narrowed flag return also requires
`ReturnsUnchanged`; aggregate results retain their complete byte list. See
[forwarder composition](PROOFS-CONTRACTS.md#inherit-a-callees-contract-in-a-forwarder).
A wrapper that allocates a private output, calls a helper and loads that output before returning
needs the helper's actual preservation and readback evidence. It is not an exact-result forwarder:
write permission alone proves neither initialized bytes nor their value. Compose its checked
call, local load and return using the evidence the helper actually guarantees.

For a word store through a named output, `cil_contract_steps` first uses supplied checked
operation facts. If none establishes the store, it derives a successful write from the current
`ValidCall` and the output bounds. This covers `store64`, eight-byte `storeScalar`, and
eight-byte `setFieldAt`. The continuation names the new memory `stored`, its address and byte
write equations `addressed` and `written`, the initialized bytes `readback`, and the retained
call requirements `storedCall`, with numeric suffixes when names are taken. Later argument
loads use facts about this new memory. Earlier input snapshots remain facts about their original
memory; no separation or initial output contents are inferred. `ValidCall.store_word` exposes
the same write and readback evidence for explicit composition.

`MethodContract.not_holds_of_fault` refutes a contract from a checked located fault on an input
meeting its precondition. It uses fuel monotonicity to rule out success at every budget;
the witness must be a semantic fault, not fuel exhaustion.

`WP.of_embedded_run` transports a successful suffix through `CIL.Embeds`, reusing the checked
embedding simulation. `CodeAt` identifies the suffix; embedding also checks instruction targets
and method metadata, since equal instruction lists alone do not justify relocating absolute
branches. `MethodContract.Holds.of_embeds` transports the complete contract through
`CIL.MethodEmbeds`, including its footprint and precondition.

`WP.load_call_store` composes a placed `loadCallStoreCode` segment with any proved scalar helper
contract. Both input words are loaded before the call and output write, so the argument ranges
may overlap. The continuation receives the helper's `CallResult` and the actual checked write.
It retains the helper's full postcondition and footprint without unfolding the helper body.

End new theorems with `#print axioms`. The normal verifier checks both the theorem and its
extraction binding; a successful standalone elaboration is not the full verification workflow.
See [soundness](SOUNDNESS.md) for the exact trust boundary and [validation](VALIDATION.md) for
focused regression commands.

Detailed reduction behavior and consumer-visible simplification interfaces are documented in
[stepping and reduction](PROOFS-STEPPING.md). They are implementation references, not prerequisites
for the first proof.
