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

`MethodContract.not_holds_of_fault` refutes a contract from a checked located fault on an input
meeting its precondition. It uses fuel monotonicity to rule out success at every budget;
the witness must be a semantic fault, not fuel exhaustion.

End new theorems with `#print axioms`. The normal verifier checks both the theorem and its
extraction binding; a successful standalone elaboration is not the full verification workflow.
See [soundness](SOUNDNESS.md) for the exact trust boundary and [validation](VALIDATION.md) for
focused regression commands.

Detailed reduction behavior and consumer-visible simplification interfaces are documented in
[stepping and reduction](PROOFS-STEPPING.md). They are implementation references, not prerequisites
for the first proof.
