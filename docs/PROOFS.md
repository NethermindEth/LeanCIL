# Writing checked proofs

State the property independently of the emitted instructions. Use `CIL.Safety.invoke`,
`Ensures`, `MethodContract` or `OutcomeContract` when the claim includes checked execution.
Make input quantifiers, initial-memory assumptions and permitted writes explicit.

Start with the [addition walkthrough](GETTING-STARTED.md), then select the smallest proof
interface that expresses the result:

| Task | Guide | Executable example |
| --- | --- | --- |
| Execute a short method symbolically | [Instruction composition](PROOFS-STEPPING.md#compose-instructions) | [Add](../Examples/Proofs/Add.lean) |
| Carry existing theorems about a Lean model to compiled code | [Model proofs](../skills/leancil/references/bridge-model-proof.md) | [AddModel](../Examples/Proofs/AddModel.lean) |
| Call a helper through its proved contract | [Contract composition](PROOFS-CONTRACTS.md#compose-calls-through-contracts) | [CountCalls](../Examples/Proofs/CountCalls.lean) |
| Prove a loop terminates | [Loop examples](EXAMPLES.md) and [loop cutpoints](PROOFS-BINDING.md#loop-heads-and-call-sites) | [Countdown](../Examples/Proofs/Countdown.lean) |
| Establish buffer contents and preserve neighbours | [Buffer predicates](PROOFS-BUFFERS.md#describe-buffer-contents) | [FillWords](../Examples/Proofs/FillWords.lean) |
| Specify normal and exceptional outcomes | [Outcome contracts](PROOFS-CONTRACTS.md#name-exceptional-outcomes) | [CountUntil](../Examples/Proofs/CountUntil.lean) |
| Publish a smaller public guarantee | [Contract consequence](PROOFS-CONTRACTS.md#derive-public-contracts) | [Contract consequence tests](../Tests/ContractConsequence.lean) |
| Bind or transport a proof to extracted code | [Binding and transport](PROOFS-BINDING.md) | [Method binding tests](../Tests/MethodBinding.lean) |
| Import a separately proved interface | [Imported contracts](PROOFS-CONTRACTS.md#compose-through-imported-contracts) | [Interface guide](CONTRACT-INTERFACES.md) |

## Keep proof work local

Reuse checked stepping, memory readback and contract composition lemmas. Avoid unfolding helper
bodies when their contracts suffice. Loop invariants must describe the state at a checked
cutpoint, and continuing iterations must decrease an explicit measure. A finite successful
sample does not establish termination for arbitrary input.

End new theorems with `#print axioms`. The normal verifier checks both the theorem and its
extraction binding; a successful standalone elaboration is not the full verification workflow.
See [soundness](SOUNDNESS.md) for the exact trust boundary and [validation](VALIDATION.md) for
focused regression commands.

Detailed reduction behavior and consumer-visible simplification interfaces are documented in
[stepping and reduction](PROOFS-STEPPING.md). They are implementation references, not prerequisites
for the first proof.
