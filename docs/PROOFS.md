# Writing checked proofs

Use `CIL.Safety.invoke` for specifications that include checked memory execution.
State the mathematical contract and its input/memory preconditions independently
of the implementation. The [soundness boundary](SOUNDNESS.md) describes what a
successful checked execution establishes.

## Compose instructions

Import `CIL.Safety.SymbolicExecution` and mark definitions used for instruction
lookup with `@[cil_code]`. This complete example executes eight instructions on
symbolic inputs and preserves arbitrary caller memory:

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

The [automation regression](../Tests/Automation.lean) checks this pattern and
symbolic branch proofs. This handwritten body demonstrates the tactic; a proof
about an assembly must bind its body to the generated program, as described in
the [README](../README.md#binding-extraction-independent-bodies), and pass verification.

`cil_checked_steps` composes `invoke_of_run`, `run_next`, `run_return` and
`run_call_of_invoke`. It checks method/instruction lookups and frame setup,
infers intermediate states, and checks the returned values. These lemmas are
also available directly from [StepComposition](../CIL/Safety/StepComposition.lean)
and [CallComposition](../CIL/Safety/CallComposition.lean) for manual proofs.

Its single-step helper, `cil_checked_step []`, first tries `rfl`. A concrete
opcode with symbolic operands can often reduce definitionally without an
expanded dispatcher in the proof term. If needed, it selects a local equation
for argument loads, returns or supported scalar conditional branches, then
uses simplification. Operations outside those equations retain the dispatcher
fallback.

For steps depending on hypotheses, use `cil_checked_steps [truth, stored]`
with the relevant proved facts. A nonempty fact list skips the initial `rfl`:
otherwise a symbolic branch can succeed by assigning an unresolved conditional
expression to the next program counter, leaving the following lookup stuck.
Both straight-line and loop-exit automation try return proofs only for fetched
`.ret` instructions, including narrow returns, so other opcodes do not incur
failed return-step simplification.

For loops, import [LoopAutomation](../CIL/Safety/LoopAutomation.lean).
`cil_loop_steps [facts]` composes an execution segment and `cil_loop_finish [facts]`
proves an exit path and its postcondition. Supply an invariant and decreasing
measure to the loop termination theorem; these tactics do not infer termination.
See the [countdown proof](../Examples/Proofs/Countdown.lean).

## Reuse framework contracts

When extending generic safety proofs, reuse the facts established by the shared
dispatch or traversal proof. Names in this table are in `CIL.Safety`, except
the base relabeling helpers in `CIL.Embedding`.

| API | Reusable information | Source |
| --- | --- | --- |
| `RunTrace` | Successful execution through next, return, call and construction cases | [ExecutionTrace](../CIL/Safety/ExecutionTrace.lean) |
| `FrameSetup` | Fresh ownership, frame allocations, preservation below the allocation boundary, static bindings and conditional validity | [FrameSetupLemmas](../CIL/Safety/FrameSetupLemmas.lean) |
| `InstructionContract` | Memory effects and conditional output-value validity from one instruction analysis | [InstructionMemoryLemmas](../CIL/Safety/InstructionMemoryLemmas.lean) |
| `StaticInstructionContract` | Corresponding contract for static-memory instructions | [StaticMemoryLemmas](../CIL/Safety/StaticMemoryLemmas.lean) |
| `StepContract` | Memory/frame effects and conditional live-value validity for a checked action | [ExecutionInvariants](../CIL/Safety/ExecutionInvariants.lean) |
| `Fallthrough`, `Branching` | Shared relabeling proofs for base instruction families | [BaseStep](../CIL/Embedding/BaseStep.lean) |

These contracts retain their hypotheses. For example, `InstructionContract.values`
requires well-formed input memory and valid input values; its memory-effect field
does not require those additional hypotheses. `RunTrace` describes successful
execution; fault-preservation proofs need the appropriate equivalence lemmas.

## Keep proof work local

Prefer a small `change` or an instruction equation over repeatedly unfolding
`run`, `CIL.Safety.step` and `CIL.step`. For generic opcode proofs, split the
opcode and stack shape before splitting operand constructors, and close
definitionally equal cases early. Share the remaining family-level reasoning.
For concrete execution, compose steps first and simplify the resulting value
equation separately when needed.

Measure changes with fresh Lean processes and prebuilt dependencies on both
revisions. Alternate baseline and candidate runs serially on the same machine,
and include downstream consumers. Record elapsed time, CPU time, `.olean` bytes,
peak process memory and kernel replay separately. A smaller artifact can still
require expensive elaboration or cause callers to repeat work; peak memory also
includes imported environments. Keep kernel replay and the axiom audit enabled.

The [validation guide](VALIDATION.md#proof-automation) describes the regression
coverage and commands for checking the proof tactics.
