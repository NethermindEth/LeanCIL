# Proof work measurements

Measured on Windows, AMD Ryzen 9 9950X, Lean 4.35.0. Each pair uses the same compiled
imports and toolchain, with no concurrent benchmark. Module times include process startup,
imports and elaboration. They are not whole-job CI timings.

## Allocation renaming

| Module | Before | After | Reduction |
| --- | ---: | ---: | ---: |
| `CIL.Safety.AllocatingStepRenaming` | 10.44s | 7.30s | 30.0% |
| `CIL.Safety.InstructionRenaming` | 11.62s | 10.31s | 11.2% |

`stepMemory` uses the checked `step_memory_eq` instead of unfolding the
complete instruction dispatcher in three expressions. `instructionResult` rewrites its
outer guard directly and tries the write correspondence before the read correspondence.
The earlier order spent time reducing a write while trying to match an inapplicable read
lemma. The theorem statements and reported axioms (`propext`, `Quot.sound`) are unchanged.
End-of-proof heartbeat measurements fall from 264,632 to 227,277 for `instructionResult`
and from 5,451 to 602 for `stepMemory`. Both revisions' compiled declarations also pass
independent `leanchecker` replay.

Run `lake env lean -Dprofiler=true CIL/Safety/AllocatingStepRenaming.lean` and the
corresponding `InstructionRenaming.lean` command after building dependencies on each revision.
Do not sum these module savings to predict the cold library critical path: their compilation
can overlap with other modules.

## IntegerMath boundary tables

The fixture uses 40 tables containing all 21,804 input/outcome pairs. Each table's
Boolean checker has a proved implication to equality of the execution result with the observed
runtime outcome. The kernel checks every row; one generic theorem covers every member, including
narrowing and located arithmetic faults. No comparison is sampled or removed.

The generated `correctness` statement is universally quantified over that finite table.
The compiled minimum contract, incorrect maximum rejection, seven forged
signature/identity checks and BigMul checks remain unchanged.

At four shards on the same Windows machine, the slowest elaboration falls from 29.29s to
21.43s (26.8%). Independent replay rises from 6.35s to 8.08s, giving a combined reduction from
35.64s to 29.51s (17.2%) for these sequential stages. The complete warm local Math suite moves
from 58.08s to 56.49s; other stages and cache behavior dilute the proof-stage saving. These
measurements do not predict hosted CI wall time. All positive proofs and independent replay pass.

## Constrained dispatch

On an Apple M4 ARM64 machine with Lean 4.35.0, the complete ConstrainedCalls positive batch
falls from 10.69/10.86s to 5.60/5.64s in repeated measurements (about 48%). Both revisions
start from main `0361ca9`, rebuild the affected dependency closure with Lake, and compile the
same generated source, SHA256 `ff40f05c551f2afe4c961073deaa0cbb27bd6dc1394a09a642292fc9a9fdb55b`.
The batch retains all four execution results, complete translation certificates and narrowed
positive controls. These are direct compilation timings, not complete Evidence suite timings.

Dispatch decodes ASCII metadata by traversing its linked byte representation and
compares dispatch type keys as linked UTF-8 byte lists. A checked equality theorem establishes
that decoding produces exactly `String.toList` for every string; non-ASCII strings retain the
original decoder. The existing indexed-dispatch correspondence proofs remain unchanged.
The public `DispatchIndex` representation uses keys of `List (List UInt8)`.

Independent kernel replay of the complete constrained batch passes. All four independently
forged constrained targets still fail their intended `ConstrainedCallsValid` obligation;
the constrained metadata regression module also passes, including Unicode scopes and rejected
decorated or malformed names.

### Integrated Evidence suite

The complete Windows Evidence suite, including checked control reuse, passes in 400.03s against
440.27s on main `0361ca9` (9.1% faster). Including C# builds, the command takes 431.33s against
475.72s. Both runs use `dotnet run --file scripts/Test.cs -- --suite evidence`, with each revision's
authenticated library prepared beforehand, no concurrent benchmarks, and no supplied fixture
manifest. Library production is excluded from both suite measurements.

| Work | Before | After |
| --- | ---: | ---: |
| Complete constrained-call fixture | 28.08s | 14.15s |
| Complete generic evidence fixture | 65.77s | 59.59s |
| Lean frontend calls | 52 / 210.80s | 51 / 184.46s |
| Positive-batch independent replay calls | 6 / 34.69s | 6 / 33.26s |
| Extractor CLI calls | 182 | 182 |

The original positive claims and independent mutations pass, together with two added rejection
checks for missing or changed control declarations. Both runs contain 74 expected nonzero child
commands. Frontend, replay and fixture durations overlap the suite duration; they are not additive
savings. These are local measurements, not predicted hosted-runner job times.

## Operand case pruning in embedding proofs

On Windows, the same warm imported libraries and sequential `lake env lean <module>.lean`
commands gave these frontend and kernel-check times. Each command recompiles the source file;
these figures exclude Lake dependency rebuilding, artifact serialization and independent replay.

| Module | Before | After | Reduction |
| --- | ---: | ---: | ---: |
| `CIL/Safety/Embedding/Step.lean` | 102.59s | 66.26s | 35.4% |
| `CIL/Safety/StepFlow.lean` | 31.14s | 21.79s | 30.0% |
| `CIL/Safety/Embedding/AppendLocals.lean` | 24.60s | 21.10s | 14.2% |

Relabeling closes each operand-shape case before inspecting the next operand. Padding first
tries its existing dispatcher-tail theorem, so an invalid first operand does not repeat that
proof for every second-operand constructor. Callee classification extracts the successful result
of a bind instead of expanding its impossible error branch. The interpreter, theorem statements
and permitted axioms are unchanged. All 27 existing relabeling and 92 padding axiom reports match
before and after; the callee theorem explicitly reports only `propext` and `Quot.sound`.
The compiled `Step.olean` also shrank from 54,298,952 to 36,064,856 bytes (33.6%). This
reduces serialized proof data; no downstream import or replay saving is inferred from its size.

### Definitional observer normalization

The shared `step_observers` proof helper uses `dsimp` when unfolding `observerCount`.
That step needs only definitional equality; `simp` previously constructed congruence proofs
while traversing the same large dispatcher terms for every instruction family. The following
simplification still checks and removes the observer guard using its proved false result.

On Windows with the same compiled imports and Lean 4.35.0, recompiling
`CIL/Safety/Embedding/Step.lean` with `-Dprofiler=true` took 74.05s before and 58.81s after.
The simplifier's cumulative counter fell from 43.6s to 24.9s; definitional simplification was
17.7s before and 17.3s after. These profiler counters overlap and are not additive timings.
A second compilation, additionally writing the module's `.olean`, took 63.51s;
its serialized declarations passed independent `leanchecker` replay. All 27 existing axiom
reports match the baseline. Public theorem statements, execution semantics and proof-facing
step equations are unchanged. These are module measurements, not predicted CI job times.

### Observer guard simplification

The observer guard is absent from the hypothesis returned by `observer_ok` or
`observer_thrown`. After definitional normalization, the final guard simplification visits
only the goal. Re-simplifying the already normalized hypothesis traversed its full dispatcher
again for every successful and throwing instruction proof.

Measurements use Linux x86-64 Lean 4.35.0 under WSL, source and imports on ext4, fixed
`-j2 -Dprofiler=true`, and no concurrent benchmark. With warm imports, the earlier full-`simp`
observer variant takes 70.11s and the existing `dsimp` variant takes 54.16s. This reproduces the
previous improvement on Linux; it does not establish a regression from the slower hosted CI run.
The new goal-only simplification reduces the same module from 54.16s to 49.14s. Its cumulative
`simp` counter falls from 20.7s to 12.7s while `dsimp` is 14.8s versus 15.3s; these overlapping
counters are not additive. An initial cold-import sample was excluded from this comparison.

A second paired run writing `.olean` files takes 56.63s before and 53.22s after. Both serialized
modules pass independent `leanchecker` replay and all 27 axiom reports match. The smaller
repeat saving is reported separately rather than treating the first run as a CI prediction.
