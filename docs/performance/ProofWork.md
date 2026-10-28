# Proof work measurements

Measured on Windows, AMD Ryzen 9 9950X, Lean 4.35.0. Each pair uses the same compiled
imports and toolchain, with no concurrent benchmark. Module times include process startup,
imports and elaboration. They are not whole-job CI timings.

## Allocation renaming

| Module | Before | After | Reduction |
| --- | ---: | ---: | ---: |
| `CIL.Safety.AllocatingStepRenaming` | 10.44s | 7.30s | 30.0% |
| `CIL.Safety.InstructionRenaming` | 11.62s | 10.31s | 11.2% |

`stepMemory` now uses the existing checked `step_memory_eq` instead of unfolding the
complete instruction dispatcher in three expressions. `instructionResult` rewrites its
outer guard directly and tries the write correspondence before the read correspondence.
The earlier order spent time reducing a write while trying to match an inapplicable read
lemma. The theorem statements and reported axioms (`propext`, `Quot.sound`) are unchanged.
End-of-proof heartbeat measurements fall from 264,632 to 227,277 for `instructionResult`
and from 5,451 to 602 for `stepMemory`. Both revisions' compiled declarations also pass
independent `leanchecker` replay. The unchanged `FixedStepRenaming` module was measured at
18.54s during initial profiling; no speculative change to that module is retained.

Run `lake env lean -Dprofiler=true CIL/Safety/AllocatingStepRenaming.lean` and the
corresponding `InstructionRenaming.lean` command after building dependencies on each revision.
Do not sum these module savings to predict the cold library critical path: their compilation
can overlap with other modules.

## IntegerMath

The 40 generated fixtures retain all 21,804 runtime boundary cases. Each final `correctness`
statement is byte-identical to its predecessor, including narrowing and located arithmetic
faults. The extraction, forged-identity and signature rejection checks are unchanged.

Results at fixed concurrency, with the same extraction sources, compiled imports and baseline
assignment of fixtures to four shards:

| Shard | Before | After |
| --- | ---: | ---: |
| 0 | 37.50s | 30.22s |
| 1 | 37.07s | 29.97s |
| 2 | 35.66s | 28.25s |
| 3 | 35.05s | 27.67s |

The proof phase is 19.4% faster. It creates 1,690 bounded boundary-group theorems instead of
21,804 individual boundary theorems. Projected success and fault wrappers also share the
`congrArg` proof instead of rebuilding it for every input. Groups have at most 16 leaves;
their recursive split follows the existing balanced statement exactly. A single giant inline
proof was slower and exceeded the normal heartbeat budget, so that experiment was discarded.
The four public `.olean` files shrink from 46,764,952 to 30,114,104 bytes (35.6%).
For shard 0, Lean's cumulative elaboration counter falls from 28.0s to 20.5s and its
type-checking counter from 15.8s to 9.52s. These overlapping counters are not additive.
All seven forged runtime identity/signature rejection checks still pass.
Independent replay of the same four serialized shards falls from 18.32s to 14.70s (19.8%).

For an end-to-end comparison, build each revision's authenticated library first, set
`DOTNET_PROCESSOR_COUNT=4`, and run `dotnet run --file Tests/IntegerMath.cs`. The measurements
above isolate generated-file compilation, exclude preparation and extraction, and hold the
baseline shard assignment fixed even though source lengths change. They do not establish the
elapsed time of the complete Math CI job.

### Checked boundary tables

On main `c59b64e`, a further change replaces the 1,690 conjunction-group theorems with
40 tables containing the same 21,804 input/outcome pairs, in the same order. Each table's
Boolean checker has a proved implication to equality of the execution result with the observed
runtime outcome. The kernel checks every row; one generic theorem covers every member, including
narrowing and located arithmetic faults. No comparison is sampled or removed.

The generated `correctness` statement is now universally quantified over that finite table,
rather than a large conjunction. This changes the internal test theorem's presentation, not
its coverage. The compiled minimum contract, incorrect maximum rejection, seven forged
signature/identity checks and BigMul checks remain unchanged.

At four shards on the same Windows machine, the slowest elaboration falls from 29.29s to
21.43s (26.8%). Independent replay rises from 6.35s to 8.08s, giving a combined reduction from
35.64s to 29.51s (17.2%) for these sequential stages. The complete warm local Math suite moves
from 58.08s to 56.49s; other stages and cache behavior dilute the proof-stage saving. These
measurements do not predict hosted CI wall time. All positive proofs and independent replay pass.
Larger conjunction groups, direct reflexivity terms, disabling unused-variable linting and
single-threaded elaboration did not improve this workload and are not retained.

## Evidence investigation (#424)

The initial investigation retained no Evidence optimization; the dispatch follow-up below
addresses one measured hotspot. Full-suite acceptance for #424 remains separate.
The complete generated Generic positive batch took 15.29s with existing compiled imports.
Three isolated changes to generic-constraint identity comparison did not materially improve it:

| Discarded experiment | Full positive batch |
| --- | ---: |
| Materialize canonical constraint strings as literals | 14.95s |
| Materialize them as byte-backed strings | 15.15s |
| Compare UTF-8 byte lists with checked string-equality equivalence | 15.31s |

All three candidate batches compiled, but these single-run differences do not establish a
useful gain. The experiments were removed. Serial diagnostic profiling identified six generic
specialization proofs taking roughly 0.42–0.59s in elaboration and 0.59–0.72s in kernel checking
per proof. Nested traces spend substantial time reducing string equality, but the tested local
changes did not improve the complete batch. Async profiler durations overlap and must not be
added; `-DElab.async=false` was used only to diagnose individual reductions, not as a proposed
production setting.

A separate experiment trimmed generated dependency closures. All tests passed, but complete
fixture times showed no material improvement: Generic 61.447→60.554s, TypeTests
24.808→25.139s, and ConstrainedCalls 25.589→25.736s. That change was also discarded.
Those fixture timings include more work than the positive-batch-only measurements above and
should not be compared directly with them.

### Constrained dispatch follow-up

On an Apple M4 ARM64 machine with Lean 4.35.0, the complete ConstrainedCalls positive batch
falls from 10.69/10.86s to 5.60/5.64s in repeated measurements (about 48%). Both revisions
start from main `0361ca9`, rebuild the affected dependency closure with Lake, and compile the
same generated source, SHA256 `ff40f05c551f2afe4c961073deaa0cbb27bd6dc1394a09a642292fc9a9fdb55b`.
The batch retains all four execution results, complete translation certificates and narrowed
positive controls. These are direct compilation timings, not complete Evidence suite timings.

The retained changes decode ASCII metadata by traversing its linked byte representation and
compare dispatch type keys as linked UTF-8 byte lists. A checked equality theorem establishes
that decoding produces exactly `String.toList` for every string; non-ASCII strings retain the
original decoder. The existing indexed-dispatch correspondence proofs remain unchanged.
The public `DispatchIndex` representation changes from keys of `List String` to
`List (List UInt8)`; lookup and resolution results are unchanged.

The two changes must be measured together: individual exploratory runs were 11.11s for the
decoder and 10.70s for byte keys against an 11.19s baseline, whereas their combination was
5.49s. These nonadditive timings motivated the clean repeated pair above; they do not establish
an additive cost model. Generic's positive batch remains approximately unchanged at 9.87s.

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

An exploratory padding variant tried its full monadic normalization before splitting the second
operand. That increased compilation to 58.12s by speculatively expanding unresolved matches and
was rejected. Importing the existing shared equations alone also showed no improvement for the
relabeling module (102.88s versus 102.59s); the retained change does not add that import.

### Execution equivalence and equation generation experiments

No change was retained in `ExecutionEquivalence` or `Equations`. Moving the stack-allocation
rule after cheaper proof alternatives measured 30.59s versus 29.85s on Windows with the same
profiling options, too small to establish a useful gain. On Apple M4, importing `Equations`
measured 12.95s versus 12.92s. Generating all of `step`'s direct matcher equations in a shared
module cost another 3.68s while the consumer still took 13.32s.

Lean 4.35.0's `Meta.Match.getEquationsForImpl` deliberately generates private splitters under
the current module, so importing an earlier module does not eliminate that generation.
A further experiment splitting the opcode before unfolding `step` exceeded the existing
heartbeat limit and was discarded. These experiments changed neither the retained source nor
its resource limits; their timings are not claimed as improvements.
