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

## Evidence investigation (#424)

No Evidence optimization is retained from this investigation; #424 remains unresolved.
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