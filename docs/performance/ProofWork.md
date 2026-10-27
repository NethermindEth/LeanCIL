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
decorated or malformed names. A full Evidence comparison is required before claiming suite-wide
savings.
