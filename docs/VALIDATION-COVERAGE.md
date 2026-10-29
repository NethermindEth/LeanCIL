# Coverage and verification infrastructure

## Preparation and shared infrastructure

The workflow builds `scripts/Test.cs`, `Tests/ContractExport.cs` and
`Tests/FullImportVerification.cs` once with Release analyzer checks. Their shared artifact is bound
to a separately supplied manifest digest, the SDK/runtime, included sources, repository build
configuration and the complete output file set. The workflow checks executable hashes before
starting the runner. Nested fixture invocations check the same identity and use the compiled
assembly; absent or incompatible preparation falls back to an ordinary local build. Modified example
assemblies are still rebuilt by their mutation tests. Only relocated fixture binaries use the shared
checkout override; source-built child scripts retain their own source root, including producers
running against an isolated modified library. Configuration identity includes props, targets and
configuration files along the entry script's directory chain through the checkout root. Fixtures
with `#:project` references use an ordinary build because their external MSBuild source graph is not
described by file-app includes.

`Tests/PreparedFixtures.cs` covers arguments, included-source changes, nested configuration changes,
unsupported project references, SDK/runtime mismatches, manifest tampering and added or modified
output files. Shared preparation amortizes fixture compilation across suites; producer work and
artifact transfers remain part of total CI time.

Branch positions and prefix-bypass checks use indexes scoped to each body traversal, and call
translation uses a method index scoped to the current ordered call graph. Original and specialized
bodies have separate instruction indexes. Dependency invalidation traverses reverse import edges
once with a queue, including missing roots and cycles. Support reuse retains the existing external
module and extraction-source binding exceptions. `Tests/InstructionIndexes.cs`,
`Tests/ConstrainedResolution.cs` and `Tests/ConsumerSupportCandidates.cs` cover identity, fresh
traversal, branch/switch prefix bypasses, reverse-ordered chains, cycles, missing imports and
support source bindings.

Extraction reuses each method's reachability result within validation, emission and exception
linting. Feature evidence uses the same incoming states as instruction selection. Each phase
computes a fresh result, so no analysis is cached across method mutation or profile changes.
`Tests/ExtractionBatch.cs` compares direct and batch output across assemblies, scalar and SIMD
profiles, feature queries and a loop backedge, and retains source/assembly tampering checks.

The array, generic, layout and parameter evidence fixtures submit their 63 independent positive
extractions in six batches. Each method retains fresh mutable metadata; immutable assembly bytes,
hashes and whole-assembly signature validation are shared within the batch. Long-form argument
fixtures use a separate batch after writing their modified assembly. Expected extraction failures
remain isolated, since a batch stops at its first failure.

On Windows, the 45 positive array/generic extractions took 7.90s as individual commands and 0.59s in
three batches. Their emitted Lean sources were byte-identical, and their positive proofs,
independent replay and mutation checks passed. This measures extraction work, not the complete
Evidence suite or hosted CI wall time.

Generated positive evidence in `PrimitiveArrays`, `LayoutEvidence`, `ParameterEvidence`,
`GenericEvidence` and `StaticScalarValues` shares imports within each fixture. Each extraction and
its proof remain in their own namespace, following the generated verification batch pattern. The
combined file is compiled once and independently replayed with `leanchecker`; passes are printed
only after both checks and source-stability checks succeed. Rejection fixtures still run separately
with their original diagnostic assertions. The array read, null and bounds checks share one final
file instead of checking the read twice.

Generic and constrained-call positive controls retain their narrowed declarations and exact
obligation types, but reuse the original checked theorem instead of reducing its validator again.
Generic controls compile and replay in the original positive batch. Missing or changed control
declarations must still fail type checking; isolated mutation cases retain their original validator
proofs and diagnostic checks, without access to the positive-control witnesses. Constrained fixtures
include direct closed generic struct slots with substituted parameters and results, closed
interfaces on ordinary and generic structs, and explicit implementations whose interface
instantiations share a token and signature. A forged closed override owner must fail the same
checked dispatch obligation. These cases share the existing positive batch and kernel replay. The
projected declarations use a distinct namespace, so missing names cannot fall back to the original
`Extracted` namespace. Controls reject explicit access to that namespace while preserving quoted
metadata strings and disable automatic implicit parameters. Regression cases cover removed
declarations used by definitions or obligation types, changed definitions, qualified references and
opened namespaces. Rejection diagnostics retain their case boundaries with or without Lean's
diagnostic classification codes. Feature-flow and folded-span mutations use the same checked
controls and retain only the intended feature-flow obligation in each negative fixture. Every
rejection must identify `FeatureFlowValid` as false. Full positive certificates, runtime
comparisons, and consumer replay remain; folded instructions with an unrecognized theorem cannot
silently skip a test. On Apple M4 with the indexed constrained-dispatch library already built, the
constrained positive batch fell from 5.67s to 5.26s. Generic positive compilation, independent
replay and controls took 18.79s before reuse and 16.84s afterward, including replay of the controls
in the combined batch. These fixture measurements exclude extraction, dependency setup and unchanged
rejection checks; they are incremental gains on top of the dispatch improvement, not whole-suite CI
timings.

Each of these five scripts accepts `--measure`, which first checks the same final source files
separately. `artifacts/<fixture>/batch-timings.json` records source hashes, separate time and batch
compilation/replay time. One local run measured:

| Positive evidence | Files | Separate checking | Batch checking and replay |
| --- | ---: | ---: | ---: |
| Primitive arrays | 30 | 68.37s | 18.34s |
| Layouts | 7 | 17.64s | 14.11s |
| Parameter homes | 11 | 43.06s | 14.28s |
| Generic specializations | 15 | 42.84s | 32.16s |
| Static scalar values | 16 | 40.39s | 8.16s |
| Total | 79 | 212.29s | 87.04s |

These timings exclude extraction, dependency setup and unchanged rejection cases; they are not
whole-suite CI timings. `GenericEvidence` also checks that an invalid proof fails batch compilation
and that an unchecked declaration reaches, and fails, independent kernel replay. The complete local
`PrimitiveArrays` fixture, including extraction and rejection checks, took 76.20 seconds before
batching and 31.72 seconds afterward.

```sh
dotnet run --file Tests/PrimitiveArrays.cs -- --measure
```

`Tests/CliImportedKernelAudit.cs`, called by the CLI suite, extends the producer's certified base
with two previously uncompiled helper sources. Both standalone `verify --fresh` calls use private
copies authenticated by that producer's manifest digest. The valid helper succeeds; the forged
`AuditBad.helper` fails specifically during kernel replay and removes the previous certificate. Both
helpers remain outside the audited base aggregate. The fixture also rejects using the modified
corpus's certificate with the unmodified tool. Trace assertions require zero fresh base
builds/replays, one source extension and two successful private copies. New helper declarations
never inherit certification from that extension. Run `dotnet run --file
Tests/CliImportedKernelAudit.cs` after building the extractor and example assembly; `--
--fresh-preparation` measures one fresh preparation, and `-- --measure-baseline` measures the
original two-build workload. Without a supplied base, a local run prepares it before measuring the
extension. Each run writes `timings.json` beneath its isolated `artifacts/CliImportedKernelAudit-*`
directory.

`Tests/LibrarySourceExtension.cs` independently checks manifest authentication, private copies,
changed/self-rehashed compiled artifacts, existing-source edits/removals, configuration changes,
compiled-module shadows (including case variants on case-insensitive filesystems), and preservation
of an existing destination. Its synthetic compiled bytes exercise preparation integrity only; the
CLI fixture supplies the end-to-end kernel checks against real compiled declarations.

`Tests/ConsumerBatchSetup.cs` runs the fixed mixed-outcome consumer checks used by the core suite.
Imported axioms, unchecked declarations, expected-rejection mismatches and invalid execution proofs
retain their own outcomes and certificate assertions. Successful requests after rejected proofs
verify that failures do not contaminate their shared session. The checks use one certified-base
preparation instead of three; `--separate` reproduces the old two isolated rejections followed by
the seven-request batch. Both modes write stage counts and timings under
`artifacts/ConsumerBatchSetup-*`, with caches disabled for the measured requests. When a certified
artifact is supplied, copy counts are asserted as one versus three. Mutable-source, environment,
provenance, receipt-tampering and process-progress tests remain separate. The core test copies only
its exact framework cache entry into its private cache.

```sh
dotnet run --file Tests/ConsumerBatchSetup.cs -- --separate
dotnet run --file Tests/ConsumerBatchSetup.cs
```

One local comparison of these nine requests, against the same certified base, took 113.79 seconds
separately and 65.66 seconds batched. Base copies fell from three to one, consumer builds from five
to three, and replay invocations from six to three. This is a measurement of the selected cases, not
the whole core suite or a CI wall-time guarantee.

`Tests/ExternalIdentityEncoding.cs` kernel-checks generated identity strings against their literal
values, including empty strings, embedded NULs, escaping and Unicode characters crossing chunk
boundaries. Malformed UTF-16 is rejected before serialization, and invalid UTF-8 fails its validity
proof. A compiled `Math.Abs` extraction passes, while a changed, still-valid UTF-8 call identity
fails `ScalarFlowValid`.

`scripts/BenchmarkExternalIdentities.cs` accepts fixed baseline `Extracted.lean` files with
`externalIdentityNBytes_eq` declarations. It replaces only their identity encoding with the current
emitter, compiles both complete modules with one Lean worker, then independently kernel-replays
each. All chunk declarations are included. `artifacts/ExternalIdentityBenchmark` contains the paired
sources and `timings.json`, including input SHA-256, source/artifact sizes, compilation and replay
times. Use the same fixed files and toolchain when comparing results. For per-declaration kernel
costs, run the paired Lean files with `--json --profile -j1 -DElab.async=false
-Dprofiler.threshold=0`; JSON source positions identify each declaration.

Consumer checks compile together in `Tests/ConsumerVerification.cs` and run in separate child
processes. Run one with `dotnet run --file Tests/ConsumerVerification.cs -- --check <name>`. Names
are `source-resolution`, `support-union`, `certificate-reuse`, `components`, `fingerprints`, and
`certified-fingerprints`. Each retains its private process and worker checks.

`Tests/ConsumerComponents.cs` checks four independently certified wrappers around one helper. The
common profile/layout and helper modules must compile and replay once, while all four complete
extraction certificates must replay. Profile, helper and call-target changes invalidate their
component identities; a consumer source shadowing a generated component must fail without a
certificate. Source byte counts and compilation/replay/wall timings are recorded in `timings.json`.
Pass a baseline extractor DLL and `--measure` to run the same workload without asserting reuse. The
existing certificate-reuse fixture still checks authenticated cross-process restoration,
self-rehashed corrupt artifacts, changed extraction sources and generated-source tampering.

`Tests/VerificationCache.cs` checks certified-library copying against the pinned manifest, source
snapshot and toolchain key, rejects changed/missing/extra files and rehashed manifests, and
independently detects destination corruption. On Unix it also checks that both streamed artifacts
and copied metadata retain their file modes. `Tests/LibraryCopyScaling.cs` compares separate
validation/copying with hashing during copying, retaining independent destination validation in both
paths. It alternates four pairs over the same framework/native build files and records file count,
bytes and wall time. An optional argument selects the donor `.lake/build` directory, by default the
certified library's; the synthetic performance fixture is never supplied to a verifier as a
certified library.

`Tests/ConsumerFingerprintReuse.cs` checks authenticated canonical fingerprints across independent
verifier processes using two framework modules and a multipart fixture. It covers corrupt receipts,
changed or missing parts, module names, auditor bytes, fresh and disabled caches, diagnostic
normalization, source/import invalidation and kernel replay. `--measure` uses the fixed full
framework plus fixture workload and records wall time, raw input bytes, serialization counts and
native normalization time. Supply a baseline worker DLL before `--measure` to compare the same seven
requests.

`Tests/CertifiedFingerprints.cs` compares direct normalization with an authenticated
prepared-library table while local receipts remain disabled. It checks identical canonical results
across independent receivers, relocation, renamed modules, changed parts and native tools, metadata
mutation before publication and consumption, and self-rehashed corruption. The normal fixture uses
two framework modules plus one consumer module; `--measure` uses the complete prepared framework and
compares direct and prepared requests, recording fingerprint time, total worker time and
serialization counts. Preparation normalizes the framework once; its cost must be included when
assessing a workload's amortized savings.

`Tests/ConsumerCertificateReuse.cs` measures four independent verifier processes with distinct proof
sources. Unchanged generated certificates retain their authenticated build outputs and skip the
otherwise redundant certificate `lake build` invocation. Reuse requires the complete certificate
module parts and traces, unchanged authenticated restored artifacts, and the existing source/import
closure binding. Changed extraction text and self-rehashed corrupt artifacts force rebuilding
`Extracted`. Every successful request still independently replays `Extracted` and the proof and
audits the certificate. Expected rejection groups retain the separate `ExtractionAudit` module.
Generated-source tampering remains rejected before receipt reuse, and proof code cannot replace
restored or freshly built certificate artifacts; both rejection paths remove a stale report. Pass a
baseline extractor DLL and `--measure` to collect the same workload without requiring preparation
reuse; process counts and elapsed times are written to `timings.json`.

Generated certificates have their own authenticated support records containing only the closed
generated module set. Their preparation key binds all generated sources and their Lake
configuration, framework artifacts, tools and declared environment inputs. Consumer package
configuration changes can reuse this preparation without reusing consumer modules or exempting the
certificate from replay. The default consumer workload checks this with its existing
custom-build-directory request and checks invalidation with its existing Lake environment mutation;
these assertions add no verification requests.

Run `dotnet run --file Tests/ConsumerVerification.cs -- --check certificate-reuse
--configuration-reuse` for focused configuration reuse, fresh verification, self-rehashed corruption
and post-restoration artifact mutation checks. Run `dotnet run --file Tests/ConsumerVerification.cs
-- --check components --configuration-reuse` to check that split certificates retain their complete
generated dependency set across a consumer configuration change. These extra requests are opt-in and
are excluded from the unchanged full-workload timing comparison.

The complete Windows consumer workload took 615.93s before this configuration reuse and 605.23s
after it, with the same 29 top-level assertions and helper fixtures. Certificate builds fell from 37
to 35 (89.31s to 84.88s); fresh consumer builds remained 48, joint replays 52 and fallback replays
4. The focused configuration-only request took 5.30s versus 7.19s with `--fresh`, avoiding a 2.06s
certificate build. Both full runs used isolated success caches and the same authenticated framework
donor. This removes specific redundant work; the 1.7% total improvement is not a substantial suite
speedup.

On Windows, the unchanged-extraction request removed one 0.186s certificate process; total request
time was 4.976s before and 4.952s after, so this run establishes the eliminated work but not a
significant overall latency gain. Both measurements used an already certified library and retained
independent replay of `Extracted` and `LeanCILProof`.

Ordinary consumer requests regenerate the extraction and recheck their original inputs once after
proof execution. Export and full-import callbacks retain another recheck after the callback
executes. The fixture records these recheck counts and times: four requests dropped from eight
rechecks (0.675s) to four (0.341s) on Windows. Total request times were noisy, so this measures
eliminated work rather than an established overall latency improvement. The export and full-import
mutation cohorts continue to check the post-callback integrity guards.

`Tests/StandaloneCertificateReuse.cs` measures complete CLI requests against an already certified
library, including source guards, native theorem audits and independent kernel replay. Standalone
verification audits `Extracted.translation_valid` directly, eliminating the separate
`ExtractionAudit` elaboration. The fixture checks frontend process counts for initial, unchanged,
proof-edited, changed-extraction and `--fresh` requests. Pass a baseline extractor DLL and
`--measure` to compare the previous wrapper-based implementation.

| Windows request | Before | After | Frontend processes before → after |
| --- | ---: | ---: | ---: |
| Initial verification | 7.613s | 5.729s | 3 → 2 |
| Unchanged verification | 1.784s | 1.783s | 0 → 0 |
| Proof-only edit | 5.611s | 5.611s | 1 → 1 |
| Changed extraction | 7.603s | 5.740s | 3 → 2 |
| Fresh proof verification | 7.462s | 5.714s | 3 → 2 |

The existing `Tests/TranslationAudit.cs` independently checks the direct certificate's exact type
and rejects missing, unrelated, non-theorem and wrong-import-table declarations, as well as a
definitionally equal but structurally different statement. CLI regressions retain unchecked-theorem
and transitive-helper rejection, stale-report removal and changed-code proof failure. The remaining
generated and proof modules still elaborate independently; this improvement does not introduce
shared frontend environments or native snapshots.

`Tests/TranslationScaling.cs` checks the unchanged extraction prefix once, then imports it into the
compositional certificate and deliberately failing monolithic certificate. Its `--measure` option
also checks both original complete files and records command timings for the identical six-method
workload. The consumer still verifies the original extraction. `Tests/TranslationAudit.cs` shares
and replays the prefix once across certificate mutations; each variant retains its original
certificate audit and rejection assertions. A changed prefix is rejected before any suffix can use
the checked module.

`Tests.CertificateFlow` covers streaming fallthrough, indexed forward/backward edges, missing
states, out-of-bounds targets and mismatched certificate lengths. The feature and scalar equivalence
theorems retain the original list-indexed rules, including rejection when the feature and scalar
certificate lengths differ.

`Tests/CertificateFlowScaling.lean` and `Tests/CertificateBranchScaling.lean` provide fixed 512-nop
and 512-branch workloads, each followed by a return, for kernel checking and independent replay.
Their profiler reports tactic execution and kernel type-checking separately. Compile and replay each
workload, for example:

```sh
lake env lean -o .lake/build/lib/lean/Tests/CertificateFlowScaling.olean Tests/CertificateFlowScaling.lean
lake env leanchecker Tests.CertificateFlowScaling
```

Compare identical source with baseline and updated libraries; native evaluation alone does not
measure this workload. The benchmark is separate from ordinary library builds.

`Tests/ConsumerSupportUnion.cs` runs a fixed three-extraction consumer batch in two orders. Support
imported only by later groups must build and replay once; direct and indirect extraction-dependent
modules must replay in every consuming group, including repeated import commands on one line.
Compiled import headers remain authoritative when scheduling misses an import. The fixture records
wall, build and replay timings and module counts in `timings.json`. Run it with an extractor DLL
path and `--measure` to record a baseline without asserting the improved reuse counts. The ordinary
consumer suite runs the assertions.

For checked-step and loop tactics, see [proof automation](VALIDATION-PROOFS.md#proof-automation).

`Tests/LocalSnapshotSteps.lean` checks opt-in local snapshot stepping through vector and int32
stores, reloads and overwrites with abstract homes and memory, plus signed-byte narrowing. The
mixed-width case carries Vector256, Vector128 and int32 locals through one snapshot invariant and
returns the full arbitrary 256-bit input after the other locals are written. Missing write
authority, mismatched local kinds and unknown local contents remain rejected. Each rejection uses an
isolated store or load and a matching successful run with only the missing authority, correct value
kind or remembered contents supplied. Strict proof elaboration prevents an incomplete rejected proof
from inserting a placeholder. The ordinary shared tactic tests run unchanged.

`Tests/PrimitiveArrays.cs` checks compiled loads and stores for twelve primitive integer element
types against runtime results and certified checked execution. It also covers length, helper calls,
aliases, returned arrays, named null/bounds faults and unsupported array forms. Independent changes
to load width or signedness must fail the Lean scalar certificate. `Tests/PrimitiveArrays.lean`
covers empty and null arrays, signed and native indices, initialization, authority, invalid extents,
local storage and neighboring-byte preservation. Both run in the evidence suite.

`Tests/ArrayElementReferences.cs` checks compiled `ldelema` returns, helper reads and writes against
runtime behavior, preserving neighboring contents and rejecting a forged element type.
`Tests/ArrayElementReferences.lean` covers null, empty and out-of-range accesses, expired references
and address formation without granting memory authority. Both run in the evidence suite.

`Tests/ReadOnlyArrayReferences.cs` inserts real `readonly.` prefixes into compiled fixtures, checks
returned and locally stored references, and proves that caller stores fail despite writable backing
memory. It rejects independently forged writable evidence, separated prefixes and branches that skip
a prefix. `Tests/ReadOnlyArrayReferences.lean` also checks alias updates, read access and rejection
of an adapter that would remove the restriction. Both run in the evidence suite.

`Tests/StaticScalarValues.cs` compares 16 compiled readonly-field loads with the runtime, covering
integer widths, Boolean/Char, native integers, signed/unsigned enums, helper initialization and
copies. It rejects missing initialization assumptions, mutable fields, repeated stores, branches and
address-taking during initialization. Independent Lean checks reject forged scalar signedness, width
and literal evidence. It runs in the evidence suite.

The repository pins .NET SDK **10.0.403** and Lean **4.35.0**. The checks below cover semantic
behavior, extracted contracts, artifact integrity and rejection cases.

```sh
lake build
dotnet run --file scripts/Test.cs
```

The regression runner covers **54 check groups** across twenty-three test partitions. This includes
initial CLI proof selection and theorem output, an actual addition-to-subtraction source edit and
rebuild, recovery using settings retained after the failed proof, the invalid-memory-access theorem,
and the integer opcode, narrow-storage and primitive-operation matrices. The CLI tests also exercise
an isolated installation of the packaged .NET tool.

The runner builds the independent assemblies and the CIL library, then prepares a source-keyed,
kernel-replayed library for verification. CI rebuilds from sources; local runs may reuse a cache
entry whose receipt binds its key and manifest. The library is checked by its trusted manifest
digest and read in place: every proof still compiles and undergoes kernel replay in a new private
session package that requires the library as a path dependency, so Lake writes only below that
session. File-based C# apps provide the test runner, verifier and metadata fixture generator.
Metadata tooling uses the same pinned Mono.Cecil version as the extractor; the F# example assembly
also uses pinned FSharp.Core.

CI prepares the certified library once per workflow attempt and passes its immutable artifact ID,
the run that uploaded it and its manifest digest from the producer job to the suite jobs. The
producer first looks for a library already certified by a run of the same commit. On push events it
next checks at most ten associated merged PRs from the same repository, requiring their merge commit
to be this push and their complete Git tree to match exactly. Successful runs of those heads precede
the main push of the checkout's first parent. API failures or absent eligible artifacts retain the
older-main/source-build fallback. Their own trusted code built that library and printed its digest,
so the digest is read from the donor job's log, never from the artifact. `PrepareLibrary.cs --reuse`
then rechecks the library key and source binding and kernel-replays the library; any mismatch, or no
donor, builds from source. It does not restore compiled libraries from the GitHub Actions cache: a
cache's source key and self-described file hashes cannot authenticate the native auditor or
establish that compiled modules came from those sources.

`dotnet run --file scripts/PrepareLibrary.cs -- <output-directory>` requires an empty or absent
destination and publishes a freshly built library through a staging directory. Explicit reuse uses
`--reuse <trusted-manifest-sha256>`; obtain this digest independently from a trusted producer, never
by hashing the restored manifest itself. Missing or invalid reuse evidence fails without replacing
the destination. Rebuilding an existing library requires a separate output directory.
`Tests/LibraryCache.cs` covers substituted auditors and compiled modules with regenerated manifests,
missing producer digests, and preservation of unrelated destination files.

Main push runs publish their validated library even after exact reuse. This keeps the main run
eligible to donate to later PRs without following a chain of earlier runs. Suite jobs prefer the
current run's artifact when it uploaded one; PR runs that reuse a donor still consume that donor
directly. Publication follows the existing source binding and independent kernel replay.

When only Lean sources changed, `--incremental <donor-directory> <trusted-manifest-sha256>`
authenticates every donor file before reusing its Lake build traces in a private copy. The runtime,
compiler, kernel checker and build configuration must match. Changed and removed modules lose their
compiled artifacts; Lake checks the current source hashes and rebuilds the dependent closure. The
native auditor is relinked, every resulting module is kernel-replayed, and canonical fingerprints
are regenerated before a new source-bound manifest is published. CI tries this after exact reuse,
then falls back to a cold build if incremental preparation fails. `Tests/LibraryIncremental.cs`
covers artifact tampering, incompatible identities/configuration, source removal and copy isolation.

A Windows run with an `OleanAudit`-only comment edit rebuilt that module, its native object and the
auditor executable: compilation took 4.31s, full replay 11.75s, fingerprints 7.89s, and total
preparation 32.43s. Exact reuse took 12.36s. The donor's cold compilation on the same host/toolchain
took 189.40s during fixture setup; that setup overlapped other short validation work, so this is not
a controlled paired timing. All compiled module-part hashes matched the donor after the comment
edit; the new certificate bound the changed source. These are local library timings, not full CI job
measurements.

`Tests/LibraryReplayCoverage.cs` uses a small synthetic producer manifest with a valid aggregate and
an invalid theorem in a separate module. Both joint replay and its external-checker fallback must
reject that declaration; checking only the aggregate is insufficient. The cache fixture runs this
regression alongside the authentication tests.

The runner accepts `--suite <name>` after `--`, with names `core`, `cli`, `integer`, `narrow`,
`primitive`, `division`, `checked`, `conversions`, `native`, `arguments`, `layout`, `copy`, `bits`,
`enums`, `nested`, `instance`, `constructors`, `fsharp`, `math`, `divrem`, `unsafe`, `blocks`,
`generics`, `loops`, `contracts`, `evidence`, `scaling`, `excluded`, `identity`, `labels`, `names`,
`symbols`, `workspace`, `templates`, `callers`, `construction`, `outcomes` and `audit`. These
partitions cover the same check groups as the full command and can run concurrently in separate
checkouts. Each partition builds its own prerequisites (in CI, one job builds the extractor and
example assembly with `--build-tools` and suite jobs set `LEANCIL_PREBUILT_TOOLS=true` to use them),
retains fresh Lean proof checking and writes `artifacts/test-results-<suite>.json`; running without
arguments checks everything and writes `artifacts/test-results.json`.

| Coverage | Result |
| --- | --- |
| Profile-parametric templates | Compiled AVX2/SSE4.2 dispatch helper, one generated template proof on three profiles, renumbered managed callees, exact per-pc equations, independent kernel replay, and wrong flag/callee/branch/equation, stale source and metadata rejection |
| Cyclic control flow and termination | Universal checked countdown proof for every `uint`, including zero and maximum value; a counted loop proved through its helper's contract, unchanged for a reimplemented helper and rejecting a discarded result or double count; a loop that returns or raises its helper's exception after earlier calls, proved for every pair of `uint`s from the helper's outcome contract, unchanged for a reimplemented helper and rejecting another exception type, a nondecreasing measure, a non-inductive invariant and a wrong specified exception; a buffer fill loop proved to write exactly `count` words for every nonnegative count, with four runtime comparisons and shifted or skipping stores rejected; 17 runtime comparisons; incorrect implementation rejected under the unchanged contract; infinite loop proved to exhaust every fuel budget; backward switch, native arithmetic and fixed-feature loops checked; eight malformed or unsupported fixtures rejected |
| Generic method specialization | 125 C#/F# runtime comparisons, six universal identity proofs, six reference checks, twelve metadata/recursion rejections, wrong-implementation rejection and provenance tamper detection |
| Block memory and alignment prefixes | 251 checks; ten malformed-prefix/type cases rejected; universal out-of-bounds fill rejection |
| Layout-based Unsafe helpers | 418 checks across 19 element types and all three managed offset overloads; ten malformed generic calls rejected |
| Checked Unsafe value transfers | Runtime comparisons and checked execution proofs cover signed and unsigned scalars, aggregates and integer vectors through byte references and pointers. Aligned pointer cases use physically aligned runtime buffers, while unaligned cases access byte offset one. Shared boundary proofs cover initialization masks, unreadable scalars, bounds and readonly destinations; aligned cases additionally check misalignment and write-only authority. Certificate mutations reject incorrect widths, signedness, helper identity, transfer direction, scalar/vector alignment and aggregate layout alignment. |
| Byte-span value transfers | Eight compiled MemoryMarshal wrappers cover reads, writes and their try forms for scalars, aggregates and integer vectors. Nineteen checked behavior claims include short-span exceptions, default-initialized out values, write-free failed try-writes, write authority and initialization masks. Seven certificate mutations reject changed signatures, operations, flags and scalar/vector/aggregate widths. |
| Span reinterpretation | Compiled mutable and readonly AsBytes/Cast wrappers cover enum types, aliasing writes, empty and uninitialized storage, truncated lengths and overflow. Lean certificate mutations reject changed widths, capability and operation. |
| Overlapping span copies | Six compiled wrappers and seventeen checked claims cover mutable and readonly sources, enums and 64-bit elements, both overlap directions, self-copy, disjoint slices within one allocation, empty spans, short destinations, initialization, write authority and neighboring bytes. Six independent certificate mutations reject changed widths, operation, try flag, external identity, readonly destination and enum identity. Runtime checks compare copied contents with snapshot copying. |
| Typed indirect dispatch | Compiled pointer locals and supplied handler tables cover ordinary calls, indirect tail cycles, return/throw outcomes, null tables, bounds, unknown targets and local-reference expiration. Independent Lean certificate mutations reject forged targets, identities, signatures, numeric pointers, conventions and dropped tail semantics. Malformed calling conventions and branches into a tail transfer are rejected during extraction. |
| Aggregate and vector spans (`AggregateSpans`) | Reference-free aggregate buffers and integer vectors cover views, slicing, typed reads/writes, reinterpretation, overlap-safe copying and clearing. Vector masks and neighboring bytes are checked; vector-field layouts are certified for x64 and ARM64. Evidence mutations reject forged widths and write capabilities. |
| Aggregate/vector fills (`AggregateSpanFill`) | Five compiled aggregate, Vector128/256/512 and aliased-source wrappers check repeated values, initialization masks, unknown-lane rejection, empty views, write authority and neighboring bytes. Independent evidence mutations reject changed aggregate/vector widths and clear/fill flags. |
| Span constructors (`SpanConstructors`) | Single-reference and pointer constructors cover primitive, aggregate and integer-vector elements, mutable/readonly views and in-place local initialization without readable bytes. Vector-field aggregate layouts are checked on x64 and ARM64; evidence mutations reject changed widths and capabilities. |
| Supplied aggregate/vector arrays (`AggregateArrays`, `AggregateArrayStorage`) | Typed element addresses, loads/stores, lengths, span conversions and data references cover reference-free structs and integer vectors over existing storage. Kernel fixtures check masks, authority, bounds, lifetime and readonly views; independent evidence mutations reject changed element descriptors and operations. |
| Closed generic structs (`GenericLayouts`) | Sequential same-assembly reference-free instantiations cover nested layouts, fields, direct instance methods and constructors through checked owner substitution and ordinary aggregate storage. Unsupported reference-bearing, open, non-sequential and interface/reference-constrained generic layouts remain rejected. |
| Byte-order span transfers (`BinarySpans`) | Compiled wrappers exercise all 48 signed/unsigned 16-, 32- and 64-bit read/write/try endian overloads, short spans, read/write authority and uninitialized reads. Evidence mutations reject altered widths, endian choices, signedness and try behavior. |
| No-read view observations (`ViewAccessors`) | Span emptiness, pinnable references and array data references cover empty/default/readonly views, empty and null arrays and observations without readable bytes or byte authority. Evidence mutations reject mismatched accessors and capabilities. |
| Closed generic owners (`GenericOwners`) | Static helpers on closed same-assembly generic owners, nested owners and combined owner/method arguments certify through structural substitution; evidence mutations reject incorrect owner and argument bindings. |
| Native managed dispatch (`NativeManagedDispatch`, `NativeMethodTables`) | Supplied immutable native tables cover checked byte-offset loads, authenticated native target locals, separate numeric locals and tail dispatch. Fault and certificate controls reject invalid storage, target provenance and signature changes. |
| Null managed references | `IsNullRef` of `NullRef` and of a live argument, reads and writes through `NullRef` (indirect and field) and an optional `ref` local: ten outcomes compared with .NET, each `NullReferenceException` matched to a located null-dereference fault; forged `NullRef`/`IsNullRef` translations rejected by the call binding; 22 malformed generic calls rejected |
| Reference/null observations | Emitted CIL fixtures compare .NET and checked Lean execution for `ceq`, `brtrue`, `brfalse`, `beq`, `bne.un` and bounded `ldnull`; an independently changed equality operation must fail scalar evidence. Semantic fixtures cover readonly views, null, lifetime, invalid addresses, end pointers and disjoint allocation interiors. A null-message throw fixture preserves existing folding. |
| Integer Math helpers | 21,804 runtime comparisons across 40 overloads; universal signed-minimum proof; incorrect implementation and seven malformed calls rejected |
| `X86Base.X64.DivRem` through `ValueTuple<ulong, ulong>` Item1/Item2 reads | Runtime tuple offset probe; 500 checked-execution boundary cases across five read shapes compared with hardware and a `UInt128` oracle, including divide-by-zero and overflow faults; universal quotient and fault proof; remainder substituted for quotient rejected; eight forged calls, scopes and tuple layouts rejected |
| Library, scalar/SIMD semantics, allocation, permissions, initialization, lifetime and symbolic automation | Passed |
| Ten extracted arithmetic, branching, call, aliasing, aggregate and semantic-negative proofs, each with artifact checks | Passed |
| Compiled C# negation: universal modular additive-inverse contracts for 32- and 64-bit inputs | Both proofs passed |
| Exact `nop`, `neg`, `cgt`, `bgt`, `bgt.s`, `ble`, `ble.s`, `ble.un`, `ble.un.s` encodings in independent Cecil fixtures | 370 checked-execution boundary cases passed across 32- and 64-bit operands |
| Identity substituted for negation, with the unchanged universal contract | Both widths rejected by proof checking; no successful report retained |
| New scalar operations: stack underflow, mixed widths and reference operands; `nop` preserves arbitrary stacks | Semantic tests passed |
| Compiled C# unsigned-short conversion: universal result `x % 65536` for every 32-bit input | Proof passed |
| Narrow conversions, locals, arguments, returns, calls and fields, including aggregate snapshots | 744 checked-execution boundary cases passed, including 144 deliberate faults |
| Uninitialized narrow locals and 64-bit stores into narrow homes | Rejected with the expected located faults |
| Two-byte field overrun and forged narrow runtime type identity | Both rejected during extraction |
| Signed conversion substituted for unsigned conversion, with the unchanged universal contract | Rejected by proof checking; no successful report retained |
| Narrow access bounds, permissions and lifetime; generic typed store/load normalization | Semantic tests and universal roundtrip theorem passed |
| Compiled C# `ref int` store/load: every 32-bit input returned unchanged | Universal proof passed |
| Primitive `ldobj`, `stobj`, `initobj`, indirect loads/stores, C# aliasing, `switch` and `sizeof`, including native integer storage | 534 cases passed, including memory faults, initialization and preservation of neighboring bytes |
| Empty/duplicate switch tables, out-of-range unsigned indices and switch-only managed dependencies | Passed |
| Corrupted switch target, unsupported arm, four forged type tokens and floating-point size | Seven intended extraction rejections |
| `sizeof` on pointers, managed references, objects, strings, arrays, double, auto layouts and malformed sequential field offsets, reference-containing structs and unsupported generic layouts | Eleven intended extraction rejections; no Lean extraction produced |
| Constant-zero write substituted for the input, with the unchanged universal store/load contract | Rejected by proof checking; no successful report retained |
| Scalar access operand/width checks, bounds and lifetime; arbitrary-memory 32-bit store/load roundtrip | Semantic tests and universal roundtrip theorem passed |
| Short and full assembly selectors retain the same complete manifest identity | Passed |
| Explicit version, culture and public-key-token mismatches | Three intended identity rejections |
| Method selectors: aliases, optional returns, short declaring types, overloads, canonical artifact identity, malformed inputs and candidate diagnostics | 23 checks passed |
| Assembly inference from a renamed DLL, equivalent explicit identities, mismatched constraints, malformed options and stale outputs without `--assembly` | Passed |
| Directory-only checks: recorded profiles, moved DLL override, missing DLL, invalid profile and modified artifacts | Passed |
| Independent hardware-feature assembly built from a single C# file | Passed |
| CLI packaging smoke checks: build and publish `leancil.exe`, `dotnet run`, isolated .NET tool installation, installed `leancil extract` and `leancil check` | Passed separately |
| One-command worked example: `dotnet run --file Examples/Verify.cs` | Passed; `ExampleProof.correctness` verified |
| Installed `leancil verify`: explicit proof, printed theorem, portable settings, source mutation, failure/recovery, memory fault theorem and stdout/stderr | Four CLI regression stages passed |
| Method discovery includes canonical selectors and unsupported candidates without claiming support | Passed |
| Malformed settings, missing proof, unsupported CIL, changed assembly and missing Lake produce stage-specific guidance | Passed |
| Subtraction rejected by the unchanged universal addition contract | Passed; no successful report retained |
| Primitive integer array allocation | Checked zero initialization, empty/non-null identity, negative/native lengths, helper returns and stores; forged element/operation certificates and unsupported element types rejected |
| Integer `div`, `div.un`, `rem`, `rem.un`, both widths | 648 comparisons against actual .NET execution and corresponding Lean proofs passed, including divide-by-zero and signed overflow |
| Extracted unsigned quotient for arbitrary inputs with a nonzero divisor | Universal proofs passed for 32 and 64 bits; multiplication substituted for division rejected by the unchanged contract |
| Division with mixed widths, references, stack underflow or a zero divisor | Semantic rejection tests passed |
| Checked add/subtract/multiply, signed and unsigned at both widths | 2,028 comparisons against actual .NET results or overflow exceptions and corresponding Lean proofs passed |
| Checked addition with a sum that fits | Universal 32-/64-bit natural-number addition proofs passed; subtraction substituted for addition rejected |
| All 20 integer checked-conversion encodings, from both input widths | 762 comparisons against actual .NET execution and corresponding Lean proofs passed, including native destinations and overflow |
| Checked 64-to-32-bit unsigned narrowing with a representable input | Universal preservation proof passed; an eight-bit truncating implementation rejected |
| Native signatures, locals, calls, fields, references, arithmetic, shifts, casts and `sizeof`, plus exact mixed native/int32 operations in both operand orders | 2,511 comparisons against actual .NET results or arithmetic exceptions and corresponding Lean proofs passed; all 60 ambiguous mixed unsigned-branch forms rejected unless explicitly widened |
| Extracted native addition on the admitted 64-bit target | Universal modular-addition proof passed |
| Required-32-bit assembly, forged native type identity, native field overrun, native/int64 operands and 32-bit execution profile | Five intended extraction rejections |
| Native widening wrapper with memory instructions, nested wrappers or references | Semantic rejection tests passed; unsigned branch/comparison widening differences checked explicitly |
| Argument assignment/addressing, both full and short encodings, all admitted integer storage types, aliases, calls, byref reassignment and structs | 639 runtime/memory cases passed, including 636 actual .NET comparisons |
| Overwriting an argument with a replacement value | Universal proof passed for arbitrary inputs; assignment to the wrong parameter rejected |
| Returning an address into a parameter home | Lifetime fault proved for every input; successful execution ruled out for every fuel budget |
| Parameter setup with missing inputs or incompatible scalar/reference values, and narrow initialization | Semantic checks passed; taking the address of a byref parameter rejected during extraction |
| Ordinary and packed sequential structs, all admitted packing values, small/odd explicit sizes and empty structs | 187 runtime layout/execution cases passed; emitted sizes and field offsets agree with managed runtime probes |
| Sequential struct field store/load | Universal preservation proof passed for every 32-bit input |
| Invalid packing, oversized layout, auto layout, reference/float fields, inline arrays, generics, explicit offsets on sequential fields, nested reference-bearing and recursive fields | Ten intended metadata rejections |
| Synchronized methods, wrong framework/identity, invalid field layout, unsupported locals, static initializer and forged runtime scope | Seven intended metadata rejections |
| Identity-bound static RVA data | Passed |
| Static `ReadOnlySpan<uint>`/`<ulong>` tables | Indexed reads, length and first element compared with .NET, including negative and past-end indices faulting with `System.IndexOutOfRangeException`; forged receiver folds fail the feature certificate; tampered RVA bytes change the proved word; branches into the fold rejected |
| Memory-backed primitive spans | Compiled readonly and writable slices passed to helpers; sequence-content read and update contracts, and readonly/writable caller composition without unfolding helper bodies; creation over an existing reference; forged element widths and write capabilities rejected by specialization evidence; empty end slices, invalid indexes and slices, alias visibility, missing write authority, uninitialized reads and expired local storage; by-reference and floating-point span signatures rejected |
| Static readonly struct values | `Zero`, `One` and `MinValue` limbs proved and compared with the values .NET's static constructor stored, also through an out parameter; a changed constructor argument changes the proved limbs; forged value bytes fail `translation_valid`; a missing initialization assumption, a `newobj` initializer, `ldsflda`, a store outside the static constructor and a second store rejected; Lean regressions for the load semantics and a self-justifying initializer |
| Static `ReadOnlySpan<byte>` lookup tables | First and last byte proved; past-end read and write to immutable data rejected; tampered RVA bytes change the proved value; four intended span metadata rejections and positive stored-span parameter/local fixtures |
| Tampered Lean output, changed compiled assembly, changed assembly version with a short selector, changed proof and changed feature profile | Five intended stale-artifact rejections |

The addition theorem proves modular arithmetic correctness for arbitrary 64-bit inputs in the
checked execution model. The unsigned-short theorem proves reduction modulo 65,536 for arbitrary
32-bit inputs. The invalid-access and expired-reference theorems classify faults and rule out
successful execution for every fuel budget. The subtraction theorem independently refutes the
intended addition result. Other example claims have the quantifiers and inputs displayed in their
theorem statements; concrete examples do not establish universal method correctness.

All audited example theorems use only the permitted standard Lean axioms, if any. No new axioms,
`sorry`, `admit`, native proof evaluation or unproved summaries were added. See [the trusted
base](SOUNDNESS.md) for runtime and extraction assumptions.

Machine-readable results are written to `artifacts/test-results.json`; each successful proof
produces an identity-bound `verified.json`. These generated files are reproducible outputs and are
not committed. Consumer-project integration and broad .NET runtime coverage are outside these
validation results.

Typed copy validation: 648 runtime result/byte-copy checks passed across 18 primitive, struct and
vector types, including self-copies. The universal UInt64 copy contract passed and rejected reversed
source/destination operands. Four unsupported/forged type-token cases were rejected during
extraction. Ten semantic tests cover initialization, permissions, lifetime, GC-sensitive storage,
bounds, null references and partial overlap. The generic copy snapshot theorem and the full Lean
library/semantic/automation build passed.

Portable helper validation: 7,200 comparisons with actual .NET results passed, covering power-of-two
boundaries, zero/all-ones values, signed boundaries and negative/oversized rotation counts.
Universal 64-bit rotation round-trip and integer-logarithm proofs passed with only approved Lean
axioms; incorrect implementations failed the unchanged contracts. Nine malformed/unsupported runtime
calls were rejected before extraction. Semantic tests reject incorrect arity, widths and operand
types.

Enum validation: 378 runtime comparisons passed across all eight underlying integer types, flags,
calls, fields and typed storage. The universal flags proof passed and rejected an incorrect
implementation. Eleven malformed metadata cases were rejected.

Nested struct validation: 123 runtime/layout comparisons passed, including sixteen packing
combinations. A universal nested snapshot proof passed and rejected an incorrect implementation.
Seven malformed layouts and seven semantic memory-fault cases were rejected.

Struct instance-call validation: 96 runtime comparisons passed, including short and full argument
encodings, by-value copy isolation and direct constructor calls. A universal instance store/load
proof passed and rejected an incorrect implementation. Four malformed metadata cases were rejected.

Struct construction validation: 56 runtime comparisons passed, covering packed and nested structs,
chained and parameterless constructors, zero-initialized storage and checked arithmetic faults. A
universal constructed-value proof passed for every 64-bit input; an incorrect constructor result
failed the unchanged contract. Five malformed constructor cases were rejected. Semantic tests cover
zero-sized construction, missing arguments, zero initialization and a non-void constructor result.
The full 125-job Lean library, semantic and automation build passed.

F# validation: 324 comparisons with actual .NET execution passed for addition, unsigned branching,
managed calls, mutable structs and by-reference stores. The existing addition, store/load and
constructor contracts passed unchanged against the F# assembly. Subtraction failed the addition
contract, and a list-returning function was rejected during extraction. These examples require no
F#-specific CIL semantics or proof shortcuts.

## Contracts and extraction evidence

`Tests/StackAllocation.cs` extracts compiled pointer and span stack allocations, checks results with
and without localsinit, rejects uninitialized reads and escaped storage, and checks
insufficient-budget failure. Mutating the emitted initialization flag is rejected by the Lean
certificate. `Tests/StackAllocation.lean` covers alignment, repeated allocations and expiry;
`Tests/StackAllocationEvidence.lean` rejects forged flags, injected allocations, extra stack items
and non-native 64-bit size operands. These run in the `evidence` suite.

`Tests/ConstrainedCalls.cs` checks compiled implicit and explicit struct-interface calls, including
closed generic owners and mutation through the receiver, and rejects forged generated call targets,
owner arguments and malformed prefix, branch and interface-constraint metadata.
`Tests/ConstrainedResolution.cs` checks the extractor's resolution rules;
`Tests/ConstrainedEvidence.lean` independently checks Lean resolution, target, signature, ambiguity
and prefix rejection. These run in the `evidence` suite.

The core and universal-contract suites cover checked execution and memory preservation. Choose and
GenericIdentity preserve arbitrary caller memory exactly; Struct preserves preexisting caller memory
under its well-formedness hypothesis. Each unchanged contract rejects its incorrect compiled
implementation. Countdown validation covers original instructions, inserted NOPs and reordered
blocks, and rejects wrong results and nontermination.

Extraction evidence validation passed 74 Lean regressions, 34 compiled certificate fixtures, 29
generated-evidence mutation rejections, and mandatory-certificate positive/negative checks. All six
CLI checks passed, including kernel replay of imported helpers and rejection of unchecked
direct/transitive proofs. `Tests/ImportEvidence.lean` accepts an external call into a matching
import slot and rejects a forged identity, parameter count, receiver or result shape, a wrong
emitted argument count, a slot index inside the program or past the table, constructor and generic
sites, and managed or non-call sites reaching the import range; the certificate audit also rejects a
certificate over a different import table. These tests do not establish full raw-CIL/runtime
correspondence.

The native extraction suite passed 2,511 runtime comparisons and kernel proofs, its universal
addition contract, 60 ambiguous mixed unsigned-branch rejections and five metadata/profile
rejections. Separate pinned .NET 10.0.0 probes on x64 and ARM64 each passed 3,600 admitted cases;
500 rejected cases retain 38 historical model divergences. Full JIT optimization produced identical
per-case results. See [native evidence](evidence/native/README.md) for exact provenance and
reproduction commands.

Memory-view equivalence covers access, writes and subsequent checked execution, including calls,
constructors and frame cleanup. At 128 alternating stores the benchmark retained one view rather
than 129; median local kernel-reduction time was 5.6s versus 17.7s over three runs, including
startup and shared-machine activity. These timings are illustrative, not a performance guarantee.

The initialized-types end-to-end test and four mandatory-certificate audit cases check that
verification reports record both the schema-3 extraction audit and initialized-type assumptions.

