# Validation coverage

The workflow builds `scripts/Test.cs`, `Tests/ContractExport.cs` and
`Tests/FullImportVerification.cs` once with Release analyzer checks. Their shared artifact is
bound to a separately supplied manifest digest, the SDK/runtime, included sources, repository
build configuration and the complete output file set. The workflow checks executable hashes
before starting the runner. Nested fixture invocations check the same identity and use the
compiled assembly; absent or incompatible preparation falls back to an ordinary local build.
Modified example assemblies are still rebuilt by their mutation tests.

`Tests/PreparedFixtures.cs` covers arguments, included-source changes, SDK/runtime mismatches,
manifest tampering and added or modified output files. This targets the 66 runner builds,
14 contract-export builds and ten full-import builds observed in run 40486409764. CI timing
must confirm the net saving, including the shared producer and artifact transfer.

Branch positions and prefix-bypass checks use indexes scoped to each body traversal, and call
translation uses a method index scoped to the current ordered call graph. Original and specialized
bodies have separate instruction indexes. Dependency invalidation traverses reverse import edges
once with a queue, including missing roots and cycles. Support reuse retains the existing external
module and extraction-source binding exceptions.
`Tests/InstructionIndexes.cs`, `Tests/ConstrainedResolution.cs` and
`Tests/ConsumerSupportCandidates.cs` cover identity, fresh traversal, branch/switch prefix bypasses,
reverse-ordered chains, cycles, missing imports and support source bindings.

Extraction reuses each method's reachability result within validation, emission and exception
linting. Feature evidence uses the same incoming states as instruction selection. Each phase
computes a fresh result, so no analysis is cached across method mutation or profile changes.
`Tests/ExtractionBatch.cs` compares direct and batch output across assemblies, scalar and SIMD
profiles, feature queries and a loop backedge, and retains source/assembly tampering checks.

Generated positive evidence in `PrimitiveArrays`, `LayoutEvidence`, `ParameterEvidence`,
`GenericEvidence` and `StaticScalarValues` shares imports within each fixture. Each extraction
and its proof remain in their own namespace, following the generated verification batch
pattern. The combined file is compiled once and independently replayed with `leanchecker`;
passes are printed only after both checks and source-stability checks succeed. Rejection
fixtures still run separately with their original diagnostic assertions. The array read,
null and bounds checks share one final file instead of checking the read twice.

Each of these five scripts accepts `--measure`, which first checks the same final source files
separately. `artifacts/<fixture>/batch-timings.json` records source hashes, separate time and
batch compilation/replay time. One local run measured:

| Positive evidence | Files | Separate checking | Batch checking and replay |
| --- | ---: | ---: | ---: |
| Primitive arrays | 30 | 68.37s | 18.34s |
| Layouts | 7 | 17.64s | 14.11s |
| Parameter homes | 11 | 43.06s | 14.28s |
| Generic specializations | 15 | 42.84s | 32.16s |
| Static scalar values | 16 | 40.39s | 8.16s |
| Total | 79 | 212.29s | 87.04s |

These timings exclude extraction, dependency setup and unchanged rejection cases; they are
not whole-suite CI timings. `GenericEvidence` also checks that an invalid proof fails batch
compilation and that an unchecked declaration reaches, and fails, independent kernel replay.
The complete local `PrimitiveArrays` fixture, including extraction and rejection checks,
took 76.20 seconds before batching and 31.72 seconds afterward.

```sh
dotnet run --file Tests/PrimitiveArrays.cs -- --measure
```

`Tests/CliImportedKernelAudit.cs`, called by the CLI suite, extends the producer's certified
base with two previously uncompiled helper sources. Both standalone
`verify --fresh` calls use private copies authenticated by that producer's manifest digest. The valid
helper succeeds; the forged `AuditBad.helper` fails specifically during kernel replay and
removes the previous certificate. Both helpers remain outside the audited base aggregate.
The fixture also rejects using the modified corpus's certificate with the unmodified tool.
Trace assertions require zero fresh base builds/replays, one source extension and two successful
private copies. New helper declarations never inherit certification from that extension.
Run `dotnet run --file Tests/CliImportedKernelAudit.cs` after building the extractor and example
assembly; `-- --fresh-preparation` measures one fresh preparation, and `-- --measure-baseline`
measures the original two-build workload. Without a supplied base, a local run prepares it
before measuring the extension. Each run
writes `timings.json` beneath its isolated `artifacts/CliImportedKernelAudit-*` directory.

`Tests/LibrarySourceExtension.cs` independently checks manifest authentication, private copies,
changed/self-rehashed compiled artifacts, existing-source edits/removals, configuration changes,
compiled-module shadows (including case variants on case-insensitive filesystems), and preservation
of an existing destination. Its synthetic compiled bytes exercise preparation integrity only;
the CLI fixture supplies the end-to-end kernel checks against real compiled declarations.

`Tests/ConsumerBatchSetup.cs` runs the fixed mixed-outcome consumer checks used by the core
suite. Imported axioms, unchecked declarations, expected-rejection mismatches and invalid
execution proofs retain their own outcomes and certificate assertions. Successful requests
after rejected proofs verify that failures do not contaminate their shared session. The
checks use one certified-base preparation instead of three; `--separate` reproduces the old
two isolated rejections followed by the seven-request batch. Both modes write stage counts
and timings under `artifacts/ConsumerBatchSetup-*`, with caches disabled for the measured
requests. When a certified artifact is supplied, copy counts are asserted as one versus three.
Mutable-source, environment, provenance, receipt-tampering and process-progress tests remain
separate. The core test copies only its exact framework cache entry into its private cache.

```sh
dotnet run --file Tests/ConsumerBatchSetup.cs -- --separate
dotnet run --file Tests/ConsumerBatchSetup.cs
```

One local comparison of these nine requests, against the same certified base, took
113.79 seconds separately and 65.66 seconds batched. Base copies fell from three to one,
consumer builds from five to three, and replay invocations from six to three. This is a
measurement of the selected cases, not the whole core suite or a CI wall-time guarantee.

`Tests/ExternalIdentityEncoding.cs` kernel-checks generated identity strings against their
literal values, including empty strings, embedded NULs, escaping and Unicode characters
crossing chunk boundaries. Malformed UTF-16 is rejected before serialization, and invalid
UTF-8 fails its validity proof. A compiled `Math.Abs`
extraction passes, while a changed, still-valid UTF-8 call identity fails `ScalarFlowValid`.

`scripts/BenchmarkExternalIdentities.cs` accepts fixed baseline `Extracted.lean` files with
`externalIdentityNBytes_eq` declarations. It replaces only their identity encoding with the
current emitter, compiles both complete modules with one Lean worker, then independently
kernel-replays each. All chunk declarations are included. `artifacts/ExternalIdentityBenchmark`
contains the paired sources and `timings.json`, including input SHA-256, source/artifact sizes,
compilation and replay times. Use the same fixed files and toolchain when comparing results.
For per-declaration kernel costs, run the paired Lean files with `--json --profile -j1
-DElab.async=false -Dprofiler.threshold=0`; JSON source positions identify each declaration.

`Tests/ConsumerComponents.cs` checks four independently certified wrappers around one helper.
The common profile/layout and helper modules must compile and replay once, while all four
complete extraction certificates must replay. Profile, helper and call-target changes invalidate
their component identities; a consumer source shadowing a generated component must fail without
a certificate. Source byte counts and compilation/replay/wall timings are recorded in `timings.json`.
Pass a baseline extractor DLL and `--measure` to run the same workload without asserting reuse.
The existing certificate-reuse fixture still checks authenticated cross-process restoration,
self-rehashed corrupt artifacts, changed extraction sources and generated-source tampering.

`Tests/VerificationCache.cs` checks certified-library copying against the pinned manifest,
source snapshot and toolchain key, rejects changed/missing/extra files and rehashed
manifests, and independently detects destination corruption. On Unix it also checks that
both streamed artifacts and copied metadata retain their file modes.
`Tests/LibraryCopyScaling.cs` compares separate validation/copying with hashing during
copying, retaining independent destination validation in both paths. It alternates four
pairs over the same framework/native build files and records file count, bytes and wall
time. An optional argument selects the donor `.lake/build` directory, by default the certified
library's; the synthetic
performance fixture is never supplied to a verifier as a certified library.

`Tests/ConsumerFingerprintReuse.cs` checks authenticated canonical fingerprints across
independent verifier processes using two framework modules and a multipart fixture. It
covers corrupt receipts, changed or missing parts, module names, auditor bytes,
fresh and disabled caches, diagnostic normalization, source/import invalidation and
kernel replay. `--measure` uses the fixed full framework plus fixture workload and records
wall time, raw input bytes, serialization counts and native normalization time. Supply a
baseline worker DLL before `--measure` to compare the same seven requests.

`Tests/CertifiedFingerprints.cs` compares direct normalization with an authenticated
prepared-library table while local receipts remain disabled. It checks identical canonical
results across independent receivers, relocation, renamed modules, changed parts and native
tools, metadata mutation before publication and consumption, and self-rehashed corruption.
The normal fixture uses two framework modules plus one consumer module; `--measure` uses
the complete prepared framework and compares direct and prepared requests, recording
fingerprint time, total worker time and serialization counts. Preparation normalizes the
framework once; its cost must be included when assessing a workload's amortized savings.

`Tests/ConsumerCertificateReuse.cs` measures four independent verifier processes with
distinct proof sources. Unchanged generated certificates retain their authenticated build
outputs and skip the otherwise redundant certificate `lake build` invocation. Reuse requires
the complete certificate module parts and traces, unchanged authenticated restored artifacts,
and the existing source/import closure binding. Changed extraction text and self-rehashed
corrupt artifacts force rebuilding `Extracted`. Every successful request still independently
replays `Extracted` and the proof and audits the certificate. Expected rejection groups retain
the separate `ExtractionAudit` module. Generated-source tampering remains rejected before
receipt reuse, and proof code cannot replace restored or freshly built certificate artifacts;
both rejection paths remove a stale report. Pass a
baseline extractor DLL and `--measure` to collect the same workload without requiring
preparation reuse; process counts and elapsed times are written to `timings.json`.

On Windows, the unchanged-extraction request removed one 0.186s certificate process; total
request time was 4.976s before and 4.952s after, so this run establishes the eliminated work
but not a significant overall latency gain. Both measurements used an already certified
library and retained independent replay of `Extracted` and `LeanCILProof`.

`Tests/TranslationScaling.cs` checks the unchanged extraction prefix once, then imports it
into the compositional certificate and deliberately failing monolithic certificate. Its
`--measure` option also checks both original complete files and records command timings
for the identical six-method workload. The consumer still verifies the original extraction.
`Tests/TranslationAudit.cs` shares and replays the prefix once across certificate mutations;
each variant retains its original certificate audit and rejection assertions. A changed
prefix is rejected before any suffix can use the checked module.

`Tests.CertificateFlow` covers streaming fallthrough, indexed forward/backward edges,
missing states, out-of-bounds targets and mismatched certificate lengths. The feature and
scalar equivalence theorems retain the original list-indexed rules, including rejection
when the feature and scalar certificate lengths differ.

`Tests/CertificateFlowScaling.lean` and `Tests/CertificateBranchScaling.lean` provide fixed
512-nop and 512-branch workloads, each followed by a return, for kernel checking and independent
replay. Their profiler reports tactic execution and kernel type-checking separately.
Compile and replay each workload, for example:

```sh
lake env lean -o .lake/build/lib/lean/Tests/CertificateFlowScaling.olean Tests/CertificateFlowScaling.lean
lake env leanchecker Tests.CertificateFlowScaling
```

Compare identical source with baseline and updated libraries; native evaluation alone does
not measure this workload. The benchmark is separate from ordinary library builds.

`Tests/ConsumerSupportUnion.cs` runs a fixed three-extraction consumer batch in two orders.
Support imported only by later groups must build and replay once; direct and indirect
extraction-dependent modules must replay in every consuming group, including repeated import
commands on one line. Compiled import headers remain authoritative when scheduling misses an import.
The fixture records wall, build and replay timings and module counts in `timings.json`.
Run it with an extractor DLL path and `--measure` to record a baseline without asserting
the improved reuse counts. The ordinary consumer suite runs the assertions.

For checked-step and loop tactics, see [proof automation](#proof-automation).

`Tests/LocalSnapshotSteps.lean` checks opt-in local snapshot stepping through vector and int32
stores, reloads and overwrites with abstract homes and memory, plus signed-byte narrowing.
The mixed-width case carries Vector256, Vector128 and int32 locals through one snapshot
invariant and returns the full arbitrary 256-bit input after the other locals are written.
Missing write authority, mismatched local kinds and unknown local contents remain rejected.
Each rejection uses an isolated store or load and a matching successful run with only the
missing authority, correct value kind or remembered contents supplied. Strict proof elaboration
prevents an incomplete rejected proof from inserting a placeholder.
The ordinary shared tactic tests run unchanged.

`Tests/PrimitiveArrays.cs` checks compiled loads and stores for twelve primitive integer
element types against runtime results and certified checked execution. It also covers length,
helper calls, aliases, returned arrays, named null/bounds faults and unsupported array forms.
Independent changes to load width or signedness must fail the Lean scalar certificate.
`Tests/PrimitiveArrays.lean` covers empty and null arrays, signed and native indices,
initialization, authority, invalid extents, local storage and neighboring-byte preservation.
Both run in the evidence suite.

`Tests/ArrayElementReferences.cs` checks compiled `ldelema` returns, helper reads and writes
against runtime behavior, preserving neighboring contents and rejecting a forged element type.
`Tests/ArrayElementReferences.lean` covers null, empty and out-of-range accesses, expired
references and address formation without granting memory authority. Both run in the evidence suite.

`Tests/ReadOnlyArrayReferences.cs` inserts real `readonly.` prefixes into compiled fixtures,
checks returned and locally stored references, and proves that caller stores fail despite
writable backing memory. It rejects independently forged writable evidence, separated prefixes
and branches that skip a prefix. `Tests/ReadOnlyArrayReferences.lean` also checks alias updates,
read access and rejection of an adapter that would remove the restriction. Both run in the
evidence suite.

`Tests/StaticScalarValues.cs` compares 16 compiled readonly-field loads with the runtime,
covering integer widths, Boolean/Char, native integers, signed/unsigned enums, helper
initialization and copies. It rejects missing initialization assumptions, mutable fields,
repeated stores, branches and address-taking during initialization. Independent Lean checks
reject forged scalar signedness, width and literal evidence. It runs in the evidence suite.

The repository pins .NET SDK **10.0.403** and Lean **4.35.0**. The checks below cover semantic behavior, extracted contracts, artifact integrity and rejection cases.

```sh
lake build
dotnet run --file scripts/Test.cs
```

The regression runner covers **54 check groups** across twenty-three test partitions. This includes initial CLI proof selection and theorem output, an actual addition-to-subtraction source edit and rebuild, recovery using settings retained after the failed proof, the invalid-memory-access theorem, and the integer opcode, narrow-storage and primitive-operation matrices. The CLI group also passed separately against an isolated installation of the packaged .NET tool before the integer opcode extension.

The runner builds the independent assemblies and the CIL library, then prepares a source-keyed, kernel-replayed library for verification. CI rebuilds from sources; local runs may reuse a cache entry whose receipt binds its key and manifest. The library is checked by its trusted manifest digest and read in place: every proof still compiles and undergoes kernel replay in a new private session package that requires the library as a path dependency, so Lake writes only below that session. File-based C# apps provide the test runner, verifier and metadata fixture generator. Metadata tooling uses the same pinned Mono.Cecil version as the extractor; the F# example assembly also uses pinned FSharp.Core.

CI prepares the certified library once per workflow attempt and passes its immutable artifact ID, the run that uploaded it and its manifest digest from the producer job to the suite jobs. The producer first looks for a library already certified by a run of the same commit or by the main push of the checkout's first parent. Their own trusted code built that library and printed its digest, so the digest is read from the donor job's log, never from the artifact. `PrepareLibrary.cs --reuse` then rechecks the library key and source binding and kernel-replays the library; any mismatch, or no donor, builds from source. It does not restore compiled libraries from the GitHub Actions cache: a cache's source key and self-described file hashes cannot authenticate the native auditor or establish that compiled modules came from those sources.

`dotnet run --file scripts/PrepareLibrary.cs -- <output-directory>` requires an empty or absent destination and publishes a freshly built library through a staging directory. Explicit reuse uses `--reuse <trusted-manifest-sha256>`; obtain this digest independently from a trusted producer, never by hashing the restored manifest itself. Missing or invalid reuse evidence fails without replacing the destination. Rebuilding an existing library requires a separate output directory. `Tests/LibraryCache.cs` covers substituted auditors and compiled modules with regenerated manifests, missing producer digests, and preservation of unrelated destination files.

When only Lean sources changed, `--incremental <donor-directory> <trusted-manifest-sha256>`
authenticates every donor file before reusing its Lake build traces in a private copy. The runtime,
compiler, kernel checker and build configuration must match. Changed and removed modules lose their
compiled artifacts; Lake checks the current source hashes and rebuilds the dependent closure.
The native auditor is relinked, every resulting module is kernel-replayed, and canonical fingerprints
are regenerated before a new source-bound manifest is published. CI tries this after exact reuse,
then falls back to a cold build if incremental preparation fails. `Tests/LibraryIncremental.cs`
covers artifact tampering, incompatible identities/configuration, source removal and copy isolation.

A Windows run with an `OleanAudit`-only comment edit rebuilt that module, its native object and the
auditor executable: compilation took 4.31s, full replay 11.75s, fingerprints 7.89s, and total
preparation 32.43s. Exact reuse took 12.36s. The donor's cold compilation on the same host/toolchain
took 189.40s during fixture setup; that setup overlapped other short validation work, so this is not
a controlled paired timing. All compiled module-part hashes matched the donor after the comment
edit; the new certificate bound the changed source. These are local library timings, not full CI
job measurements.

`Tests/LibraryReplayCoverage.cs` uses a small synthetic producer manifest with a valid aggregate
and an invalid theorem in a separate module. Both joint replay and its external-checker fallback
must reject that declaration; checking only the aggregate is insufficient. The cache fixture runs
this regression alongside the authentication tests.

The runner accepts `--suite <name>` after `--`, with names `core`, `cli`, `integer`, `narrow`, `primitive`, `division`, `checked`, `conversions`, `native`, `arguments`, `layout`, `copy`, `bits`, `enums`, `nested`, `instance`, `constructors`, `fsharp`, `math`, `divrem`, `unsafe`, `blocks`, `generics`, `loops`, `contracts`, `evidence`, `scaling`, `excluded`, `identity`, `labels`, `names`, `symbols`, `workspace`, `templates`, `callers`, `construction`, `outcomes` and `audit`. These partitions cover the same check groups as the full command and can run concurrently in separate checkouts. Each partition builds its own prerequisites (in CI, one job builds the extractor and example assembly with `--build-tools` and suite jobs set `LEANCIL_PREBUILT_TOOLS=true` to use them), retains fresh Lean proof checking and writes `artifacts/test-results-<suite>.json`; running without arguments checks everything and writes `artifacts/test-results.json`.

| Coverage | Result |
| --- | --- |
| Profile-parametric templates | Compiled AVX2/SSE4.2 dispatch helper, one generated template proof on three profiles, renumbered managed callees, exact per-pc equations, independent kernel replay, and wrong flag/callee/branch/equation, stale source and metadata rejection |
| Cyclic control flow and termination | Universal checked countdown proof for every `uint`, including zero and maximum value; a counted loop proved through its helper's contract, unchanged for a reimplemented helper and rejecting a discarded result or double count; a loop that returns or raises its helper's exception after earlier calls, proved for every pair of `uint`s from the helper's outcome contract, unchanged for a reimplemented helper and rejecting another exception type, a nondecreasing measure, a non-inductive invariant and a wrong specified exception; a buffer fill loop proved to write exactly `count` words for every nonnegative count, with four runtime comparisons and shifted or skipping stores rejected; 17 runtime comparisons; incorrect implementation rejected under the unchanged contract; infinite loop proved to exhaust every fuel budget; backward switch, native arithmetic and fixed-feature loops checked; eight malformed or unsupported fixtures rejected |
| Generic method specialization | 125 C#/F# runtime comparisons, six universal identity proofs, six reference checks, twelve metadata/recursion rejections, wrong-implementation rejection and provenance tamper detection |
| Block memory and alignment prefixes | 251 checks; ten malformed-prefix/type cases rejected; universal out-of-bounds fill rejection |
| Layout-based Unsafe helpers | 418 checks across 19 element types and all three managed offset overloads; ten malformed generic calls rejected |
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
| `sizeof` on pointers, managed references, objects, strings, arrays, double, auto layouts and malformed sequential field offsets, reference-containing structs and generic layouts | Eleven intended extraction rejections; no Lean extraction produced |
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
| Unsupported array allocation | Explicit extraction rejection |
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

The addition theorem proves modular arithmetic correctness for arbitrary 64-bit inputs in the checked execution model. The unsigned-short theorem proves reduction modulo 65,536 for arbitrary 32-bit inputs. The invalid-access and expired-reference theorems classify faults and rule out successful execution for every fuel budget. The subtraction theorem independently refutes the intended addition result. Other example claims have the quantifiers and inputs displayed in their theorem statements; concrete examples do not establish universal method correctness.

All audited example theorems use only the permitted standard Lean axioms, if any. No new axioms, `sorry`, `admit`, native proof evaluation or unproved summaries were added. See [the trusted base](SOUNDNESS.md) for runtime and extraction assumptions.

Machine-readable results are written to `artifacts/test-results.json`; each successful proof produces an identity-bound `verified.json`. These generated files are reproducible outputs and are not committed. Consumer-project integration and broad .NET runtime coverage are outside these validation results.

Typed copy validation: 648 runtime result/byte-copy checks passed across 18 primitive, struct and vector types, including self-copies. The universal UInt64 copy contract passed and rejected reversed source/destination operands. Four unsupported/forged type-token cases were rejected during extraction. Ten semantic tests cover initialization, permissions, lifetime, GC-sensitive storage, bounds, null references and partial overlap. The generic copy snapshot theorem and the full Lean library/semantic/automation build passed.

Portable helper validation: 7,200 comparisons with actual .NET results passed, covering power-of-two boundaries, zero/all-ones values, signed boundaries and negative/oversized rotation counts. Universal 64-bit rotation round-trip and integer-logarithm proofs passed with only approved Lean axioms; incorrect implementations failed the unchanged contracts. Nine malformed/unsupported runtime calls were rejected before extraction. Semantic tests reject incorrect arity, widths and operand types.

Enum validation: 378 runtime comparisons passed across all eight underlying integer types, flags, calls, fields and typed storage. The universal flags proof passed and rejected an incorrect implementation. Eleven malformed metadata cases were rejected.

Nested struct validation: 123 runtime/layout comparisons passed, including sixteen packing combinations. A universal nested snapshot proof passed and rejected an incorrect implementation. Seven malformed layouts and seven semantic memory-fault cases were rejected.

Struct instance-call validation: 96 runtime comparisons passed, including short and full argument encodings, by-value copy isolation and direct constructor calls. A universal instance store/load proof passed and rejected an incorrect implementation. Four malformed metadata cases were rejected.

Struct construction validation: 56 runtime comparisons passed, covering packed and nested structs, chained and parameterless constructors, zero-initialized storage and checked arithmetic faults. A universal constructed-value proof passed for every 64-bit input; an incorrect constructor result failed the unchanged contract. Five malformed constructor cases were rejected. Semantic tests cover zero-sized construction, missing arguments, zero initialization and a non-void constructor result. The full 125-job Lean library, semantic and automation build passed.

F# validation: 324 comparisons with actual .NET execution passed for addition, unsigned branching, managed calls, mutable structs and by-reference stores. The existing addition, store/load and constructor contracts passed unchanged against the F# assembly. Subtraction failed the addition contract, and a list-returning function was rejected during extraction. These examples require no F#-specific CIL semantics or proof shortcuts.

## Contracts and extraction evidence

`Tests/StackAllocation.cs` extracts compiled pointer and span stack allocations, checks results
with and without localsinit, rejects uninitialized reads and escaped storage, and checks
insufficient-budget failure. Mutating the emitted initialization flag is rejected by the Lean
certificate. `Tests/StackAllocation.lean` covers alignment, repeated allocations and expiry;
`Tests/StackAllocationEvidence.lean` rejects forged flags, injected allocations, extra stack
items and non-native 64-bit size operands. These run in the `evidence` suite.

`Tests/ConstrainedCalls.cs` checks compiled implicit and explicit struct-interface calls, including
mutation through the receiver, and rejects forged generated call targets and malformed prefix,
branch and interface-constraint metadata. `Tests/ConstrainedResolution.cs` checks the extractor's
resolution rules; `Tests/ConstrainedEvidence.lean` independently checks Lean resolution, target,
signature, ambiguity and prefix rejection. These run in the `evidence` suite.

The core and universal-contract suites cover checked execution and memory preservation. Choose and GenericIdentity preserve arbitrary caller memory exactly; Struct preserves preexisting caller memory under its well-formedness hypothesis. Each unchanged contract rejects its incorrect compiled implementation. Countdown validation covers original instructions, inserted NOPs and reordered blocks, and rejects wrong results and nontermination.

Extraction evidence validation passed 74 Lean regressions, 34 compiled certificate fixtures, 29 generated-evidence mutation rejections, and mandatory-certificate positive/negative checks. All six CLI checks passed, including kernel replay of imported helpers and rejection of unchecked direct/transitive proofs. `Tests/ImportEvidence.lean` accepts an external call into a matching import slot and rejects a forged identity, parameter count, receiver or result shape, a wrong emitted argument count, a slot index inside the program or past the table, constructor and generic sites, and managed or non-call sites reaching the import range; the certificate audit also rejects a certificate over a different import table. These tests do not establish full raw-CIL/runtime correspondence.

The native extraction suite passed 2,511 runtime comparisons and kernel proofs, its universal addition contract, 60 ambiguous mixed unsigned-branch rejections and five metadata/profile rejections. Separate pinned .NET 10.0.0 probes on x64 and ARM64 each passed 3,600 admitted cases; 500 rejected cases retain 38 historical model divergences. Full JIT optimization produced identical per-case results. See [native evidence](evidence/native/README.md) for exact provenance and reproduction commands.

Memory-view equivalence covers access, writes and subsequent checked execution, including calls, constructors and frame cleanup. At 128 alternating stores the benchmark retained one view rather than 129; median local kernel-reduction time was 5.6s versus 17.7s over three runs, including startup and shared-machine activity. These timings are illustrative, not a performance guarantee.

The initialized-types end-to-end test and four mandatory-certificate audit cases check that verification reports record both the schema-3 extraction audit and initialized-type assumptions.

## Proof automation

The checked proof APIs share execution traces, frame-setup effects and instruction
contracts. Their validity fields retain the required well-formedness and input
validity hypotheses. See [Writing checked proofs](PROOFS.md) for API locations
and examples.

`Tests.Automation` checks an eight-instruction arithmetic method with symbolic
inputs and arbitrary caller memory, using `cil_checked_steps`. Its instruction
sequence is `arg, arg, const32, shl, add, const32, gtu, ret`; the theorem's axiom
assertion permits only `propext` and `Quot.sound`. The same module checks both
paths of a symbolic branch using a supplied truth hypothesis, and verifies that
failed candidate summaries do not escape their transaction. Memory and static
dispatch facts retain abstract bitcast results in inferred stacks; a conjunction-wrapped
store fact exercises the generic dispatch fallback.

`Tests.LegacyFeatures`, imported by `Tests.Automation`, uses only the reference
interpreter tactic import. It checks enabled and disabled symbolic features from
caller facts, plus a concrete feature reduced to its profile field. `cil_steps`
keeps symbolic `FeatureProfile.evaluate` applications folded, as checked stepping does.

`Tests.StoreFacts` checks symbolic carry and borrow stores whose write facts
state `a + b + c`, `a - b - c` and the flag words in source form, through both
`cil_checked_steps` and `cil_contract_steps`. A wrong stored value, address or
source memory leaves the run stuck at that store, with the exact unsolved goal
asserted.

`Tests.Segment` composes the UInt256 Add Vector128 eight-op reference prefix and Multiply
AVX2 input stages at positions 44–56. Formation, checked loads and stores, intrinsic
availability and exact permutation semantics remain premises. Two actual vector writes
frame all other numeric snapshots using separated homes. Negative cases reject aliased
homes, hidden indirect writes, changed endpoint states, fuel costs and mismatched composition
positions or assertions, and placements from a different body or end boundary. Every new theorem is kernel checked with its axiom set reported.
`Tests.CodeAt` steps a segment of an abstract body at a symbolic start from the
lookups its `CodeAt` placement yields, with the error asserted when stepping has no
placement, hands that segment theorem the middle of a larger placed region, closes a
concrete placement by `rfl` and refutes a shifted one and one running past the code.
It composes adjacent placements and splits them back with `cons_iff`, `take` and
`drop`, including past the segment's end, and recovers the positional
`leading ++ segment ++ tail` form from a nonempty placement alone, proving the bound
`exists_eq_append` needs by placing the empty segment past the end of a body.

`Tests.MethodEmbedding` checks transport of checked executions to actual method
bodies with mapped program counters, and with trailing dead reference and span locals dropped,
beside kept opaque vector locals too. It checks empty and unmodeled span slots, both mutabilities
and every supported width, and rejects unsupported widths and scalar span initializers.
It rejects numeric dead locals, in the kernel and
in the tactic, and non-trailing ones, and still reports a changed live instruction
under dead locals; `Tests.OutcomeEmbedding` checks transport of
named exceptions and outcome contracts, the relocated fault pc, and that changed
throws, unsupported execution and fuel exhaustion do not transfer. `Tests.AggregateSetup` and `Tests.Semantics`
cover frame setup and interpreter behavior. `Tests.RetainedNumericLocals` keeps dead
numeric declarations before and after a live local, transfers exact-memory executions
and named exceptions through nested allocating calls, and checks that deleting a
numeric local changes the allocation watermark and fails ordinary embedding.
`Tests.AllocationRenaming` checks private allocation holes, extending identity maps, relocated
numeric homes and distinct activation labels. `Tests.AllocationExecutionRenaming` uses the
concrete allocation-refinement API to transfer scalar results, caller-memory prefixes, a
complete method contract and named exceptions through nested calls followed by dynamic
allocation, including a child that reads its initialized numeric local and nonzero private
homes before, between and after retained declarations. A generic theorem covers every
`InitializerFits` kind/value and arbitrary well-formed caller memory with bounded statics;
a concrete checked read observes the private initializer's bytes. It independently
checks different source/target allocation counters and rejects changed retained initializers,
wrong initializer kinds, overflowing bytes, aggregate lengths, unspecified vectors, invalid spans,
unchanged local operands, changed call targets and an exhausted stack quota.
Allocation-renaming proofs reuse checked step equations, and IntegerMath groups boundary
proofs without changing their final statements. See the measured compilation and proof-work
reductions in [Proof work measurements](performance/ProofWork.md).
The extracted-loop suite checks
universal countdown termination, NOP/reordered variants, runtime comparisons,
incorrect/nondecreasing loop rejection, a counted loop composed through its
helper's contract and reused for a reimplemented helper, a loop that returns or
propagates its helper's named exception, a buffer fill proved as a sequence
property, feature selection, infinite-loop fuel
exhaustion, backward switch and malformed-input rejection.

`Tests.LoopOutcome` derives the normal-only loop induction, loop call and `Ensures`
as the `none` instances of the outcome rules, and proves that unsupported
execution, invalid state, fuel exhaustion, normal return and a different
exception never satisfy an expected loop exception.

`Tests.ContractConsequence` derives public method and outcome contracts from proved
internal ones without re-executing the callee, composes callers through the derived
contracts, and proves that an unjustified stronger postcondition, a weaker
precondition, a smaller footprint and a changed exception type each fail both the
refinement premises and the derived contract on a concrete input. Its forwarders inherit
their callees' contracts through `MethodContract.Holds.forward` and `forward_out`: `Sum`,
`SumSwapped` and `AddFrom` pass `AddTo` its arguments in order, swapped and reversed;
`SumDiscard` inherits `AddFlag`'s contract with an uninitialized out local, and `CopyTo`
inherits `AddFrom`'s with a zeroed local, a callee region footprint inside its own and an
`Apart` fact from the local's freshness; `IsZeroForward`, `IsZeroIgnoring` and
`IsZeroSecond` re-narrow `IsZero`'s boolean, the last two skipping an argument; and
`IsSetForward` passes a boolean through a narrowed load. Rejected are a body whose loads
differ, a selection that passes one argument twice, a result or load outside the narrow
range, and two false contracts: `IsZeroSecond` as if it loaded its first argument, and
`IsZeroIgnoring` with a dangling unused argument.

`Tests.InvocationCertificates` builds invocation certificates from a computed
invocation and from a computed run, keeps them through a certified contract and
its refinement, proves a caller whose postcondition is the visited-state clause of
its callee's certificate, through a certified callee and through a callee without
a precondition, and refutes a contract from the returned values of a computed run.
`Tests.ValidCallTransport` carries `ValidCall` through writes, frame entry, memory
kept below a watermark and a call confined apart from the inputs, and shows that a
confined call over an input can revoke its read authority.

`Tests.ConfinedFootprints` checks footprint coverage and preservation through
`Confined`. `Tests.LocalSnapshots` keeps vector, int32, byte and narrow locals
known across stores, overwrites, writes elsewhere and confined calls, and steps
a load from a snapshot fact. `Tests.BufferContents` checks typed buffer
contents: fills and in-place transforms of any length, unchanged neighbouring
bytes and sibling slices of one allocation, a producer that extends its prefix
while its room stays unreadable, empty buffers at invalid and sentinel
positions, and rejection of uninitialized, past-end, overlapping, unjoined and
stale contents.

`Tests.ProfileContract` proves a contract for a method that tests AVX2 once, under
x86-64-v3, and carries it to x86-64-v4, to v3 without 256-bit acceleration and to every
profile with AVX2 on. A raising method's outcome contract carries over too, in outcome,
CLR-named and descriptor-indexed forms, with agreement decided from the flags the program
reads. The baseline profile, with AVX2 off, fails both the agreement check and the contract,
and turning off one of the four flags an AVX-512 DQ multiply needs fails the check.

`Tests.InstructionEquations` checks that `cil_instruction_equations` states one
equation per pc of a body over two feature flags and a callee index, keeping each
feature test as an `if`, and of bodies with no parameters, with implicit and
hypothesis parameters, and composed with `++` and `List.replicate`; that
`cil_lookup` fetches through them from a sealed body; that facts or literal flags
decide the test, in lookups and in a checked run; and that a run proved over the
flags binds two profiles. A body whose length depends on a flag, at its first pc
or a later one, is rejected with nothing declared.

`Tests.InterpreterEquations` checks that each shared equation lemma is stored by
its LeanCIL module rather than rebuilt by the importer, and that a tactic macro
naming `CIL.step.eq_def` elaborates.

`Tests.SimdLanes` checks the SIMD lane lemmas as a multi-limb routine uses them: the
carry and borrow cascades built from intrinsic comparison masks reproduce 256-bit sums
and differences for every input. The 512-bit forms cover all eight lane carry-ins and the
outgoing carry or borrow; boundary fixtures propagate across all eight lanes and reject an
unshifted generate mask. Broadcast all-ones and operand-swapped AVX-512 greater-than
sources feed the same 256-bit cascade. Tests include a carry across an all-ones lane where a
single repair hop is wrong, and 128-bit sums and differences follow from their lane
carries. Each intrinsic equation (lane add, multiply, equal, unsigned and signed compare,
`MoveMask`, shifts by immediate and by vector count, permute, sum and even-lane multiply)
rewrites a packed or symbolic operand to its lane values, the bitwise lane projections
cover a mask blend, and concrete 256-bit values are checked by kernel evaluation. A
method steps through a shift and an even-lane multiply with those lemmas as facts.

Run the focused Lean targets and extracted-loop suite with:

```sh
lake build CIL Tests.Automation Tests.MethodEmbedding Tests.RetainedNumericLocals Tests.AllocationRenaming Tests.AllocationExecutionRenaming Tests.OutcomeEmbedding Tests.AggregateSetup Tests.Semantics Tests.InterpreterEquations Tests.MethodIdentity Tests.StructuralLabels Tests.DebugNames Tests.MethodContract Tests.ConstructContract Tests.OutcomeContract Tests.Imports Tests.LoopOutcome Tests.ContractConsequence Tests.InvocationCertificates Tests.ValidCallTransport Tests.ConfinedFootprints Tests.LocalSnapshots Tests.BufferContents Tests.Linking Tests.StoreFacts Tests.ProfileContract Tests.InstructionEquations Tests.CodeAt Tests.Segment Tests.SimdLanes
dotnet run --file scripts/Test.cs -- --suite loops
```

The loop suite builds a fresh verification library and performs kernel replay
as part of extracted-loop verification. Use the full test command at the top
of this document for the complete verification suite.

When changing proof tactics or shared contracts, measure fresh elaboration of
the library and its consumers, compiled artifact size, CPU time, peak process
memory and kernel replay separately. Compile identical consumer sources against
both revisions and alternate serial runs with prebuilt dependencies on the same
machine. A smaller compiled proof alone does not establish a speed or memory
improvement. Preserve the kernel replay, axiom audits and negative regressions.

## Store view reuse

Stores reuse existing read permissions when they already cover the written range, including coverage spread across multiple views. The `write_run_equivalent` theorem proves that replacing the previous always-prepending write preserves any subsequent checked execution: returned values, exact faults, allocation state, bytes and permissions. `Memory.Equivalent.run` and `.invoke` cover branches, calls, constructors and frame cleanup.

Run `dotnet run --file scripts/BenchmarkViews.cs -- --stores 128 --repetitions 3` to compare kernel reduction against the previous write implementation. The defaults are 64 stores and 3 repetitions; results and per-run logs go to `artifacts/ViewBenchmark`. In a local Windows run with Lean 4.35.0, 128 alternating stores retained 1 view instead of 129; median elapsed time was 5.6 seconds versus 17.7 seconds. These timings include process startup and shared-machine activity; view counts are checked by kernel reduction.

## Export suite selection

`dotnet run --file Tests/ContractExport.cs` runs every export cohort once.
`dotnet run --file scripts/Test.cs -- --suite all` runs the same export leaves
once with the other suites. Each export leaf has a fresh SDK and proof
workspace. Full verification keeps fresh extraction, source audit, independent
kernel replay, and all report and artifact checks.

Run one leaf with `dotnet run --file scripts/Test.cs -- --suite NAME`:

| Name | Cases |
| --- | --- |
| `exports` | Production, wrapper-True rejection, generic/virtual/static-value restrictions and caller reuse |
| `exportsprotected` | SDK-built protected static export, separately compiled derived caller and rehashed visibility mismatch rejection |
| `exportsaudit` | Proof-source and compiled-wrapper callback mutations |
| `exportsresolution` | Same loaded files and changed loaded module |
| `exportsfullconsumer` | Explicit and repeated consumer full verification; stale-report removal; caller and library proof-build stages required separately for each invocation |
| `exportsfullordinary` | Ordinary caller full verification, requiring its direct proof check and the imported proof build |
| `exportsfullpair` | Two imported slots from one bundle, requiring both imported proof builds and the caller check |
| `exportsfullchecks` | Bundle, DLL, closure, statement digest and caller-premise rejection |
| `exportsfulltheorems` | Wrong producer theorem statement and definition |
| `exportsfullcomposition` | Transferred macro cannot replace the composition theorem with True |
| `exportsmutationordinary` | Executed ordinary caller artifact mutation |
| `exportsmutationconsumer` | Executed consumer caller artifact mutation |
| `exportsmutationsource` | Executed consumer caller source mutation |
| `exportsmutationshadow` | Executed original-root module shadow |
| `exportsstatics` | Standalone modular static exports with their own SDK setup and existing assertions |
| `exportsfullstatics` | The same fixture with `--full-composition`: forced full verification of app and library tables with one local index and one table shared by two imported slots, run after a repeated ordinary verification restored a receipt; a republished bundle with forged static records fails in preflight and a re-certified changed table fails the independent library proof; a Top → App → library chain independently composes the table reader with its static-world premise |
| `exportstransitive` | App → A → B and a four-node diamond where A and C share B; full mode rechecks each selected export despite warm receipts, rejects changed deployment pins and cycles before building, rejects forged dependency composition, and detects B changing staged A before A builds |
| `exportstransitiveoutcomes` | App → C → A → B independently preserves normal returns and the named exceptional outcome through three forwarders |
| `exportsdiscovery` | Real producer SDK/publication bootstrap, then the unchanged six-argument discovery fixture |
| `exportstyped` | Standalone closed-generic and imported-layout fixture with its own SDK setup and existing assertions |
| `exportsderived` | Standalone derived public contracts: `Holds.weaken` exports, sidecar-only callers, refuted weakenings |
| `exportsinitialized` | A static-readonly struct library exports a named initialization premise; its caller retains the scoped premise, malformed descriptors reject, and full verification remains unavailable |
| `exportsprofiles` | One family theorem across three profiles, independent full composition, outcome families and scoped initialization premises; disagreeing flags, unequal programs, malformed selections, forged audit declarations and compiled-reference mutation reject |

The base coverage ledger has 49 cases: 22 core, 3 protected, 2 callback, 2 resolution and
20 full cases. Each leaf rejects an omitted, repeated or unexpected completion.
The artifact-mode rejection follows real consumer positives so it still checks
removal of an actual successful report. The default eight-argument
`Tests/FullImportVerification.cs` invocation runs resolution and all full cohorts
once. Its optional `--cohort NAME` selects one full cohort. Unknown, missing or
duplicate selections fail before fixture setup.
The full plan contains only its ten explicit base cohorts. Later standalone
statics, fullstatics, transitive, transitiveoutcomes, discovery, typed, derived, initialized and profiles suites cannot enter that plan.
The registry now has 23 leaves. `exportsstatics`, `exportsfullstatics`, `exportstransitive`,
`exportstransitiveoutcomes`, `exportstyped`, `exportsderived`, `exportsinitialized` and `exportsprofiles` run directly, with no core export bootstrap
or nested post-call. Their fixture assertions are
separate from the 49 base case IDs. A standalone fixture cannot use an empty
base completion ledger to claim coverage.
`exportsdiscovery` records one separate `discovery.fixture` completion after
the actual child succeeds. It does not count individual child behaviors in
the 49 base cases. It builds the producer library and creates real proof
packages and publication. The child builds, extracts and verifies its own
caller. It needs no baseline caller artifact or verified report. The discovery
leaf runs no core caller verification, restrictions, callbacks or full cases.
The typed leaf explicitly owns its fixture and five input proof/interface
modules. Shared model and proof dependencies retain their existing owners.
The derived leaf likewise owns its fixture and the five `Derived*` interface,
producer and caller modules in `Tests/ContractImports`. It proves exact internal
method and outcome contracts on the actual extraction and exports public ones
derived only through `Holds.weaken`. Callers verify from the sidecar alone, on
normal and named-exception paths. Stronger posts, weaker preconditions, smaller
footprints and renamed exceptions are refuted on the same extraction; at the
exporter, one renamed exception fails only its refinement proof.

New cohort durations are unmeasured. The existing CI caps remain 90 minutes
for imports, 120 for each exports leaf, and 30 for other suites. The matrix
still uses at most eight runners. Run the resource-bounded routing tests with
`dotnet run --file scripts/TestSelectVerification.cs`; they need no Lean build
or fixture SDK project. Full integration results come from the CI leaf jobs.

`Tests/PointerOperations.cs` compares seven compiled pointer methods with .NET: int32/native
byte subtraction, pointer differences and four unsigned orderings. It independently forges
subtraction as addition and requires the Lean scalar certificate to reject it. The Lean fixtures
cover negative offsets and differences, end positions, readonly preservation, every unsigned
branch, and null, cross-allocation, invalid-position and signed-comparison rejection.

Managed-call proof construction is covered by `Tests/ExtractionGenerics.lean` and the
15 generated generic-method samples in `Tests/GenericEvidence.cs`. Direct tactic rejection
checks cover changed signedness, assembly scope, generic arguments and argument count.
The fixed three-method int256 scalar Equality extraction retains every public certificate
proposition and all program/metadata definitions. Replaying every generated theorem reduces
kernel work from 36,782,462 to 32,494,315 raw heartbeats (11.7%); the structural proofs introduce
additional auxiliary theorems, increasing the replay count from 169 to 181. These are kernel
work measurements, not full consumer build or end-to-end verification timings.

Shared runtime-scope encoding keeps the same 181 Equality theorems and reduces their replay
from 32,494,315 to 26,201,571 raw heartbeats (19.4%). Including all 43 generated data definitions
and the changed scope definition plus its equality theorem gives 32,502,723 versus 28,123,894
raw heartbeats (13.5%). The latter includes the one-time scope construction and equivalence
cost. Actual extractor output matches the measured source. Generic evidence mutations also
reject altered runtime versions and public-key tokens; no scope comparison is relaxed.

`Tests/GenericEvidence.cs` also checks exact external-call identity sharing, repeated emission,
pruned-only identities and Unicode/escaped characters. Changed bytes, versions and tokens fail
the generated equality proof. Replacing a raw target with another correctly encoded identity,
or changing its emitted intrinsic, still fails the unchanged division certificate. Existing
specialization and raw/translated metadata rejection cases remain enabled.

External-call byte sharing was measured against the parent extractor on fixed compiled inputs.
The following counts replay every generated definition, theorem and auxiliary proof, including
all new byte constants, UTF-8 proofs and exact equality proofs:

| Fixed input | Before raw heartbeats | After raw heartbeats |
| --- | ---: | ---: |
| int256 scalar Equality, three methods | 26,209,754 | 21,765,190 |
| `DivisionIntrinsics.UnsafeEquals`, x64-v3 | 28,184,308 | 22,519,141 |
| `VectorFields.Reinterpret`, x64-v3 | 15,047,351 | 14,850,377 |
| `Arithmetic.Add`, scalar, no calls | 1,397,796 | 1,397,796 |
| Feature getter only, scalar | 12,688,673 | 8,715,896 |
| `UnsafeLow` through one managed caller, scalar | 25,337,727 | 20,917,175 |
| Eight different division intrinsic helpers, x64-v4 | 379,503,016 | 257,862,158 |

The last input calls `And`, `Or`, `Xor`, `AndNot`, `ShiftLeft`, `ShiftRight`, `Less` and `Greater`
once each and sums the results. Its nine-method extraction has thirteen unique external
identities, including eight operator identities used only once. Counts include the new
declarations (582 before, 647 after); sharing does not require repeated source call sites.
Source checking and independent kernel replay both pass. These are deterministic kernel-work
measurements, not isolated wall times or end-to-end consumer verification improvements.

The core `Tests/AllocationImports.cs` fixture checks that the CIL umbrella omits allocation
refinement, builds both explicit allocation acceptance modules, and jointly replays every
additional imported module. The current closure contains 49 production and two test modules;
all remain mandatory checks while ordinary consumers avoid loading their 197 MiB of oleans.
The compiled namespace audit checks their theorem axiom closures even on warm builds and binds
the audited paths and module bytes to those replayed. An isolated theorem depending on
`sorryAx` passes kernel replay but must fail that audit; build output is also checked.

Extraction bookkeeping indexes declaration names, imported assembly identities, imported call
slots, batch proof modules and aggregate layout names. Component imports retain declaration
order; raw layout positions and emitted layout constant positions have separate indexes.
`Tests/ConsumerSupportCandidates.cs` checks dependency ordering and conservative references in
literal text, while `Tests/InstructionIndexes.cs` checks nested layout ordering and absent types.
The transitive import regression also checks identical imports before rejecting ambiguous versions.

On the Apple M4 with .NET 10.0.401, splitting synthetic one-dependency method chains took these
median times over seven warmed runs, including index construction and component hashing:

| Methods | Declaration scans | Indexed dependencies |
| --- | ---: | ---: |
| 128 | 1.23 ms | 0.46 ms |
| 512 | 13.79 ms | 1.94 ms |
| 2,048 | 113.59 ms | 6.46 ms |

Each input contains two declarations per method and refers to the previous method's value.
Both implementations produced identical component sources and aggregate imports. A separate
24-request extraction matrix (eight entries across scalar, x64-v3 and arm64-advsimd profiles)
retained all 48 generated Lean file hashes. These measure component splitting and output
stability, not end-to-end proof or CI speedups.

The certificate successor index consumes the source list once to build its balanced tree,
replacing repeated length/take/drop traversals. `Tests.FlowIndex` covers empty and singleton
inputs, odd/even partitions, missing certificate states, out-of-bounds lookups and untouched
suffixes. `FlowIndex.build_spec` proves prefix consumption and exact list lookup equivalence.

`Tests/FlowIndexScaling.lean` retains the former builder as a benchmark reference. It constructs
indexes and checks every target in reverse order, including the first out-of-bounds position,
using `decide +kernel`. On Apple M4 with Lean 4.35.0, leanprof measured these theorem-checking
heartbeat counts (kHB); they include elaboration and kernel checking, not whole-suite timings:

| Entries | Repeated list splitting | Consuming builder |
| --- | ---: | ---: |
| 128 | 1,019.05 | 654.46 |
| 512 | 4,749.06 | 2,907.29 |
| 2,048 | 21,825.45 | 12,951.03 |

These fixed workloads reduce checking work by 36–41%. Tree construction is linear in list
cells; arbitrary target lookup remains logarithmic. The existing feature and scalar validators
continue to use the same proved optional-lookup interface.

The shared state-pairing proof also uses explicit list-shape cases instead of broad simplifier
search. Its statement is unchanged, and its checked axiom set is reduced to `propext`.

Region closure now builds an ordered map of each method's minimum starting pc, visits program
methods sequentially, and checks each included body once. It skips absent region entries and
preserves region membership for absent callees: execution validity is a separate obligation.
The equivalence theorem covers the former checker exactly, including duplicate starts and
out-of-range pcs. `Tests.RegionRun` exercises those cases; `Tests/RegionScaling.lean` is a
standalone before/after workload for `leanprof elab --heartbeats`.

On Apple M4 with Lean 4.35, kernel-decision declaration work for a single full-method region:

| Nops before return | Former checker (kHB) | Indexed checker (kHB) |
| --- | ---: | ---: |
| 128 | 2,674.46 | 214.01 |
| 512 | 38,908.36 | 742.40 |
| 2,048 | 608,701.24 | 2,855.94 |

Measurements include index construction. They show the removal of quadratic instruction
lookup; they do not estimate total CI savings. The separate `all3_zip_states` proof cleanup
reduces declaration work from 97,195.29 to 589.64 kHB on the same machine, without changing
its statement. Its axiom set shrinks to `propext`.
Constrained validation uses balanced instruction/reachability indexes and a set of all decoded
branch destinations, including unreachable instructions and switch arms. The following constrained
lowering pass also indexes predecessor instructions; `lowerConstrainedRaw_eq_original` proves
identical output for arbitrary raw bodies, including malformed prefixes. Managed-call validation
indexes both extracted methods and imported slots once per method check. The equivalence theorems
`ConstrainedCallsValid_iff_original` and `ManagedCallsValid_iff_original` preserve the original
list-based rules, including absent entries, import offsets and malformed lengths.
`cil_managed_calls` still uses structural metadata equalities before its kernel-decision fallback.

`lake env lean Tests/CallIndexScaling.lean` compares indexed and list-based checks and independently
replays every theorem, including the auxiliary proof declarations created by `decide +kernel`.
On Windows with Lean 4.35, the dominant auxiliary declarations used these raw kernel heartbeats:

| Workload | Size | List lookup | Indexed lookup |
| --- | ---: | ---: | ---: |
| Constrained validation, reachable nops | 128 instructions | 4,984,847 | 2,045,014 |
| Constrained validation, reachable nops | 512 instructions | 76,557,716 | 9,566,111 |
| Managed calls, each target used once | 128 methods/calls | 2,767,034 | 1,368,097 |
| Managed calls, each target used once | 512 methods/calls | 39,348,863 | 6,135,858 |

The indexed measurements include index construction and length checks; the list baselines measure
only the per-site checks. These isolate lookup costs rather than estimate total CI wall time.
The constrained traversal is O(N log N), plus branch-target set construction and metadata checks;
it no longer performs O(N²) optional list lookups. Imported signature comparisons retain their
existing checks and costs. The registered constrained/import evidence suites also test unreachable
switch-prefix bypass, duplicate switch targets, short reachability and both import-table bounds.
Home discovery and static/opaque-local validation use balanced indexes instead of repeated
linked-list scans. Home discovery collects live stores and addresses once, then retains argument
order while filtering the argument range. Static sites keep the first descriptor at a duplicate
pc. Opaque-local discovery still considers addresses in the complete raw body, including dead
instructions. Equivalence theorems cover arbitrary input lists, including malformed indexes,
duplicate sites and truncated masks; no new assumptions are required.

`Tests.ExtractionHomeIndexes` exercises those boundary cases. The indexed implementations use
`Std.TreeSet`/`Std.TreeMap` for keyed membership and `FlowIndex` for positional lookup. This adds
standard-library tree dependencies to the validators. The public validity propositions retain
their obligations, with explicit equivalence theorems for the indexed checks.

An Apple M4 run of `leanprof elab --heartbeats` measured the following total declaration work
for paired `decide +kernel` proofs (kHB, thousands of raw heartbeats). More than 99% of total
profiled work was in the kernel. Each pair includes constructing its index. The home fixture
has one store per argument; the static fixture has one descriptor per load; the opaque fixture
has equally many vector locals and out-of-range address references, leaving all locals eligible.

| Check | Entries | List scans | Indexed |
| --- | ---: | ---: | ---: |
| Parameter home discovery | 128 | 3,568.83 | 4,674.26 |
| Parameter home discovery | 512 | 53,145.52 | 24,966.14 |
| Static-load shape validation | 128 | 5,402.08 | 5,152.10 |
| Static-load shape validation | 512 | 81,005.04 | 26,628.89 |
| Opaque-local discovery | 128 | 9,601.26 | 7,323.65 |
| Opaque-local discovery | 512 | 124,343.11 | 31,897.40 |

The tree overhead increases work for the smaller home fixture; at 512 entries, measured work
falls by 53%, 67% and 74%, respectively. These isolate the changed checks and do not estimate
end-to-end CI time. Parameter slot lookup and the rest of contract verification are unchanged.

Call and home/static/opaque measurements above were collected for each isolated change before
stacking the linear FlowIndex builder. Combined-stack counts may differ. Managed-call numbers
measure direct kernel decision, not the preserved structural "cil_managed_calls" shortcut.

Region suffix membership makes fallthrough closure automatic: `lower ≤ pc` implies
`lower ≤ pc + 1`. The checker therefore looks up only explicit branch targets and callees.
Its equivalence theorem still covers every instruction, including a final fallthrough beyond
the body; instruction availability remains a separate execution obligation.

On Apple M4 / Lean 4.35, paired `decide +kernel` checks of 32, 128 and 512 methods, each
containing 16 nops and a return and listed from pc zero, took 1,120.60→1,008.90,
5,832.86→5,391.51 and 29,638.99→27,878.92 kHB respectively. These include region-index
construction and show 6–10% less kernel work, not total verification wall-time savings.
Aggregate metadata validation counts module type names once per layout traversal and field names
once per visited type. Duplicate instance/static field names and duplicate full type names still
reject; the counts are rebuilt on each public layout request so later metadata mutations remain
visible. `Tests.InstructionIndexes` includes those rejection and mutation cases.

An isolated Windows .NET 10 scaling fixture used sequential structs with UInt64 fields, warmed
three times, then took the median of seven batches of ten complete layout computations. Index
construction is included: 256 fields improved 1.293→0.158 ms, 1,024 fields 3.753→0.479 ms, and
4,096 fields 49.715→1.829 ms. The duplicate-field check is linear instead of quadratic. These
are layout-validation measurements, not end-to-end extraction or CI estimates. The ordinary
struct extraction retained its generated Lean bytes, and mixed batch-extraction regressions pass.
Template emission groups methods by identity once, indexes template positions and each
variant's method positions, and indexes template callee parameters. Sorted template/callee
order and profile input order remain unchanged; duplicate identities are still rejected before
emission. An absent callee in an excluded profile retains the existing zero placeholder.
`Tests/TemplateIndexes.cs` checks reordered methods, conditional absent callees, deterministic
output and duplicate rejection without compiling Lean.

A Windows .NET 10 Release benchmark emitted two profiles with reverse method ordering and one
call per method. Median times over five measured runs after two warmups, including index
construction, generated text and output writes, were 2.90→1.87 ms at 128 methods, 20.56→6.37 ms
at 512, and 127.10→24.18 ms at 2,048. Combined output hashes matched at every size. These are
isolated template-emission measurements, not end-to-end verification estimates.
Argument instruction validation now shares indexes for argument types and appended home slots.
The home-slot map preserves the first occurrence even for duplicate home lists; missing argument
indexes, hidden home accesses and unsupported replacements remain rejected. Expected home kinds
also use the argument-type index. Exact lookup/check equivalence theorems preserve the existing
semantic consequence statements. Tests in `Tests.ExtractionHomeIndexes` cover these boundaries.

`Tests/ArgumentSlotScaling.lean` isolates the per-instruction checks with one store per argument.
On Apple M4 / Lean 4.35, `leanprof elab --heartbeats` reported:

| Arguments/stores | List lookup (kHB) | Indexed lookup (kHB) |
| --- | ---: | ---: |
| 128 | 8,953.23 | 4,647.67 |
| 512 | 136,907.69 | 24,508.59 |

The indexed measurements include constructing both indexes with the current linear FlowIndex
builder. They reduce measured work by 48–82%; they do not estimate total CI wall time.

Loaded contract libraries index exports by exact identity and certifications by exact
(identity, profile). The production reader still rejects duplicates before constructing either
index. `Tests/ImportIndexes.cs` checks case-sensitive lookup, multiple profiles and the reader's
exact duplicate diagnostics using an otherwise accepted interface.

A Windows .NET 10 Release synthetic lookup benchmark, with one lookup per export and two
certifications per export, measured median batches of 128/512/2,048 exports at
0.369/1.814/22.929 ms with list searches versus 0.031/0.121/0.590 ms with dictionaries.
Dictionary construction is included. This measures the lookup algorithm, not DLL validation,
proof checking or end-to-end import time.

Blocker collection retains ordered lists for sites, entries and call chains while using indexes
for deduplication. Sites use record value equality; entries use exact (signature, profile)
keys; chains use full ordinal element equality, including element boundaries and order.
Findings and reaches have reference identity, so assigning a finding's output ID cannot change
its hash. `Tests/Blockers.cs` checks distinct arrays with equal contents, distinct chain splits,
profile case and first-seen output ordering. The full fixture report matches the former CLI
except for its extractor hash.

A Windows .NET 10 Release collection benchmark inserted each unique site and two-element chain
twice into one finding. After a one-second warmup per implementation/size, median times over
five measured batches at 128/512/2,048 unique sites and chains were 0.093/2.761/35.876 ms for
list deduplication versus 0.021/0.130/0.540 ms for indexed accumulation. Collection construction
is included; indexed measurements invoke the actual accumulator through reflection. These are
collection costs, not admission or complete report-generation timings.
Constrained instruction validation now consumes the raw, reachability and emitted lists together,
retaining the previous instruction and reading the next one from the tail. Lowering likewise
retains the raw predecessor before rewriting it. This removes per-position tree lookup and
construction for sequential instruction evidence while preserving malformed-neighbor and length
rejection. Method-target lookup, branch membership and dispatch metadata resolution keep their
existing checks. Opaque-local enumeration reads each type directly from `zipIdx`; address-set
membership remains indexed. The earlier equivalence theorems retain their statements.

`Tests/StreamingValidationScaling.lean` compares these traversals to the preceding indexed
implementations, using the current linear FlowIndex builder. An Apple M4 / Lean 4.35 run of
`leanprof elab --heartbeats` measured total theorem-declaration work:

| Check | Entries | Indexed positions (kHB) | Streaming positions (kHB) |
| --- | ---: | ---: | ---: |
| Constrained reachable nops | 128 | 1,256.40 | 330.73 |
| Constrained reachable nops | 512 | 5,596.06 | 1,257.34 |
| Eligible opaque locals, no addresses | 128 | 2,248.81 | 1,781.24 |
| Eligible opaque locals, no addresses | 512 | 4,807.78 | 2,599.93 |

These include index construction and isolate positional work. They do not measure dispatch
metadata resolution, full-method proof time or total CI savings. Existing constrained/opaque
regressions pass, with additional trailing-prefix and extra-emitted-instruction rejection cases.

Read-only translation validation and Lean emission now each own a `LayoutContext`, scoped to
one module and architecture. It reuses fully validated root layouts and field/position snapshots
through layout declarations, instruction translation and raw evidence emission. Every new root
still runs the original recursive validator with a fresh active set and recursive cache: warming
a child cannot bypass the 128-level nesting check. Contexts never cross metadata rewrites or
extraction requests, and context-taking helpers reject module/architecture mismatches.

`Tests.InstructionIndexes` checks nested-root reuse, field identity/order, fresh-call mutation
visibility, distinct x64/arm64 vector layouts and nesting rejection after warming a child. A
34-request matrix covering scalar, x64-v3, x64-v4 and arm64-advsimd, including nested vector
layouts and tuple division, retained all 68 generated Lean file hashes.

A Windows .NET 10 fixture compiled a method reading every UInt64 field of a wide struct and
measured complete `LeanEmitter.Emit` calls, including constructing the context. After three
warmups, median times over seven runs were 7.762→1.133 ms at 64 fields, 72.221→4.212 ms at
256 fields, and 531.870→21.939 ms at 1,024 fields. All three emitted source hashes matched.
The baseline already includes linear metadata-name counting. This isolates emission work;
it does not include loading assemblies, the initial admission walk, proof checking or CI.

C# argument translation now builds argument-to-home-position indexes once per method in
validation, emission and exception lint. The original ordered home array still drives evidence
emission. Duplicate inputs retain their first position, missing homes remain absent, and raw
locals are still added to the home position when emitting local-slot instructions.

`Tests.InstructionIndexes` exercises loads, stores, addresses, duplicate homes and missing-store
rejection. Eight argument-processing methods across scalar, x64-v3 and arm64-advsimd produced
48 byte-identical Lean files before/after. A Windows .NET 10 lookup fixture, including index
construction, performs eight passes over reverse-ordered homes plus a missing argument. After
one-second warmups, median seven samples of 25 runs measured 128/512/2,048 homes at
0.0090/0.0306/0.4200 ms before and 0.0021/0.0088/0.0649 ms after. These isolate lookup costs,
not full extraction or CI wall time.
Parameter home discovery enumerates the collected ordered set and filters its members by the
argument bound. It no longer allocates every argument index and performs a tree lookup for each.
The proved list equality retains ascending order, duplicate elimination, out-of-range filtering
and truncated reachability semantics. `Tests/HomeEnumerationScaling.lean` compares both algorithms.

Apple M4 / Lean 4.35 paired `decide +kernel` declaration work, including set construction (kHB):

| Arguments | Homes | Range membership | Set enumeration |
| --- | ---: | ---: | ---: |
| 128 | 128 | 4,674.52 | 4,331.61 |
| 512 | 512 | 24,966.38 | 23,066.91 |
| 512 | 8 | 2,152.66 | 360.60 |
| 2,048 | 8 | 8,246.02 | 1,011.87 |

The dense cases improve 7–8%; sparse cases improve 83–88%. Computing the argument bound still
traverses the argument list. These are focused kernel-work measurements, not total CI savings.

Interface-module merging uses an ordinal-ignore-case spelling index to detect collisions while
retaining ordinal sorted output. Exact duplicate names with identical source remain accepted;
changed source or different casing remains rejected, including Unicode ordinal case pairs.
`Tests.ImportIndexes` exercises this merge rule independently of interface admission.

A Windows .NET 10 collection benchmark with reverse-ordered unique module names, including
both indexes and sorted output construction, measured 128/512/2,048 modules at
0.092/1.304/20.984 ms before and 0.011/0.060/0.458 ms after (one-second warmups, median seven
samples). This isolates module merging, not full import verification. Collision detection
becomes expected linear work; sorted output construction still takes O(M log M).

Static initializer bindings reuse the emitter's existing method-identity index instead of
searching the method array at each static load. Null initializers still use zero and missing
initializers still produce the existing `-1` sentinel. Three compiled Word256 static-load
entries retain all six generated Lean hashes; an unsupported initializer retains its exact
rejection diagnostic. This removes O(static sites × methods) search work without another index.
Static initializer validation shares a read-only `StaticValues.Context` within one metadata
validation walk. Constructor indexes retain store positions, the first control transfer and
an ordered branch-reentry envelope; module indexes retain the first stores outside a field's
constructor. Constructor closure address checks and initializer static-access checks are also
shared. Specialization creates detached clones, so the compiled module remains unchanged.
A later validation receives a fresh context; there is no module-wide persistent index cache.
The existing field/architecture value cache remains unchanged.

`Tests.StaticValueIndexes.cs` checks scalar copies, duplicate stores, prefix control flow,
branch/switch and foreign targets, first outside writer, closure address-taking, fresh contexts
and resolution-error ordering. Index construction records resolution failures so a later
failure cannot replace the original earlier writer diagnostic. Twenty-four extraction requests
(eight scalar loads across three profiles) retain all 48 generated Lean file hashes.

Windows .NET 10 medians over seven runs after three warmups measured resolution of every field
in a fresh synthetic module, including context/index construction, literal evaluation and
value checks but excluding fixture construction. The module has one constructor assigning
all fields and one reader accessing them all:

| Readonly fields | Repeated scans | Shared indexes |
| --- | ---: | ---: |
| 128 | 5.638 ms | 0.350 ms |
| 512 | 28.794 ms | 1.470 ms |
| 2,048 | 172.527 ms | 6.254 ms |

These isolate static-field resolution and do not estimate full extraction or CI savings.
Layout computation accumulates field placements in reverse and restores declaration order once,
removing quadratic `fields ++ [field]` work. `computeLayout_eq_append` proves equality to the
complete former computation for arbitrary layouts, architectures and nested-layout tables.
`Tests.LayoutAccumulation` covers order, explicit overlaps, empty layouts, missing children,
packing/offset failures and vector architecture restrictions.

Apple M4 / Lean 4.35 paired `decide +kernel` checks in the standalone
`Tests/LayoutAccumulationScaling.lean` fixture measured 2,556.71→546.05 kHB for 128 fields and
34,404.26→2,080.50 kHB for 512 fields (79–94% less kernel work). These include constructing and
comparing the entire computed layout, not total CI time. Local step lemmas keep the new full
algorithm-equivalence proof inexpensive: its declaration takes 1,282.34 kHB rather than the
177,255.76 kHB of the initial broad proof attempt.
Constrained-call validation and lowering now build ordered dispatch candidate indexes once per
invocation, then reuse them across call sites. Type identity, method token/name and explicit
interface override lookup no longer rescan the full catalog for every call. Candidate buckets
retain duplicates, exact type checks and explicit override precedence. Repeated override tokens
within one method still contribute only one candidate. Arbitrary-input equivalence theorems
cover indexed resolution, complete instruction validation and lowering, including malformed and
ambiguous metadata. The list-based `resolveConstrained` remains the specification used by those
theorems; production validation and lowering use `DispatchIndex.resolve`.

`Tests/DispatchScaling.lean` is a standalone kernel-work comparison with one valid call per
concrete type and a shared interface. Both sides construct the raw catalog; the indexed side
also constructs all indexes. Apple M4 / Lean 4.35 `leanprof elab --heartbeats` declaration work:

| Concrete types and calls | List search (kHB) | Indexed dispatch (kHB) |
| --- | ---: | ---: |
| 16 | 3,825.30 | 4,691.19 |
| 32 | 11,182.25 | 9,893.97 |
| 64 | 36,403.13 | 21,464.39 |

Index construction costs 23% more in the small fixture, breaks even before 32 calls and reduces
work by 41% at 64 calls. These are type-heavy dispatch measurements, not total proof or CI time.
Validation and lowering each construct their own index; they do not share it across invocations.
The helper APIs `constrainedSiteWindow`, `constrainedSites`, `lowerConstrainedInstruction`,
`lowerConstrainedCode` and their streaming equivalence theorems now accept a resolver function.
Public `ConstrainedCallsValid` and `lowerConstrainedRaw` argument types are unchanged.

Public layout projection validation now constructs balanced indexes for artifact selection and
nested public-index expansion. Ordered sets replace the three quadratic list-uniqueness checks.
`LayoutProjectionValid_iff_list` proves exact equivalence to all former conditions for arbitrary
inputs, including malformed indices and catalogs. `Tests.LayoutProjectionIndexes` checks
reordering, empty catalogs, duplicate identities/indices, case-sensitive identity, missing
indices and nested expansion; the existing imported-layout certificate tests also pass.

The proposition's unfolded conjunction now exposes `projectionDistinct ... = true` instead of
`List.Nodup`, and `projectionMetadataMatches` instead of the list-based metadata equality.
Consumers that destructure these clauses can recover the former statements through
`LayoutProjectionValid_iff_list`; the validator's accepted inputs and computed-layout checks
are unchanged. No stepping equations or execution tactics change.

Apple M4 / Lean 4.35 `leanprof` measurements of the standalone
`Tests/LayoutProjectionScaling.lean` paired `decide +kernel` fixture include complete validators,
both computed-layout checks, and construction of all indexes/sets. At 128 distinct empty layouts,
the workload fell from 42,941.43 to 29,594.10 kHB (31% less). At 32 layouts it increased from
3,288.47 to 3,667.68 kHB (12% more): index construction has a small-catalog cost. These are
synthetic validator measurements, not total CI timings. The eliminated work is quadratic
identity/index comparison and repeated linear metadata lookup; computed-layout validation and
structural equality remain, so this is not a claim that the entire validator is linear.

Imported-interface auditing selects declarations from the imported module catalogs rather than
materializing and filtering every declaration in the Lean environment. Current-file declarations
still use the environment scan. Private and auxiliary declarations are included and their actual
module ownership is checked. Dependency traversal visits shared expression nodes only once;
canonical contract serialization is unchanged. `Tests.ContractClosure` compares selected
membership with the former scan, including current, imported, missing and duplicate modules.
The imports suite compiles that test against its already certified library instead of rebuilding
the library's dependencies in the repository checkout.

A preliminary Windows paired native audit of `ImportFixture.addOne` measured median
3.50 seconds before and 1.22 seconds after (three runs each), with byte-identical audit output.
These focused timings are not complete-suite or CI measurements.
### Consumer certificate and theorem audit imports

Fresh consumer verification audits the extraction certificate and requested proof in one native
import environment. Both artifacts must match their kernel-replayed module paths, and their
individual theorem types, premises and allowed axioms are still checked. This removes a repeated
closure import; it does not reuse a previous proof result or skip fresh verification.

The four positive verification requests in `Tests/ConsumerCertificateReuse.cs` used eight native
audits before this change and four afterward. Local Windows traces measured 11.03 seconds versus
5.95 seconds in those audits. Other concurrent builds affected whole-fixture timings, so this is
not an end-to-end CI estimate. Corrupted receipts, changed extraction and generated-source
modification controls still reject as before.
### Allocation reference-step proof search

`fixed_fallback` normalizes mapped stack constructors definitionally and rewrites the target
profile once. It avoids repeatedly asking the simplifier to discharge the large dispatcher's
negative match conditions. Reference operations use a proved finite classification before stack
case analysis; this changes proof construction, not execution or the simulation statement.

On Apple M4 with Lean 4.35 and `leanprof --heartbeats`, elaborating
`Memory.Renamed.stepReference` fell from 416,618.32 to 204,647.51 kHB (51% less).
Its kernel check fell from 16,039.56 to 11,202.47 kHB (30% less). The generated Windows olean
shrunk from 32,111,728 to 26,561,792 bytes. All four fixed-step family consumers and the full
423-job library build passed without `sorryAx`. The profiling fixtures included the candidate
macros inline; the figures above select the theorem's own elaboration and kernel entries.
The same native auditor parses contract source import headers with Lean's parser. This replaces
compiling a temporary Lean parser program for each verification. Parsing still rejects malformed
headers, retains comments and module-system import syntax, and never elaborates source commands.
The imports fixture checks those properties explicitly. A focused native parse takes roughly
0.06 seconds locally; the original CI run spent 22.1 seconds across 25 interpreted parser calls.
### Core example batches

Core's ten immutable example proofs share one generated verification batch. Each keeps its
own extraction, theorem audit, exact translation certificate and output identity check. The
source, environment, receipt and assembly mutation scenarios remain separate. The focused
`dotnet run --file Tests/CoreExamples.cs` fixture uses the same implementation; `--separate`
reproduces the former verification loop, and `--check-existing <directory>` checks all reports
and rejects changed proof identity or batch source. With success caching disabled and the same
prepared library, the ten examples took 116.95 seconds separately and 28.65 seconds batched
on Windows. They contain nine distinct proof texts and ten distinct extracted programs.
Native audits fell from ten to one, replay processes from eleven to two, and Lake invocations
from five to one; both runs built exactly one support module. This is a focused measurement,
not a claim that the complete Core job has reached four minutes.

The generic-method, F# and universal-contract fixtures also batch their immutable positive
proofs. The generic instance and other fixed-memory contracts retain their exact statements;
batching does not turn them into arbitrary-memory specifications. Mutated assemblies and
expected failures retain their isolated checks. These changes remove eleven separate positive
verification sessions across the three fixtures.

Standalone proofs and generated batches combine their final replay and theorem audit when
eligible. Dependency certification, artifact identity checks and failure diagnostics remain;
audits needing source-location metadata still import the checked artifacts.
Paired Windows runs of the ten-example batch with the same certified library took 29.98 seconds
with separate replay/audit and 28.10 seconds combined. An earlier combined run took 40.17 seconds
with slower compilation and setup too; these short fixture timings remain sensitive to host load.

Compatible consumer requests can share that final replay and audit too. Each selected theorem
and its reachable replay-target declarations must belong to the request's own import closure.
Duplicate declarations and skipped consumer support conservatively retain separate checking.
The fallback replays each request's import-closed target set independently, preventing a forged
proof from borrowing an undeclared sibling dependency before an isolated axiom audit.
`Tests/JointReplay.cs` covers target and external owners, duplicate bodies and hidden dependencies.
The existing consumer batch checks also reject a theorem available only in another request.

`Tests/ConsumerCombinedAudit.cs` is a focused manual benchmark and adversarial fixture. Its
`--without-hidden` comparison keeps eight successful requests and two expected failures fixed.
On Windows, that workload took 30.87 seconds with separate audits and 19.48 seconds with shared
replay/audit, using the same certified library. Its default additionally checks an undeclared
reference to an unapproved sibling axiom; both shared and isolated fallback paths must reject it.
These measurements exclude fixture setup and do not establish a complete-suite CI timing.

### Native joint kernel replay

The authenticated `leancil-audit --replay INPUT` command accepts a JSON array of module names.
It uses the same `CIL/Replay.lean` algorithm as fresh-library bootstrap certification: import
non-target dependencies without extensions, reject conflicting declarations and replay target
constants in the kernel. Identical on-demand theorem duplicates retain the toolchain rule.
The native executable is checked before and after replay. Before it is authenticated, bootstrap
uses the source captured when the verifier starts and rejects changes before executing it.

`Tests/JointReplay.cs` exercises both modes against import-closed targets, repeated equation
lemmas, conflicting declarations, targets hidden behind untargeted imports and forged theorems.
Rejected joint sets still fall back to per-module replay with individual failure attribution.
The test also rejects a changed bootstrap source snapshot. In one Windows trace, the two
positive target sets took 2.03/2.19 seconds through the Lean frontend and 0.37/0.37 seconds
through the native auditor. Single-file verification now also shares replay imports for its
multi-module interface and proof target sets. Fresh checking and failure isolation are unchanged.

The native auditor also accepts `replayTargets` in an audit request. It retains the kernel's
checked environment for structural theorem and constant checks, avoiding a second dependency
import. Any duplicate declaration, interface/closure/namespace request, or contract refutation
requiring source locations retains the ordinary audit import. This does not change the standalone
replay duplicate rule: equal theorem types can have different proof bodies, so a merged replay
environment must not choose which body's axioms a subsequent audit sees. `JointReplay` checks
both duplicate orders, a forged body, source-location fallback and toolchain shadowing in both
paths. A fixed `Tests.MethodContract` artifact took 2.59–2.63 seconds for separate native replay
and audit versus 1.36–1.38 seconds combined, with identical statement and axiom output. These
are focused Windows timings. Single-request consumer groups use this path, except export callbacks,
full-import audits and profiled replay. Existing byte snapshots, module-path checks and post-audit
integrity checks still bind the result. A rejected joint set retains per-module failure attribution.
The verifier records `auditFused` so measured runs distinguish shared environments from
metadata or duplicate-declaration fallbacks.

### Evidence-suite reuse

The evidence runner compiles its test modules once against the authenticated CIL library,
without asking Lake to rebuild that library from copied build traces. Test dependencies are
ordered before their importers, with at most two independent compilations running together.
Child fixtures validate the parent's source/output hashes before reusing a completed test;
standalone fixture invocations retain their original build path. Reproduce this preparation
with `dotnet run --file Tests/ExtractionEvidence.cs -- --prepare-only`.

Generated rejection batches retain each mutation's original expected diagnostic markers. A
Lean command saves and restores the complete command state around each case, including its
declarations, attributes, scopes and options. Messages are collected with Lean's `guard_msgs`
helper, then associated with the original case's line range. A rejected neighbor, missing
marker, successful mutation or leaked failed simp theorem cannot satisfy another case's check;
`Tests/RejectedEvidenceTests.cs` exercises these failures. No rejection result is published
until every case passes. Existing audited positive batches still replay with `leanchecker`;
direct semantic fixtures retain their original frontend kernel checks while sharing imports.

The four capability profiles now share one generated verification batch. Every profile keeps
its own extraction identity, execution theorem, certificate audit and final regeneration check.
A regression rejects reuse of the scalar report under the x64-v3 profile. The runtime-scope
constants in the scalar, type-test, throw, span and imported-layout fixtures use the existing
byte representation, whose equality to the full assembly-name literal is already proved by
`runtimeScope_eq`; their regression statements are unchanged.

Focused Windows measurements on this change reduced the scalar regression file from about
26 seconds to 14.4 seconds and the type-test file from 12.2 seconds to 9.0 seconds by reusing
that representation. The mixed-profile feature fixture's traced work took 37.5 seconds locally.
These are local observations, not a claim that the evidence CI job is below four minutes;
its completed Ubuntu run remains the end-to-end acceptance measurement.

Constrained-call rejection fixtures retain the emitted definitions and the exact constrained
validator obligations, while their full positive certificates still check every validator.
Positive controls compile that same reduced fixture before changing its call target, so a
missing prerequisite cannot masquerade as rejection. Static-span proofs share one batch across
original and mutated assemblies, and UTF-8 identity mutations use isolated rejection scopes.
Generated verification batches use the authenticated native kernel replay command when it
succeeds, retaining the toolchain checker as the failure fallback for the same module set.

Translation-audit fixtures compile all six certificate variants against one checked prefix
before testing wrapper rejection, then replay those declarations and audit their exact native
statements. Missing certificates, unrelated statements, definitions and altered import tables
must fail both their wrapper checks and direct certificate audits; the definitionally equal
wrapped statement still passes elaboration but fails the exact emitted-statement check.

Generic substitution, managed-call and method-shape mutations select their corresponding
emitted validator; type-test mutations select feature-flow validation. Unchanged controls
compile first, with repeated generic controls deduplicated. Byte-backed identity definitions
retain their UTF-8 witnesses. Evidence-list omission and reordering still check the complete
certificate because they test agreement between records, not an independent validator.

Feature-flow validation indexes addressed local slots and classifies exact local types once,
then shares that index across state-shape checks, local transfers and emitted local operations.
`FeatureLocalIndex.eligible_eq` proves equality with the original raw instruction/type scan for
every index and fact, including malformed metadata and missing locals. Existing feature-flow
equivalence and reachability proofs retain their statements. The focused feature regression
also checks boolean bounds, both address-taking opcodes, wrong assembly scopes and malformed
address operands.

`Tests/FeatureLocalScaling.lean` isolates known facts at every instruction/local pair. A local
kernel measurement reduced 128×128 checks from 1.52 to 0.844 seconds, 256×256 from 6.58 to
3.99 seconds, and 512×512 from 29.3 to 16.4 seconds. Both measured sequences grow approximately
quadratically; these data do not demonstrate a different asymptotic kernel cost. The eliminated
work is repeated raw-body address scanning, local-list lookup and type classification. The
existing feature regression module changed from 4.290 to 4.056 seconds, a smaller benefit
because ordinary certificates often contain unknown facts, which already exit early.
For full 128-instruction feature certificates, empty-local kernel checks measured 116 versus
117 ms and 128 unknown locals measured 161 versus 152 ms; this sample showed no material
regression on the early-exit paths.

Full-verification term transfer encodes each structurally distinct expression node once and
writes a compact data table instead of elaborating a recursively expanded constructor term.
Structural equality includes binder spelling and annotations; names retain numeric and string
components, and universe expressions retain their full structure. Metadata is stripped as
before. The decoder rejects missing, cyclic and forward references, unknown binder annotations
and malformed table data. Free variables and expression/universe metavariables remain unsupported.

Decoding constructs expressions only. Each transferred declaration still passes `Lean.addDecl`
with kernel checking explicitly enabled, followed by the existing independent replay and exact
composition audit. The generated source imports the decoder from the certified
`CIL.Interface.FullTransfer` module. `Tests.FullTransfer` checks exact reconstructed types and
values across binders, universes, projections, local lets, string literals and proofs, plus
malformed table rejection. The full transitive suite retains its forged dependency, staged
mutation, changed implementation, cyclic dependency and missing-bundle regressions.

Contract publication audits interface declarations and their requested closures in one imported
environment. The fresh consumer theorem audit also requests each export's closure and certified
statement, including independently rebuilt full-verification exports. Export callbacks consume
that authenticated response after the existing artifact and source guards; they do not import
the environment again. The closure digest, contract kind, theorem axioms and statement checks
remain separate obligations. `exportsaudit` exercises source and compiled-artifact mutation
after those callbacks and requires the original integrity failures.

Exports whose artifacts lie outside the proof root share one consumer input snapshot and the
existing extraction-group verification machinery. Each request retains its own exact export
audit and checked result. Artifacts inside the proof root retain individual snapshots so their
output exclusion does not hide another request's source. `exportsfullpair` checks two exported
methods and their independently replayed caller composition; its focused Windows run passed
in 179.7 seconds. That is a validation timing, not a before/after performance measurement.
Consumer workspaces restore authenticated, source-bound support before compiling published
interfaces. Identical interfaces can therefore reuse their compiled artifacts across extraction
groups, while each workspace still kernel-replays them and checks their canonical contract
closures against its own imports. Existing before/after artifact checks remain in place.
`Tests/ContractImports.cs --interface-reuse-only` checks two fresh profile groups with one
interface compilation and independent replays. A focused Windows comparison reduced interface
build stages from 5.28 to 2.95 seconds and the two-request verification from 50.54 to 47.67
seconds. These are fixture timings, not complete-suite or CI measurements.

Consumer verification audits `Extracted.translation_valid` directly after kernel replay instead
of compiling a second theorem that merely restates it. The native auditor still requires a
theorem declaration, the exact `TranslationValid` application over the emitted tables and
program, and the approved axiom set. Consumer reports therefore name
`Extracted.translation_valid` in `extractionAudit`; the single-file verifier still names
`ExtractionAudit.valid`. Workspaces containing expected proof rejections retain the wrapper,
since those requests can finish before the final native audit. Compiled extraction and component
artifacts are hashed before consumer proof checking and checked again afterward.
Authenticated native replay also handles single-module target sets; profiling retains the
toolchain frontend, and rejected native replays retain the existing per-module fallback.
The same two-profile fresh workload took 43.56 seconds with these changes, versus 47.67
seconds with interface restoration alone; certificate compilation fell from 8.71 to 5.64
seconds and replay from 8.73 to 6.83 seconds. Full-suite timing remains a separate check.

The component-reuse and support-union fixtures skip their framework-only warmup verification
when `LEANCIL_CERTIFIED_LIBRARY` is supplied. Their actual batches still authenticate that
library and verify every original request with success caching disabled. Without a supplied
library, the original warmup remains. This removes two redundant complete consumer sessions
from prepared CI runs without removing any component, replay or source-identity assertions.

Fold discovery counts decoded local references once with a balanced tree instead of filtering
the entire instruction body per local. `foldRoles_eq_filter` proves exact equality to the
former filter-based selection, including malformed operands and out-of-range local indexes.
Methods without locals skip count construction. The separate positional lookup of local types
remains linear; this change does not make all of fold discovery linear.

Exception folds inspect at most three message loads, since admitted constructors accept at
most two. `throwFold_eq_takeWhile` proves equality to the unrestricted prefix scan. Long
rejected prefixes still permit an admitted fold starting later. Span and throw evidence tests
cover extra uses, malformed local operands, oversized prefixes and valid suffix folds.

On Apple M4, kernel-checked discovery for 256 span locals/768 instructions fell from 7.87s to
2.40s (user CPU 7.45s to 2.05s), including index construction and checking every output role.
A 4,096-instruction message-only body fell from 6.47s to 2.06s (user CPU 6.15s to 1.76s).
Smaller counts showed 0.94s to 0.76s at 64 locals and 2.29s to 1.17s at 128 locals. Existing
TypeTestEvidence and SpanEvidence were effectively unchanged: 5.22s to 5.15s and 0.77s to
0.77s. Those fixtures contain few locals and short message prefixes, so these are scaling
improvements rather than a demonstrated large CI saving.

The standalone kernel benchmarks are `docs/performance/fold-roles/CountScaling.lean` and
`ThrowScaling.lean`. After building each revision's library, run
`lake env lean docs/performance/fold-roles/CountScaling.lean` (and the throw file) under an
external timer. They construct their inputs inside the checked proposition and verify complete
role lists with `decide +kernel`; neither benchmark is part of the default library build.

With the indexed validators and combined replay/audit built into a newly certified library,
the Windows two-profile interface-reuse workload passed in 39.14 seconds, compared with
43.56 seconds before these changes. Both consumer groups used the fused audit; the interface
still compiled once and was independently replayed in each group. The entire fixture,
including setup, took 56.86 seconds. These timings do not establish a whole-suite CI gain.
The certificate-reuse fixture passed all six checks: its four positive sessions used the
fused audit, and generated-source tampering and compiled-extraction substitution were rejected.
