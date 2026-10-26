# Validation coverage

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
time. An optional argument selects the donor `.lake/build` directory; the synthetic
performance fixture is never supplied to a verifier as a certified library.

`Tests/ConsumerFingerprintReuse.cs` checks authenticated canonical fingerprints across
independent verifier processes using two framework modules and a multipart fixture. It
covers corrupt receipts, changed or missing parts, module names, auditor/runtime bytes,
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
outputs; changed extraction text and self-rehashed corrupt artifacts force rebuilding both
`Extracted` and `ExtractionAudit`. Every successful request still replays both modules and
the proof, and audits the certificate. Generated-source tampering remains rejected before
receipt reuse. Pass a baseline extractor DLL and `--measure` to collect the same workload
without requiring compilation reuse; results are written to `timings.json`.

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

The repository pins .NET SDK **10.0.402** and Lean **4.35.0**. The checks below cover semantic behavior, extracted contracts, artifact integrity and rejection cases.

```sh
lake build
dotnet run --file scripts/Test.cs
```

The regression runner covers **54 check groups** across twenty-three test partitions. This includes initial CLI proof selection and theorem output, an actual addition-to-subtraction source edit and rebuild, recovery using settings retained after the failed proof, the invalid-memory-access theorem, and the integer opcode, narrow-storage and primitive-operation matrices. The CLI group also passed separately against an isolated installation of the packaged .NET tool before the integer opcode extension.

The runner builds the independent assemblies and the CIL library, then prepares a source-keyed, kernel-replayed library for verification. CI rebuilds from sources; local runs may reuse an integrity-checked cache. Every proof still compiles and undergoes kernel replay in a new private directory. File-based C# apps provide the test runner, verifier and metadata fixture generator. Metadata tooling uses the same pinned Mono.Cecil version as the extractor; the F# example assembly also uses pinned FSharp.Core.

CI builds the certified library once per workflow attempt and passes its immutable artifact ID and manifest digest from the producer job to the suite jobs. It does not restore compiled libraries from the GitHub Actions cache: a cache's source key and self-described file hashes cannot authenticate the native auditor or establish that compiled modules came from those sources.

`dotnet run --file scripts/PrepareLibrary.cs -- <output-directory>` requires an empty or absent destination and publishes a freshly built library through a staging directory. Explicit reuse uses `--reuse <trusted-manifest-sha256>`; obtain this digest independently from a trusted producer, never by hashing the restored manifest itself. Missing or invalid reuse evidence fails without replacing the destination. Rebuilding an existing library requires a separate output directory. `Tests/LibraryCache.cs` covers substituted auditors and compiled modules with regenerated manifests, missing producer digests, and preservation of unrelated destination files.

The runner accepts `--suite <name>` after `--`, with names `core`, `cli`, `integer`, `narrow`, `primitive`, `division`, `checked`, `conversions`, `native`, `arguments`, `layout`, `copy`, `bits`, `enums`, `nested`, `instance`, `constructors`, `fsharp`, `math`, `divrem`, `unsafe`, `blocks`, `generics`, `loops`, `contracts`, `evidence`, `scaling`, `excluded`, `identity`, `labels`, `names`, `symbols`, `workspace`, `templates`, `callers`, `construction`, `outcomes` and `audit`. These partitions cover the same check groups as the full command and can run concurrently in separate checkouts. Each partition builds its own prerequisites, retains fresh Lean proof checking and writes `artifacts/test-results-<suite>.json`; running without arguments checks everything and writes `artifacts/test-results.json`.

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
