# Coverage and verification infrastructure

<!-- audience: maintainers -->

This page lists what the fixtures behind the [suites](VALIDATION.md#suites) check for extraction,
runtime comparison, artifact identity, consumer reuse and certified library preparation, and how
to run each focused fixture. Read it to find the fixture that covers a behavior before changing it.

## Preparation and shared infrastructure

### Prepared fixtures

The workflow builds `scripts/Test.cs`, `Tests/ContractExport.cs` and
`Tests/FullImportVerification.cs` once with Release analyzer checks.

- Their shared artifact is bound to a separately supplied manifest digest, the SDK/runtime,
  included sources, repository build configuration and the complete output file set.
  Configuration identity includes props, targets and configuration files along the entry script's
  directory chain through the checkout root.
- The workflow checks executable hashes before starting the runner. Nested fixture invocations
  check the same identity and use the compiled assembly; absent or incompatible preparation falls
  back to an ordinary local build.
- Mutation tests rebuild the example assemblies they modify.
- Only relocated fixture binaries use the shared checkout override; source-built child scripts
  keep their own source root, including producers running against an isolated modified library.
- Fixtures with `#:project` references use an ordinary build: file-app includes do not describe
  their external MSBuild source graph.

`Tests/PreparedFixtures.cs` covers arguments, included-source changes, nested configuration
changes, unsupported project references, SDK/runtime mismatches, manifest tampering and added or
modified output files.

### Extractor indexes and analysis reuse

- Branch positions and prefix-bypass checks use indexes scoped to each body traversal, and call
  translation uses a method index scoped to the current ordered call graph. Original and
  specialized bodies have separate instruction indexes.
- Dependency invalidation traverses reverse import edges once, including missing roots and
  cycles. Support reuse keeps the external module and extraction-source binding exceptions.
- `Tests/InstructionIndexes.cs`, `Tests/ConstrainedResolution.cs` and
  `Tests/ConsumerSupportCandidates.cs` cover identity, fresh traversal, branch/switch prefix
  bypasses, reverse-ordered chains, cycles, missing imports and support source bindings.
- Validation, emission and exception linting each compute one reachability result per method and
  reuse it within that phase, so no analysis is cached across method mutation or profile changes.
  Feature evidence uses the same incoming states as instruction selection.
  `Tests/ExtractionBatch.cs` compares direct and batch output across assemblies, scalar and SIMD
  profiles, feature queries and a loop backedge, and checks source/assembly tampering.

### Feature evidence

`Tests/FeatureEvidence.lean` checks:

- known int32 comparisons at signed/unsigned boundaries, short/long branch encodings, unknown
  operands and loss of facts after native conversions;
- that independent certificates reject changed comparison signedness, unjustified pruning and
  constants that do not survive a loop backedge; compiled profile guards exercise the same
  propagation;
- switches with known, unknown, negative and out-of-range selectors, empty and duplicate tables,
  and backedge weakening. Unselected targets reject out-of-range positions and tail-transfer
  interiors in both extraction and independent evidence validation.

`Tests/FeatureEvidence.cs` proves how each feature getter is classified:

| Getter | Classification |
| --- | --- |
| `AdvSimd.Arm64.IsSupported` | Agrees with `AdvSimd` under scalar, x64 and ARM64 profiles; the unmodeled ARM64 body it guards blocks only `arm64-advsimd`. `Crc32.Arm64` and `Rdm.Arm64` stay unclassified. |
| `Avx512Vbmi.VL` | Agrees with `Avx512Vbmi`: both are false under the built-in profiles and true under a custom v4 profile declaring VBMI, where the unmodeled VBMI body blocks extraction. `Avx512Vbmi2.VL` stays unclassified, and observations that omit or split `avx512VbmiVL` are rejected. |
| x86 `Aes` and `Aes.X64` | Read `aes`. |
| ARM64 `Aes` and `Aes.Arm64` | Read `armAes`. |

All four AES getters are false under the built-in profiles, and each architecture's pair is true
only under a custom profile declaring its flag. `Pclmulqdq` stays unclassified, and observations
that omit or split `aesX64` or `armAes64` are rejected. `BitConverter.IsLittleEndian` prunes its
big-endian branch on those profiles; forged owners and values are rejected by both certificates,
and lookalike scopes, fields and same-named module types are rejected by the extractor.

### Exact intrinsics

`Tests/ExactIntrinsics.cs` compares each intrinsic below with the host CPU, except where the row
says otherwise. Where a row names wrong models, the test fails if its inputs do not separate the
model from them:

| Intrinsic | Inputs | Must separate the model from | Rejections |
| --- | --- | --- | --- |
| `Avx2.Shuffle` and `Ssse3.Shuffle`, fed by `Vector256.Create<byte>` and `Vector128.Create<byte>` over byte spans | Twelve seeded span pairs each, one a 32-byte reversal mask; both short-span calls raise `ArgumentOutOfRangeException` in the runtime and the model | Shuffles that ignore bit 7 or cross 128-bit halves | A profile without the feature; forged load widths; substituted intrinsics |
| `Sse2.Multiply` on `Vector128.Create` lanes reinterpreted as `uint` | Twelve argument sets, two with set high halves and both 32-bit extremes | Odd lanes, a signed product, a full 64-bit product | `scalar`; forged evidence substituting the 256-bit multiply or another exact SSE call |
| A portable AES hash round on `Aes.Encrypt` | Eight seeded blocks; the extraction returns the same vectors under a custom x64 profile declaring `aes` and under a custom ARM64 profile declaring `armAes`, where it uses AESE and AESMC | | Every built-in profile rejects the reachable ARM64 calls; forged evidence substituting another AES step |
| A 256-bit arithmetic shift window: `Avx512F.VL.PermuteVar4x64x2` over a sign fill from `Vector256.LessThan<long>` | The five windows such a shift loads and seven random index vectors; the x64-v4 extraction returns the same vectors | A bit-3 table select and swapped tables | See below |
| `Vector256.Create` of eight `uint`s | Compared the same way | | |
| `AdvSimd.ReverseElement8` under arm64-advsimd | Checked against `BinaryPrimitives.ReverseEndianness` of each lane, since no ARM64 host runs it | | See below |
| A method that swaps two halves through `Vector128.LoadUnsafe` and `StoreUnsafe`, with and without an offset | Matches the host and faults on the second store into a 31-byte destination | | See below |

For the last four rows, profiles without AdvSimd or AVX-512 VL reject the reachable calls, and
forged permutations, reversals and transfer offset forms are rejected.

`Tests/AesHardware.cs` checks the host's own AES instructions against the Lean model on sixteen
seeded blocks: x86 AESENC in the `intrinsics` suite, and ARM64 AESE and AESMC in the ARM64 AES
workflow.

### Evidence batches

- The array, generic, layout and parameter evidence fixtures submit their 63 independent positive
  extractions in six batches. Each method keeps fresh mutable metadata; immutable assembly bytes,
  hashes and whole-assembly signature validation are shared within the batch. Long-form argument
  fixtures use a separate batch after writing their modified assembly. Expected extraction
  failures are isolated, since a batch stops at its first failure.
- `PrimitiveArrays`, `LayoutEvidence`, `ParameterEvidence`, `GenericEvidence` and
  `StaticScalarValues` each compile their generated positive evidence once as one file, with
  shared imports and a namespace per extraction and proof, and replay it independently with
  `leanchecker`. A pass is printed only after both checks and the source-stability checks
  succeed. Rejection fixtures run separately with their own diagnostic assertions. The array
  read, null and bounds checks share one final file.
- Each of these five scripts accepts `--measure`, which first checks the same final source files
  separately. `artifacts/<fixture>/batch-timings.json` records source hashes, separate time and
  batch compilation/replay time.
- `GenericEvidence` also checks that an invalid proof fails batch compilation and that an
  unchecked declaration reaches, and fails, independent kernel replay.
- `GenericEvidence` mutates the body evidence of its first sample: a body byte, the header, a token
  operand byte, a token table key, a token table operand, an emitted instruction offset, `maxStack` and
  a branch index. Each must fail a body obligation with the kernel's failed-decision message, so a
  mutation that only breaks parsing does not count, and the unmutated obligation is the positive
  control.
  `Tests/BodyDecoding.lean` decodes hand-made tiny and fat bodies with short and long branches, a
  switch, two-byte opcodes, token operands and float constants, rejects each kind of malformed
  body separately with its specific error, and compares the operand table with a static list
  generated once from the opcodes of Mono.Cecil.
  `Tests/BodyEncoding.lean` writes bytes and the metadata slice for the hand-built methods of
  other Lean fixtures.
  `Tests/MetadataDecoding.lean` decodes rows, headers, heap entries, signature blobs and
  assembly names copied from `Examples.dll` (two-byte columns) and from the runtime's
  `System.Private.CoreLib.dll` (four-byte columns) and compares them with the values
  System.Reflection.Metadata and Mono.Cecil read from the same positions, and rejects malformed
  rows, headers, heaps and signatures with their specific errors.
  `Tests/MetadataBinding.lean` checks every operand form, the locals and a method definition
  against a hand-built pair of pinned assemblies, and changes one row byte, blob byte, heap
  offset, scope, instantiation, field index, local or link at a time, each with its exact error.
  `Tests/MetadataDifferential.cs` writes every reference, type specification and method
  specification row of `Examples.dll`, with Cecil's full name for each method reference, and Lean
  must spell the same names from the bytes.
  Tests/BodyLiteral.lean writes the evidence of one method as literals, proves its body check with
  the kernel, rejects a changed byte, and requires the elaborator's decide to refuse the check
  within a small heartbeat budget. Tests/ScalarEvidence.lean does the same for the whole
  certificate, and reduces the fixture encoder in the elaborator at two method sizes.
  Tests/LookupScaling.cs also compares the metadata check's cost per token for 125 and 500 user
  string and field tokens and for 25 and 100 call tokens.
- Runtime bit tests narrow each source pattern to the parameter type before removing duplicates,
  so each distinct typed input runs once; every rotation count runs as supplied, including
  negative and out-of-width counts. Replay fallback tests check rejection and attribution in one
  invocation. Independent metadata mutations, malformed proofs, cache
  invalidation and native/bootstrap paths each have their own case.

```sh
dotnet run --file Tests/PrimitiveArrays.cs -- --measure
```

The positive controls for generic, constrained-call, feature-flow and folded-span mutations follow
these rules:

- Generic and constrained-call positive controls keep their narrowed declarations and exact
  obligation types, and reuse the original checked theorem without reducing its validator again.
  Generic controls compile and replay in the original positive batch. A constrained-call control
  compiles the same reduced fixture its mutation changes, so a missing prerequisite cannot cause
  the rejection, and the full positive certificate checks every validator.
- Missing or changed control declarations must fail type checking. Isolated mutation cases keep
  their own validator proofs and diagnostic checks, without access to the positive-control
  witnesses.
- Constrained fixtures include direct closed generic struct slots with substituted parameters and
  results, closed interfaces on ordinary and generic structs, and explicit implementations whose
  interface instantiations share a token and signature. A forged closed override owner must fail
  the same checked dispatch obligation. These cases share the positive batch and kernel replay.
- The projected declarations use a distinct namespace, so missing names cannot fall back to the
  original `Extracted` namespace. Controls reject explicit access to that namespace while
  preserving quoted metadata strings, and disable automatic implicit parameters.
- Regression cases cover removed declarations used by definitions or obligation types, changed
  definitions, qualified references and opened namespaces. Rejection diagnostics keep their case
  boundaries with or without Lean's diagnostic classification codes.
- Feature-flow and folded-span mutations use the same checked controls and keep only the intended
  feature-flow obligation in each negative fixture. Every rejection must identify
  `FeatureFlowValid` as false. Full positive certificates, runtime comparisons and consumer replay
  run as well; folded instructions with an unrecognized theorem cannot silently skip a test.

### Imported kernel audit and library extension

`Tests/CliImportedKernelAudit.cs`, called by the `cli` suite, extends the producer's certified
base with two uncompiled helper sources.

- Both standalone `verify --fresh` calls use private copies authenticated by that producer's
  manifest digest. The valid helper succeeds; the forged `AuditBad.helper` fails specifically
  during kernel replay and removes the previous certificate.
- Both helpers stay outside the audited base aggregate, and new helper declarations never inherit
  certification from that extension.
- The fixture rejects using the modified corpus's certificate with the unmodified tool.
- Trace assertions require zero fresh base builds/replays, one source extension and two successful
  private copies.

Run `dotnet run --file Tests/CliImportedKernelAudit.cs` after building the extractor and example
assembly. `-- --fresh-preparation` measures one fresh preparation, and `-- --measure-baseline`
measures a two-build workload. Without a supplied base, a local run prepares it before measuring
the extension. Each run writes `timings.json` beneath its isolated
`artifacts/CliImportedKernelAudit-*` directory.

`Tests/LibrarySourceExtension.cs` independently checks manifest authentication, private copies,
changed/self-rehashed compiled artifacts, existing-source edits/removals, configuration changes,
compiled-module shadows (including case variants on case-insensitive filesystems), and
preservation of an existing destination. Its synthetic compiled bytes exercise preparation
integrity only; the CLI fixture supplies the end-to-end kernel checks against real compiled
declarations.

### Consumer batch setup

`Tests/ConsumerBatchSetup.cs` runs the fixed mixed-outcome consumer checks used by the `core`
suite, with one certified-base preparation.

- Imported axioms, unchecked declarations, expected-rejection mismatches and invalid execution
  proofs keep their own outcomes and certificate assertions.
- Successful requests after rejected proofs verify that failures do not affect their shared
  session.
- `--separate` runs two isolated rejections followed by the seven-request batch, with three
  preparations. Both modes write stage counts and timings under `artifacts/ConsumerBatchSetup-*`,
  with caches disabled for the measured requests. When a certified artifact is supplied, copy
  counts are asserted as one versus three.
- Mutable-source, environment, provenance, receipt-tampering and process-progress tests are
  separate. The `core` test copies only its exact framework cache entry into its private cache.

```sh
dotnet run --file Tests/ConsumerBatchSetup.cs -- --separate
dotnet run --file Tests/ConsumerBatchSetup.cs
```

## Artifact identity and consumer reuse

### External identity encoding

`Tests/ExternalIdentityEncoding.cs` kernel-checks generated identity strings against their literal
values, including empty strings, embedded NULs, escaping and Unicode characters crossing chunk
boundaries. Malformed UTF-16 is rejected before serialization, and invalid UTF-8 fails its
validity proof. A compiled `Math.Abs` extraction passes, while a changed, valid UTF-8 call
identity fails `ScalarFlowValid`.

`scripts/BenchmarkExternalIdentities.cs` takes fixed baseline `Extracted.lean` files with
`externalIdentityNBytes_eq` declarations, replaces only their identity encoding with the current
emitter's, compiles both complete modules with one Lean worker and kernel-replays each
independently, all chunk declarations included. `artifacts/ExternalIdentityBenchmark` holds the
paired sources and `timings.json`: input SHA-256, source/artifact sizes, compilation and replay
times. Compare results only for the same fixed files and toolchain. For per-declaration kernel
costs, run the paired Lean files with `--json --profile -j1 -DElab.async=false
-Dprofiler.threshold=0`; JSON source positions identify each declaration.

### Consumer checks

Consumer checks compile together in `Tests/ConsumerVerification.cs` and run in separate child
processes, each with its private process and worker checks. Run one with
`dotnet run --file Tests/ConsumerVerification.cs -- --check <name>`:

| `--check` name | Fixture | Checks |
| --- | --- | --- |
| `source-resolution` | `Tests/ConsumerSourceResolution.cs` | Consumer source resolution |
| `compile-check` | `Tests/ConsumerComponents.cs` | The components fixture run with `--compile-check` |
| `support-union` | `Tests/ConsumerSupportUnion.cs` | A fixed three-extraction consumer batch in two orders. Support imported only by later groups must build and replay once; direct and indirect extraction-dependent modules must replay in every consuming group, including repeated import commands on one line. Compiled import headers are authoritative when scheduling misses an import. |
| `certificate-reuse` | `Tests/ConsumerCertificateReuse.cs` | Four independent verifier processes with distinct proof sources. Unchanged generated certificates keep their authenticated build outputs and run no certificate `lake build`. Reuse requires the complete certificate module parts and traces, unchanged authenticated restored artifacts, and the source/import closure binding. Changed extraction text and self-rehashed corrupt artifacts force rebuilding `Extracted`. Every successful request independently replays `Extracted` and the proof and audits the certificate. Expected rejection groups keep the separate `ExtractionAudit` module. Generated-source tampering is rejected before receipt reuse, and proof code cannot replace restored or freshly built certificate artifacts; both rejection paths remove a stale report. |
| `components` | `Tests/ConsumerComponents.cs` | Four independently certified wrappers around one helper. The common profile/layout and helper modules must compile and replay once, while all four complete extraction certificates must replay. Profile, helper and call-target changes invalidate their component identities; a consumer source shadowing a generated component must fail without a certificate. |
| `fingerprints` | `Tests/ConsumerFingerprintReuse.cs` | Authenticated canonical fingerprints across independent verifier processes, using two framework modules and a multipart fixture: corrupt receipts, changed or missing parts, module names, auditor bytes, fresh and disabled caches, diagnostic normalization, source/import invalidation and kernel replay. |
| `certified-fingerprints` | `Tests/CertifiedFingerprints.cs` | Direct normalization compared with an authenticated prepared-library table while local receipts are disabled: identical canonical results across independent receivers, relocation, renamed modules, changed parts and native tools, metadata mutation before publication and consumption, and self-rehashed corruption. The fixture uses two framework modules plus one consumer module. |

The checks take these measuring options:

- `timings.json` records wall, build and replay timings and module counts for `support-union`,
  process counts and elapsed times for `certificate-reuse`, and source byte counts and
  compilation/replay/wall timings for `components`. For each of the three checks, pass a baseline
  extractor DLL path and `--measure` to record the same workload without asserting reuse.
- `fingerprints --measure` uses the fixed full framework plus fixture workload and records wall
  time, raw input bytes, serialization counts and native normalization time. Supply a baseline
  worker DLL before `--measure` to compare the same seven requests.
- `certified-fingerprints --measure` uses the complete prepared framework and compares direct and
  prepared requests, recording fingerprint time, total worker time and serialization counts.
  Preparation normalizes the framework once; include its cost when assessing a workload's
  amortized savings.

Generated certificates have their own authenticated support records containing only the closed
generated module set. Their preparation key binds all generated sources and their Lake
configuration, framework artifacts, tools and declared environment inputs. A consumer package
configuration change can reuse this preparation without reusing consumer modules or exempting the
certificate from replay. The default consumer workload checks this with its
custom-build-directory request and checks invalidation with its Lake environment mutation.

Two opt-in checks are excluded from the default workload:

- `dotnet run --file Tests/ConsumerVerification.cs -- --check certificate-reuse
  --configuration-reuse` checks configuration reuse, fresh verification, self-rehashed corruption
  and post-restoration artifact mutation.
- `dotnet run --file Tests/ConsumerVerification.cs -- --check components --configuration-reuse`
  checks that split certificates keep their complete generated dependency set across a consumer
  configuration change.

Ordinary consumer requests regenerate the extraction and recheck their original inputs once after
proof execution. Export and full-import callbacks add a recheck after the callback executes. The
fixture records these recheck counts and times. The export and full-import mutation cohorts check
the post-callback integrity guards.

### Library copies

`Tests/VerificationCache.cs` checks certified-library copying against the pinned manifest, source
snapshot and toolchain key, rejects changed/missing/extra files and rehashed manifests, and
independently detects destination corruption. On Unix it also checks that both streamed artifacts
and copied metadata keep their file modes.

`Tests/LibraryCopyScaling.cs` compares separate validation/copying with hashing during copying,
with independent destination validation in both paths. It alternates four pairs over the same
framework/native build files and records file count, bytes and wall time. An optional argument
selects the donor `.lake/build` directory, by default the certified library's; the synthetic
performance fixture is never supplied to a verifier as a certified library.

### Standalone certificates and translation audit

- `Tests/StandaloneCertificateReuse.cs` measures complete CLI requests against a certified
  library, including source guards, native theorem audits and independent kernel replay.
  Standalone verification audits `Extracted.translation_valid` directly, with no separate
  `ExtractionAudit` elaboration; the
  [export page](VALIDATION-EXPORTS.md#interface-and-theorem-audits) states what that audit
  requires. The fixture checks frontend process counts for initial,
  unchanged, proof-edited, changed-extraction and `--fresh` requests. The generated and proof
  modules elaborate independently; there are no shared frontend environments or native snapshots.
- `Tests/TranslationAudit.cs` compiles six certificate variants against one checked prefix,
  replays them together and audits each exact statement. Missing, unrelated, non-theorem and
  wrong-import-table certificates must fail both the `ExtractionAudit` wrapper and the direct
  audit; a definitionally equal but structurally different statement passes elaboration and the
  wrapper but fails the direct audit. A changed prefix is rejected before any suffix can use the
  checked module.
- CLI regressions cover unchecked-theorem and transitive-helper rejection, stale-report removal
  and changed-code proof failure.
- `Tests/TranslationScaling.cs` checks the extraction prefix once, then imports it into the
  compositional certificate and a monolithic certificate that the elaborator's decide refuses at once,
  since only the kernel may evaluate the body and metadata check. `--measure` also
  checks both complete files and records command timings for the identical six-method workload.
  The consumer verifies the original extraction.

### Proof workspace

The `workspace` suite (`Tests/ProofWorkspace.cs`) builds a small library with a four-limb
`Workspace.Wide` struct and opens `Workspace.Wide::get_IsZeroOrOne()` under the scalar profile
with `--assume-initialized Workspace.Wide`. It checks the proof in place, adds a helper about the
method body, and expects that helper to fail after a C# rebuild with a different body and no Lean
edit. It verifies the same files fresh, shows that a forged editor module changes nothing
verification reads, and rejects a tampered extraction and a proof importing another extraction's
key. Under `watch`, editing a second method, `Workspace.Arith::Twice(ulong)`, refreshes and
rechecks only its proof, which fails at its theorem, while every file of the first method keeps
its bytes and write time. A C# syntax error makes both proofs stale and deletes both
certificates, and renaming the method reports its proof missing.

## Execution and extraction regressions

For checked-step and loop tactics, see [proof automation](VALIDATION-PROOFS.md#proof-automation).

- `Tests.CertificateFlow` covers streaming fallthrough, indexed forward/backward edges, missing
  states, out-of-bounds targets and mismatched certificate lengths. The feature and scalar
  equivalence theorems keep the list-indexed rules, including rejection when the feature and
  scalar certificate lengths differ.
- `Tests/LocalSnapshotSteps.lean` checks opt-in local snapshot stepping:
  - Vector and int32 stores, reloads and overwrites with abstract homes and memory, plus
    signed-byte narrowing. The mixed-width case carries Vector256, Vector128 and int32 locals
    through one snapshot invariant and returns the full arbitrary 256-bit input after the other
    locals are written.
  - Missing write authority, mismatched local kinds and unknown local contents are rejected. Each
    rejection uses an isolated store or load and a matching successful run with only the missing
    authority, correct value kind or remembered contents supplied. Strict proof elaboration
    prevents an incomplete rejected proof from inserting a placeholder.
  - Contract walks cross stores whose homes are stated at the frame's entry memory or after a
    leading root slot, and are rejected without evidence that the current memory keeps the homes'
    access or that the leading slot is no byte home.
  - Homes over opaque numeric specs take a local's kind from a supplied fact and stop at the store
    without it, as does a store at a symbolic local index.
  - A supplied store advances the snapshots to its own memory, and a store's named evidence and
    the caller reads and buffers it carries are checked against the final memory.
  - One walk crosses three stores while forming argument references, reading an input word through
    `ValidCall` and loading two caller limbs, one named and one supplied as a projection, and
    stops when a limb is not shown below the boundary. A counted walk stops after its second step
    and a second walk resumes from the snapshots it named.
  - One proof walks two bodies, with the body a variable until a case split and the homes
    derived before it by an untyped `have`. Such homes also justify a store on their own. The
    library build fails on an internal error printed while these proofs elaborate.
- `Tests/PrimitiveArrays.cs` checks compiled loads and stores for twelve primitive integer element
  types against runtime results and certified checked execution. It also covers length, helper
  calls, aliases, returned arrays, named null/bounds faults and unsupported array forms. Generic
  integer and enum fills cover readback, neighboring bytes, empty arrays, named null exceptions and
  missing write authority. Ranged fills cover interior slices, end-position empty ranges,
  null-first faults and negative or overflowing bounds. Malformed or expired storage cannot
  establish a named runtime exception. Independent changes to fill element identities, widths,
  operations, scope, arity and range selection, or load width and signedness, must fail the Lean
  scalar certificate. `Tests/PrimitiveArrays.lean` covers empty and null arrays, signed and native
  indices, initialization, authority, invalid extents, local storage and neighboring-byte
  preservation. Both run in the `evidence` suite.
- `Tests/ArrayElementReferences.cs` checks compiled `ldelema` returns, helper reads and writes
  against runtime behavior, preserving neighboring contents and rejecting a forged element type.
  `Tests/ArrayElementReferences.lean` covers null, empty and out-of-range accesses, expired
  references and address formation without granting memory authority. Both run in the `evidence`
  suite.
- `Tests/ReadOnlyArrayReferences.cs` inserts `readonly.` prefixes into compiled fixtures,
  checks returned and locally stored references, and proves that caller stores fail despite
  writable backing memory. It rejects independently forged writable evidence, separated prefixes
  and branches that skip a prefix. `Tests/ReadOnlyArrayReferences.lean` also checks alias updates,
  read access and rejection of an adapter that would remove the restriction, plus readonly
  `GetReference` results for nonempty, empty and out-of-extent views and field loads, field
  addresses and rejected field stores through restricted references. Both run in the `evidence`
  suite.
- `Tests/StaticScalarValues.cs` compares 16 compiled readonly-field loads with the runtime,
  covering integer widths, Boolean/Char, native integers, signed/unsigned enums, helper
  initialization and copies. It rejects missing initialization assumptions, mutable fields,
  repeated stores, branches and address-taking during initialization. Independent Lean checks
  reject forged scalar signedness, width and literal evidence. For `SeededHash`, whose seeds come
  from `RandomNumberGenerator`, it verifies `OpaqueSeeds.lean` for every seed, checks the reported
  `opaqueStaticValues`, and rejects a proof that reads a seed without a caller binding, a value
  forged into a seed's placeholder, `ldsflda` of a seed, and missing assumptions, mutable fields,
  repeated stores and outside stores. It runs in the `evidence` suite.

`Tests/CertificateFlowScaling.lean` and `Tests/CertificateBranchScaling.lean` provide fixed
512-nop and 512-branch workloads, each followed by a return, for kernel checking and independent
replay. Their profiler reports tactic execution and kernel type-checking separately. They are
separate from ordinary library builds. Compile and replay each workload, for example:

```sh
lake env lean -o .lake/build/lib/lean/Tests/CertificateFlowScaling.olean Tests/CertificateFlowScaling.lean
lake env leanchecker Tests.CertificateFlowScaling
```

Compare identical source with two libraries; native evaluation alone does not measure this
workload.

## Running the suites

[Validation](VALIDATION.md#running-suites) shows how to run the suites and what a run writes.
The runner:

- builds the independent assemblies and the CIL library, then prepares a source-keyed,
  kernel-replayed library for verification. In CI that library comes from the
  [`prepare` job](CI.md#certified-library); a local run may reuse a cache entry whose receipt
  binds its key and manifest and whose files all hash to that manifest on each use;
- checks the library by its trusted manifest digest and reads it in place: every proof compiles
  and undergoes kernel replay in a new private session package that requires the library as a
  path dependency, so Lake writes only below that session;
- uses file-based C# apps for the test runner, verifier and metadata fixture generator. Metadata
  tooling uses the same pinned Mono.Cecil version as the extractor; the F# example assembly uses
  pinned FSharp.Core.

Its CLI regressions cover initial proof selection and theorem output, an
addition-to-subtraction source edit and rebuild, recovery using settings kept after the failed
proof, the invalid-memory-access theorem, the integer opcode, narrow-storage and
primitive-operation matrices, `new-proof` rejecting an existing file, a stale extraction and a
struct parameter, and an isolated installation of the packaged .NET tool.

The runner, the tool and library preparation reject every run of Lean, Lake or the audit
executable whose output holds an [internal error](CLI.md#diagnostics), so a panic while building
any `CIL`, `Examples` or `Tests` module fails the suite that builds it.
`scripts/TestLeanDiagnostics.cs` checks that rule on recorded output:

- Each message form fails a run that exited with `0` and makes a failed run an
  `internal-error`, whether it was written to stderr, logged by Lake, logged by Lean at a
  position or printed in `--json` output.
- The report names the proof module and file and quotes the message, an internal error leads the
  Lean errors of its run, and another request's proof module is left out.
- Ordinary information, warnings and recursion limits keep their results, as do a message that
  quotes the runtime's text inside a sentence, a goal or a term and a program other than Lean
  that prints it.

The `failures` suite verifies a proof that holds and runs a tactic that reads past the end of an
array. The run exits with `1`, reports kind `internal-error` and leaves no `verified.json`.

## Certified library preparation

This section covers `scripts/PrepareLibrary.cs` and its tests. CI's [donors](CI.md#donors) and
[reuse and replay](CI.md#reuse-and-replay) rules say which runs may donate a library and when
reuse skips kernel replay.

| Invocation | Behavior |
| --- | --- |
| `dotnet run --file scripts/PrepareLibrary.cs -- <output-directory>` | Requires an empty or absent destination and publishes a freshly built, kernel-replayed library through a staging directory. Rebuilding an existing library requires a separate output directory. |
| `--reuse <trusted-manifest-sha256> [--producer-replayed]` | Rechecks the library key, the source binding and every file against that manifest, then kernel-replays the library unless `--producer-replayed` is passed. Obtain the digest independently from a trusted producer, never by hashing the restored manifest itself. Missing or invalid reuse evidence fails without replacing the destination. |
| `--incremental <donor-directory> <trusted-manifest-sha256>` | For changed Lean sources. Authenticates every donor file before reusing its Lake build traces in a private copy. The runtime, compiler, kernel checker and build configuration must match; the configuration is the [library view](CI.md#identity) of `lakefile.toml`. Changed and removed modules lose their compiled artifacts; Lake checks the current source hashes and rebuilds the dependent closure. The native auditor is relinked, every resulting module is kernel-replayed, including those kept from the donor, since a byte-identical module can import a rebuilt one, and canonical fingerprints are regenerated before a new source-bound manifest is published. |

These tests cover preparation:

- `Tests/LibraryCache.cs` covers substituted auditors and compiled modules with regenerated
  manifests, missing producer digests, preservation of unrelated destination files, and a
  receipted cache entry whose module was rewritten, restored or joined by a file its manifest
  lacks.
- `Tests/LibraryCache.cs` also covers closure entries: their key names exactly their modules, a
  compiled module or source outside the closure rejects the entry, an import outside the closure
  fails, and a closure entry is never accepted as the whole library. With a few modules in place
  of the framework and CI's settings cleared, the fixture builds and kernel-replays a closure
  from an empty cache, reuses it, keeps it while a process reads it, reports a whole library that
  cannot be built, completes the whole library, which replaces the entry and is preferred, and
  rejects an import outside a closure from the compiled import header in three spellings.
- `Tests/LibraryCache.cs` also covers eviction of library entries. Entries unused for the
  retention period and abandoned staging go. The current entry, an entry whose use lock is held,
  an entry a package pins, a directory without a publisher's manifest and receipt, other names,
  lock files and links stay, and a link inside a removed entry is not followed. The entry limit
  removes only the least recently used entries unused for a day, and no retention setting removes
  an entry used within a day. Opening or publishing an entry renews it, and an open run and an
  editor process hold the entry's lock, taken before the entry is validated. Another process
  holding the lock excludes a pass, and the lock files stay. A pin that cannot be read, is being
  written, is renewed during the pass, or names a missing package keeps its entry as described in
  the CLI document, a package whose lakefile names the entry keeps it however old its pin and
  however the cache directory is spelled, and no pass raises. A lakefile that never answers, and
  an injected reader that blocks, delay a pass by a bounded time; the named-pipe check prints SKIP
  on Windows. Opening an entry evicts nothing, and a publication reports its removal as a stage
  with the number removed and nothing else on stderr. Malformed settings keep the defaults and
  huge ones clamp. The link checks print SKIP when no symbolic link or junction can be made. The
  `workspace` suite checks that both package kinds pin the entry they require.
- The `workspace` suite checks that a full audit, contract imports and a package import are never
  offered a closure entry.
- Closure verification of a real extraction through the CLI, with its `verified.json` fields and
  exit code, runs in no suite: it needs the 95 framework modules an extraction imports.
- `Tests/LibraryIncremental.cs` covers artifact tampering, incompatible identities/configuration,
  source removal and copy isolation.
- `Tests/LibraryReplayCoverage.cs` uses a small synthetic producer manifest with a valid aggregate
  and an invalid theorem in a separate module. Both joint replay and its external-checker fallback
  must reject that declaration; checking only the aggregate is insufficient. It also checks that
  reviewed reuse runs no replay yet rejects a changed file or digest, while other reuse and
  release replay reject a forged module. The cache fixture runs it alongside the authentication
  tests.

## Coverage by behavior

| Coverage | Checks |
| --- | --- |
| Profile-parametric templates | Compiled AVX2/SSE4.2 dispatch helper, one generated template proof on three profiles, renumbered managed callees, exact per-pc equations, independent kernel replay, and wrong flag/callee/branch/equation, stale source and metadata rejection |
| Cyclic control flow, termination and generated proof outlines | The `loops` and outline suites; the lists below the table give their cases |
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
| Span constructors (`SpanConstructors`) | Single-reference and pointer constructors cover primitive, aggregate and integer-vector elements, mutable/readonly views and in-place local initialization without readable bytes. Empty getters and explicit default resets cover returns, helper calls and empty slices. Vector-field aggregate layouts are checked on x64 and ARM64; evidence mutations reject changed widths, capabilities and aggregate identities. Wrong scoped reset types and branches into reset folds are rejected. |
| Span reference parameters (`SpanReferences`, `SpanReferenceContracts`, `SpanReferenceWordContract`, `SpanReferenceSecondContract`) | `in` and `ref readonly` span parameters cover loops, indexing, slicing, element writes, copies, forwarding, caller-side local, parameter and temporary addresses, closed generic helpers, a struct constructor, field reads and field addresses through writable and readonly aggregate elements, and `MemoryMarshal.GetReference` of readonly views, including a byte-order read and `Unsafe.Add`, `Subtract` and `AddByteOffset` offsets and an advancing cursor loop that stay readonly; symbolic `Contents` contracts prove an indexed read, a first-word read and a second-word read through `Unsafe.Add`. Kernel fixtures check expired backing storage, readonly element stores, writes and field stores through readonly `GetReference` results and their offsets against writable controls, one-past, beyond-end and negative readonly offsets, empty and out-of-extent readonly views and forged reference arguments. Evidence mutations reject a span-valued raw argument and a load in place of a span copy; rebinding, addressing or storing to the parameter, writable span parameters (including a generic helper's `ref` span and a generic definition stripped of its readonly markers), span reference returns and indirect copy sources are rejected during extraction. |
| Supplied aggregate/vector arrays (`AggregateArrays`, `AggregateArrayStorage`) | Typed element addresses, loads/stores, lengths, span conversions and data references cover reference-free structs and integer vectors over existing storage. Kernel fixtures check masks, authority, bounds, lifetime and readonly views; independent evidence mutations reject changed element descriptors and operations. |
| Closed generic structs (`GenericLayouts`) | Sequential same-assembly reference-free instantiations cover nested layouts, fields, direct instance methods and constructors through checked owner substitution and ordinary aggregate storage. Unsupported reference-bearing, open, non-sequential and interface/reference-constrained generic layouts remain rejected. |
| Byte-order span transfers (`BinarySpans`) | Compiled wrappers exercise all 64 signed/unsigned 16-, 32-, 64-bit and native integer read/write/try endian overloads, short spans, read/write authority and uninitialized reads. Evidence mutations reject altered widths, endian choices, signedness and try behavior. |
| No-read view observations (`ViewAccessors`) | Span emptiness, pinnable references, `MemoryMarshal.GetReference` of writable and readonly spans and array data references cover empty/default/readonly views, empty and null arrays and observations without readable bytes or byte authority. Evidence mutations reject mismatched accessors and capabilities. |
| Closed generic owners (`GenericOwners`) | Static helpers on closed same-assembly generic owners, nested owners and combined owner/method arguments certify through structural substitution; evidence mutations reject incorrect owner and argument bindings. Span indexer, `Length` and `Slice` calls on owners built from method (`!!0`), owner (`!0`) and nested owner (`!1`) parameters execute against caller views; unsubstituted, wrongly instantiated, swapped-member, wrong-owner and misspelled open targets fail instantiation. |
| Native managed dispatch (`NativeManagedDispatch`, `NativeMethodTables`) | Supplied immutable native tables cover checked byte-offset loads, authenticated native target locals, separate numeric locals and tail dispatch. Fault and certificate controls reject invalid storage, target provenance and signature changes. |
| Null managed references | `IsNullRef` of `NullRef` and of a live argument, reads and writes through `NullRef` (indirect and field) and an optional `ref` local: ten outcomes compared with .NET, each `NullReferenceException` matched to a located null-dereference fault; forged `NullRef`/`IsNullRef` translations rejected by the call binding; 22 malformed generic calls rejected |
| Reference/null observations | Emitted CIL fixtures compare .NET and checked Lean execution for `ceq`, `brtrue`, `brfalse`, `beq`, `bne.un` and bounded `ldnull`; an independently changed equality operation must fail scalar evidence. Semantic fixtures cover readonly views, null, lifetime, invalid addresses, end pointers and disjoint allocation interiors. A null-message throw fixture preserves existing folding. |
| Integer Math helpers | 21,804 runtime comparisons across 40 overloads; universal signed-minimum proof; incorrect implementation and seven malformed calls rejected |
| `X86Base.X64.DivRem` through `ValueTuple<ulong, ulong>` Item1/Item2 reads | Runtime tuple offset probe; 500 checked-execution boundary cases across five read shapes compared with hardware and a `UInt128` oracle, including divide-by-zero and overflow faults; universal quotient and fault proof; remainder substituted for quotient rejected; eight forged calls, scopes and tuple layouts rejected |
| `Math.DivRem` tuple and `out` overloads | Runtime equal-width tuple offset probe; 562 checked-execution comparisons with .NET over the ten tuple overloads, a narrow Item2 read and both `out` overloads, including divide-by-zero, wide `MinValue / -1` overflow, wrapping narrow `MinValue / -1` and null output faults; universal `int` quotient, divide-by-zero and overflow proof; remainder substituted for quotient rejected; forged mixed-width tuple rejected |
| Signed and 32-bit `Math.BigMul` | Universal signed high/low proof with exact `Int` recomposition and 81 signed boundary cases with uninitialized output storage; unsigned high-word contract rejected for the signed call; universal exact `BigMul(int, int)` proof; 36 signed and 36 unsigned 32-bit boundary cases compared with .NET |
| Library, scalar/SIMD semantics, allocation, permissions, initialization, lifetime and symbolic automation | Regression checks |
| Ten extracted arithmetic, branching, call, aliasing, aggregate and semantic-negative proofs, each with artifact checks | Regression checks |
| Compiled C# negation: universal modular additive-inverse contracts for 32- and 64-bit inputs | Universal proofs at both widths |
| Exact `nop`, `neg`, `cgt`, `bgt`, `bgt.s`, `ble`, `ble.s`, `ble.un`, `ble.un.s` encodings in independent Cecil fixtures | 370 checked-execution boundary cases across 32- and 64-bit operands |
| Identity substituted for negation, with the unchanged universal contract | Rejects both widths during proof checking; no successful report retained |
| Scalar operations: stack underflow, mixed widths and reference operands; `nop` preserves arbitrary stacks | Semantic tests |
| Compiled C# unsigned-short conversion: universal result `x % 65536` for every 32-bit input | Proof checking |
| Narrow conversions, locals, arguments, returns, calls and fields, including aggregate snapshots | 744 checked-execution boundary cases, including 144 deliberate faults |
| Uninitialized narrow locals and 64-bit stores into narrow homes | Rejected with the expected located faults |
| Two-byte field overrun and forged narrow runtime type identity | Both rejected during extraction |
| Signed conversion substituted for unsigned conversion, with the unchanged universal contract | Rejects during proof checking; no successful report retained |
| Narrow access bounds, permissions and lifetime; generic typed store/load normalization | Semantic tests and universal roundtrip theorem |
| Compiled C# `ref int` store/load: every 32-bit input returned unchanged | Universal proof |
| Primitive `ldobj`, `stobj`, `initobj`, indirect loads/stores, C# aliasing, `switch` and `sizeof`, including native integer storage | 534 cases, including memory faults, initialization and preservation of neighboring bytes |
| Empty/duplicate switch tables, out-of-range unsigned indices and switch-only managed dependencies | Regression checks |
| Corrupted switch target, unsupported arm, four forged type tokens and floating-point size | Seven intended extraction rejections |
| `sizeof` on pointers, managed references, objects, strings, arrays, double, auto layouts and malformed sequential field offsets, reference-containing structs and unsupported generic layouts | Eleven intended extraction rejections; no Lean extraction produced |
| Constant-zero write substituted for the input, with the unchanged universal store/load contract | Rejects during proof checking; no successful report retained |
| Scalar access operand/width checks, bounds and lifetime; arbitrary-memory 32-bit store/load roundtrip | Semantic tests and universal roundtrip theorem |
| Short and full assembly selectors retain the same complete manifest identity | Regression checks |
| Explicit version, culture and public-key-token mismatches | Three intended identity rejections |
| Method selectors: aliases, optional returns, short declaring types, overloads, canonical artifact identity, malformed inputs and candidate diagnostics | 23 checks |
| Assembly inference from a renamed DLL, equivalent explicit identities, mismatched constraints, malformed options and stale outputs without `--assembly` | Regression checks |
| Directory-only checks: recorded profiles, moved DLL override, missing DLL, invalid profile and modified artifacts | Regression checks |
| Independent hardware-feature assembly built from a single C# file | Regression checks |
| CLI packaging smoke checks: build and publish `leancil.exe`, `dotnet run`, isolated .NET tool installation, installed `leancil extract` and `leancil check` | Packaging smoke checks |
| One-command worked example: `dotnet run --file Examples/Verify.cs` | Verifies `ExampleProof.correctness` |
| Installed `leancil verify`: explicit proof, printed theorem, portable settings, source mutation, failure/recovery, memory fault theorem and stdout/stderr | Four CLI regression stages |
| Method discovery includes canonical selectors and unsupported candidates without claiming support | Regression checks |
| Malformed settings, missing proof, unsupported CIL, changed assembly and missing Lake produce stage-specific guidance | Regression checks |
| Subtraction rejected by the unchanged universal addition contract | Rejects the implementation and removes any successful report |
| Reference-free array allocation | Checked primitive/enum, packed/nested aggregate and vector zero initialization, payload alignment, empty/non-null identity, negative/native lengths, helper returns and packed field stores; forged element identity, layout identity/width and byref-like certificates, malformed markers and unsupported extents rejected |
| Integer `div`, `div.un`, `rem`, `rem.un`, both widths | 648 comparisons against .NET execution and corresponding Lean proofs, including divide-by-zero and signed overflow |
| Extracted unsigned quotient for arbitrary inputs with a nonzero divisor | Universal proofs for 32 and 64 bits; multiplication substituted for division rejected by the unchanged contract |
| Division with mixed widths, references, stack underflow or a zero divisor | Semantic rejection tests |
| Checked add/subtract/multiply, signed and unsigned at both widths | 2,028 comparisons against .NET results or overflow exceptions and corresponding Lean proofs |
| Checked addition with a sum that fits | Universal 32-/64-bit natural-number addition proofs; subtraction substituted for addition rejected |
| All 20 integer checked-conversion encodings, from both input widths | 762 comparisons against .NET execution and corresponding Lean proofs, including native destinations and overflow |
| Checked 64-to-32-bit unsigned narrowing with a representable input | Universal preservation proof; an eight-bit truncating implementation rejected |
| Native signatures, locals, calls, fields, references, arithmetic, shifts, casts and `sizeof`, plus exact mixed native/int32 operations in both operand orders | 2,511 comparisons against .NET results or arithmetic exceptions and corresponding Lean proofs; all 60 ambiguous mixed unsigned-branch forms rejected unless explicitly widened |
| Extracted native addition on the admitted 64-bit target | Universal modular-addition proof |
| Required-32-bit assembly, forged native type identity, native field overrun, native/int64 operands and 32-bit execution profile | Five intended extraction rejections |
| Native widening wrapper with memory instructions, nested wrappers or references | Semantic rejection tests; unsigned branch/comparison widening differences checked explicitly |
| Argument assignment/addressing, both full and short encodings, all admitted integer storage types, aliases, calls, byref reassignment and structs | 639 runtime/memory cases, including 636 .NET comparisons |
| Overwriting an argument with a replacement value | Universal proof for arbitrary inputs; assignment to the wrong parameter rejected |
| Returning an address into a parameter home | Lifetime fault proved for every input; successful execution ruled out for every fuel budget |
| Parameter setup with missing inputs or incompatible scalar/reference values, and narrow initialization | Semantic checks; taking the address of a byref parameter rejected during extraction |
| Ordinary and packed sequential structs, all admitted packing values, small/odd explicit sizes and empty structs | 187 runtime layout/execution cases; emitted sizes and field offsets agree with managed runtime probes |
| Sequential struct field store/load | Universal preservation proof for every 32-bit input |
| Invalid packing, oversized layout, auto layout, reference/float fields, inline arrays, generics, explicit offsets on sequential fields, nested reference-bearing and recursive fields | Ten intended metadata rejections |
| Synchronized methods, wrong framework/identity, invalid field layout, unsupported locals, static initializer and forged runtime scope | Seven intended metadata rejections |
| Identity-bound static RVA data | Regression checks |
| Static `ReadOnlySpan<uint>`/`<ulong>` tables | Indexed reads, length and first element compared with .NET, including negative and past-end indices faulting with `System.IndexOutOfRangeException`; forged receiver folds fail the feature certificate; tampered RVA bytes change the proved word; branches into the fold rejected |
| Memory-backed primitive spans | Compiled readonly and writable slices to helpers; sequence-content read and update contracts, and readonly/writable caller composition without unfolding helper bodies; creation over an existing reference; forged element widths and write capabilities rejected by specialization evidence; empty end slices, invalid indexes and slices, alias visibility, missing write authority, uninitialized reads and expired local storage; by-reference and floating-point span signatures rejected |
| Static readonly struct values | `Zero`, `One` and `MinValue` limbs proved and compared with the values .NET's static constructor stored, also through an out parameter; a changed constructor argument changes the proved limbs; forged value bytes fail `Extracted.translation_valid`; a missing initialization assumption, a `newobj` initializer, `ldsflda`, a store outside the static constructor and a second store rejected; Lean regressions for the load semantics and a self-justifying initializer |
| Static `ReadOnlySpan<byte>` lookup tables | First and last byte proved; past-end read and write to immutable data rejected; tampered RVA bytes change the proved value; four intended span metadata rejections and positive stored-span parameter/local fixtures |
| Tampered Lean output, changed compiled assembly, changed assembly version with a short selector, changed proof and changed feature profile | Five intended stale-artifact rejections |

The `loops` suite checks cyclic control flow and termination:

- A universal checked countdown proof holds for every `uint`, including zero and the maximum
  value, with 17 runtime comparisons, and holds unchanged after inserted NOPs and reordered
  blocks. An incorrect implementation is rejected under the unchanged contract, and an infinite
  loop is proved to exhaust every fuel budget. Backward switch, native arithmetic and
  fixed-feature loops are checked, and eight malformed or unsupported fixtures are rejected.
- `CountCalls` is proved through its helper's contract, unchanged for a helper reimplemented as
  `value + 0xFFFFFFFF` with only its contract re-proved; builds that discard the helper result or
  count twice are rejected. On the correct build, measuring by the count fails the decrease
  obligation, and the non-inductive invariant `count + remaining = value + count * remaining`
  fails only its preservation.
- `CountUntil`, which returns or raises its helper's exception after earlier calls, is proved for
  every pair of `uint`s from the helper's outcome contract and compared with .NET on five inputs,
  two of which throw. The proof holds unchanged for a reimplemented helper and fails at the
  exceptional exit for a helper throwing `System.ArgumentException` under a re-proved contract.
  On the correct build, measuring by the count fails the decrease obligation, the invariant
  `count <= limit - remaining` fails only its preservation, and specifying
  `System.ArgumentException` for the loop fails only at the exceptional exit.
- `CopyUntilZero` is compared with .NET on five spans, checking that the words past the copy are
  unchanged; builds whose `Stamp` writes zero or whose loop copies past a zero are rejected.
- `FillWords` is proved to write exactly `count` words for every nonnegative count and compared
  with .NET for four counts, keeping both neighbouring words; shifted or skipping stores are
  rejected.
- `AllZero` and `Sum` are compared with their sequence specifications on five spans each and a
  `default` span, including wrapping sums; a build of `AllZero` that replaces every read with zero
  and a build of `Sum` that stops while one element remains are rejected.

The outline suites check `new-proof` outlines:

- These outlines elaborate with only `sorry` warnings and are byte-identical across runs:
  - loop examples: one with two loops in sequence, one searching a free list through an object
    local, one filling a writable span, one filling it through a helper that stores the first
    element of the span it is passed, one summing and one filling an array by index, and three
    slicing a span local, which sum a span and an array and fill an array;
  - straight-line methods with `bool`, narrow, writable span and array parameters, a `bool`
    result, unsigned and signed checked adds, a bit count and splits on unsigned and signed word
    tests;
  - straight-line methods over class instances, string fields and arrays of class references,
    including element facts carried across element and field stores and an array the method
    allocates;
  - methods over value arrays of words, structs and vectors that class fields hold, including a
    struct element named across lines;
  - struct instance methods storing fields.
- The countdown outline is rejected for `sorryAx` and verifies once only its holes are filled, as
  do filled outlines for array/class composition, multiple struct-field stores, signed and
  unsigned narrow fields, struct value parameters, nested locals and receiver loops.
- A static helper over words gets a contract stub. Its filled outline verifies where the helper
  tests its arguments and its result is returned, stored into a field or returned by a caller
  over words alone, where it throws on one side and where it only computes. A `post` the helper's
  body does not meet, a `post` that does not give the caller's postcondition and a `pre` that
  admits the throwing side are rejected.
- Filled outlines verify for a helper's result kept in an integer local by a caller over an
  object or over words alone, tested after it or not, for a helper over words that keeps its own
  locals and one that tests them, and for a helper that tests a field of the object it is passed.
  A `post` the object helper's body does not meet is rejected.
- An object helper called from a frame of locals, one that throws beyond a field and one that
  throws from a frame of its own verify filled. A `pre` that admits the object helper's throw
  fails saying the path must be ruled out.
- An indexed array loop's outline states the null exclusion in `Precondition`, and a precondition
  without it fails naming null.
- Mutations to arithmetic, indexes, element types and loop progress are rejected.

The addition theorem proves modular arithmetic correctness for arbitrary 64-bit inputs in the
checked execution model. The unsigned-short theorem proves reduction modulo 65,536 for arbitrary
32-bit inputs. The invalid-access and expired-reference theorems classify faults and rule out
successful execution for every fuel budget. The subtraction theorem independently refutes the
intended addition result. Other example claims have the quantifiers and inputs displayed in their
theorem statements; concrete examples do not establish universal method correctness.

Audited example theorems meet the axiom rules of the
[trusted computing base](SOUNDNESS-VERIFICATION.md#trusted-computing-base);
[the trusted base](SOUNDNESS.md) lists the runtime and extraction assumptions.

Each successful proof produces an identity-bound `verified.json`. That file and the
[result files](VALIDATION.md#running-suites) are reproducible outputs and are not committed.
Passing the suites does not establish support for arbitrary .NET programs; see the
[support boundary](SOUNDNESS.md).

Typed copy validation covers 648 runtime result/byte-copy cases across 18 primitive, struct and
vector types, including self-copies. The universal UInt64 copy contract rejects reversed
source/destination operands. Four unsupported/forged type-token cases test extraction rejection.
Ten semantic tests cover initialization, permissions, lifetime, GC-sensitive storage,
bounds, null references and partial overlap. A generic snapshot theorem covers typed copying.

Portable helper validation compares .NET results with extracted execution, covering
power-of-two boundaries, zero/all-ones values, signed boundaries and negative/oversized rotation
counts. Primitive 32-bit, 64-bit and native rotation aliases use compact boundary samples;
the full BitOperations matrix covers their shared scalar operation.
Universal 64-bit rotation round-trip and integer-logarithm proofs use only approved Lean axioms.
Incorrect implementations must fail those contracts. Nine malformed/unsupported runtime calls
test extraction rejection. Semantic tests reject incorrect arity, widths and operand types.

Enum validation covers 378 runtime comparisons across all eight underlying integer types, flags,
calls, fields and typed storage. A universal flags proof rejects an incorrect implementation.
Eleven malformed metadata cases test extraction rejection.

Nested struct validation covers 123 runtime/layout comparisons, including sixteen packing
combinations. A universal nested snapshot proof rejects an incorrect implementation.
Seven malformed layouts and seven semantic memory-fault cases test rejection.

Struct instance-call validation covers 132 runtime comparisons, including short and full argument
encodings, by-value copy isolation, direct constructor calls and a call to an `init` accessor,
which is also proved as an entry, and with the marker declared locally or by another
System.Runtime version. A universal instance store/load proof rejects an incorrect
implementation. Four malformed metadata cases test rejection. For the `init` modifier, `modopt`,
another `modreq` type, a same-named marker in another namespace and a value-returning or
parameter placement are rejected by name, both as an entry and behind its caller; selectors and
recorded entries distinguish the accessor from a plain void setter, and both members of a
modifier-only pair are rejected. An `init` accessor export is rejected as non-static.

Struct construction validation covers 56 runtime comparisons for packed and nested structs,
chained and parameterless constructors, zero-initialized storage and checked arithmetic faults.
A universal constructed-value proof covers every 64-bit input and rejects an incorrect result.
Five malformed constructor cases test rejection. Semantic tests cover zero-sized construction,
missing arguments, zero initialization and a non-void constructor result.

F# validation compares .NET execution for addition, unsigned branching, managed calls,
mutable structs and by-reference stores across 324 cases. The addition, store/load and constructor
contracts are checked against the F# assembly. Subtraction must fail the addition contract,
and a list-returning function must fail extraction. These examples use the shared CIL semantics.

## Contracts and extraction evidence

`Tests/StackAllocation.cs` extracts compiled pointer and span stack allocations, checks results
with and without localsinit, rejects uninitialized reads and escaped storage, and checks
insufficient-budget failure. Mutating the emitted initialization flag is rejected by the Lean
certificate. `Tests/StackAllocation.lean` covers alignment, repeated allocations and expiry;
`Tests/StackAllocationEvidence.lean` rejects forged flags, injected allocations, extra stack items
and non-native 64-bit size operands. These run in the `dispatch` suite.

These fixtures cover constrained and constant calls, all in the `dispatch` suite:

- `Tests/ConstrainedCalls.cs` checks compiled implicit and explicit struct-interface calls,
  including closed generic owners and mutation through the receiver, and rejects forged generated
  call targets, owner arguments and malformed prefix, branch and interface-constraint metadata.
- Explicit implementations with `in` aggregate and span parameters (`modreq(InAttribute)`) are
  proved as entries and through constrained generic calls, including a generic helper forwarding
  its own `in` span. `modopt`, another `modreq` type, by-value and nested placements, versioned
  and foreign modifier scopes and a slot reference without the modifier are rejected, as are a
  `ref readonly` return and both members of a modifier-only overload pair.
- `Tests/ConstrainedResolution.cs` checks the extractor's resolution rules.
- `Tests/ConstrainedEvidence.lean` independently checks Lean resolution, target, signature,
  ambiguity and prefix rejection, most specific interface bodies (derived over default, deepest in
  a chain, a body for a base abstract slot, the receiver's own override over all), diamond,
  re-abstraction and incomplete-closure rejection, a forged less specific target, a struct
  implementing another pin's interface and catalog entries outside their pin.
- `Tests/ConstantCalls.lean` checks that constant and computed flag getters prune only the block
  their word rules out, and rejects a swapped getter, a forged word, non-constant bodies and a
  callee certificate claiming a word its body does not compute.
- `Tests/ConstrainedCalls.cs` proves the pruned `ConstantFlags` and `ComputedFlags` entry points
  (conjunction, negation, a getter chain, generic type tests and derived-interface bodies) against
  the runtime, keeps a static-field getter live, rejects live, swapped and untracked flags, forged
  caller and callee certificates and a recursive getter pair, and prunes a getter computing false.
- `Tests/ConstrainedCalls.cs` also proves, against the runtime, compiled most specific bodies
  (`MostSpecificBodies`, the derived generic `SpendRefunding` and derived flag getters in
  `DerivedFlags`) and static slots on closed generic struct receivers (`GenericReceivers`: a
  type-argument flag that keeps or prunes its block, an implementation and an interface default
  whose interface is instantiated at the receiver's argument). It rejects a catalog listing
  another instantiation of that interface and an open receiver, rejects a compiled diamond,
  re-abstraction, unlisted base interface and live derived flag, and has Lean reject a catalog
  hiding the most specific `MethodImpl` or moving its interface outside its pin.

The core and universal-contract suites cover checked execution and memory preservation. Choose
and GenericIdentity preserve arbitrary caller memory exactly; Struct preserves preexisting caller
memory under its well-formedness hypothesis. Each unchanged contract rejects its incorrect
compiled implementation.

Extraction evidence validation covers Lean regressions, compiled certificate fixtures,
generated-evidence mutations and mandatory-certificate positive/negative checks.
`Tests/ImportEvidence.lean` accepts an external call into a matching import slot and rejects a
forged identity, parameter count, receiver or result shape, a wrong emitted argument count, a slot
index inside the program or past the table, constructor and generic sites, and managed or non-call
sites reaching the import range; the certificate audit also rejects a certificate over a different
import table. These tests do not establish full raw-CIL/runtime
correspondence.

The [pinned native evidence](evidence/native/README.md) records x64 and ARM64 observations, model
divergences, provenance and reproduction commands for the `native` suite.
[Store view reuse](VALIDATION-PROOFS.md#store-view-reuse) covers memory-view equivalence.

The initialized-types end-to-end test and four mandatory-certificate audit cases check that
verification reports record both the schema-3 extraction audit and initialized-type assumptions.
