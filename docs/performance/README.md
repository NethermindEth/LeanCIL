# Performance

<!-- audience: maintainers -->

These pages describe how to measure the cost of LeanCIL's proofs, library modules and CI
artifacts, with reference figures to compare against. Read the page for the part you are
changing before and after the change.

| You are changing | Measure | Page |
| --- | --- | --- |
| Tactics, lemmas or anything proofs elaborate against | Heartbeats and olean bytes per proof | [Proof cost](ProofCost.md) |
| `cil_instruction_equations`, or the code list of emitted methods | Heartbeats per instruction as methods grow | [Instruction lookups](InstructionLookups.md) |
| A slow proof inside a `CIL/` module | Elaboration time of that module | [Proof work](ProofWork.md) |
| Packing or restoring the certified library | Archive bytes, pack and restore time | [Library distribution](LibraryDistribution.md) |
| Packing or restoring the Lean toolchain in CI | Archive bytes, compression and restore time | [Toolchain distribution](ToolchainDistribution.md) |
| Fold discovery in `CIL/Extraction/Folds.lean` | Kernel time of role discovery | [Fold discovery](#fold-discovery) |
| Constructor binding in `CIL/Runtime/Net11WinX64`, or how `cil_evaluated` writes a package | Kernel time of one bound extraction and its consumer proof | [Bound constructor packages](#bound-constructor-packages) |
| A test suite or its harness | Suite seconds | [Suite times](#suite-times) |

## Reading a measurement

- Heartbeats, olean bytes, kernel heartbeats and proof objects do not depend on machine load.
  Compare them between any two runs on one toolchain.
- Wall and CPU time depend on the machine and its load. Compare two times only when both were
  taken in one session on one machine with nothing else running, and repeat each at least once.
- Stage times inside a suite overlap (a fixture time includes its Lean calls), and modules
  compile concurrently. Do not add stage or module savings to predict a job's time.

## Scaling suites

Four suites fail when cost grows faster than the size of the input. Run one with
`dotnet run --file scripts/Test.cs -- --suite <name>`.

| Suite | Fails when |
| --- | --- |
| `lookups` | Heartbeats per instruction grow more than 1.15 times from about 500 to about 2,000 instructions, kernel heartbeats per array element address grow more than 1.15 times from 128 to 512 addresses, kernel heartbeats per instruction of the scalar certificate or closed argument storage of bodies of 128 to 512 loaded, addressed or `calli` pointer locals grow more than 1.25 times, kernel heartbeats per instruction of the feature certificate of local loads, stores and addresses grow more than 1.25 times from 256 to 4,096 instructions or from 16 to 256 locals at a fixed length, the feature certificate's cost grows more than 4.5 times as much from 16 to 64 known local facts as from 4 to 16, the kernel heartbeats of one native method table step or one load of its first entry at 64 or 256 entries exceed 1.15 times those at 16 entries, the kernel heartbeats per index of a load of its last entry grow more than 1.15 times from 16 to 256 entries, the kernel heartbeats per byte of the call check's method name clause or of a metadata name's encoding grow more than 1.15 times from 20 to 80 or from 80 to 320 bytes, the kernel heartbeats per call of an embedding grow more than 1.15 times at four times the calls, or the heartbeats per call site of the managed-call check grow more than 1.35 times at four times the call sites; see [instruction lookups](InstructionLookups.md) |
| `stepping` | Checked stepping exceeds its per-instruction growth budgets; see [validation](../VALIDATION.md#proof-cost) |
| `scaling` | The certificate of a six-method call graph exceeds the default heartbeat limit, kernel heartbeats per layout of the header struct layout check over nested or over generic structs, or of a method's layout check over nested structs, grow more than 1.5 times from 64 to 512 structs, or 512 structs of either kind do not check within 8 GiB |
| `excluded` | Certificates with hundreds of excluded and live sites exceed the default heartbeat limit |

## Suite times

`scripts/verification-durations.json` includes each suite's verification and verified-output
measurement on the hosted runner. The file records the source run and any substituted time.
Print the resulting jobs and their estimated minutes with:

```sh
dotnet run --file scripts/EstimateVerificationSchedule.cs -- --jobs
```

A job's summary and each suite's transcript report the suite's verification time; see
[CI operation](../CI.md).

### Gate manifests and class hierarchies

These local benchmarks isolate two repeated walks in the extractor. The gate benchmark loads
one manifest with one profile. Each variant compares its program with the next variant, and
the last compares with production. The class benchmark asks for all admitted bases of one
class in a pinned Cecil module. Each generated ancestor has no methods.

| Operation | Input size | Before | After |
| --- | ---: | ---: | ---: |
| Load gate manifest | 256 variants | 59–60 ms | 48–57 ms |
| Load gate manifest | 1,024 variants | 270–275 ms | 223–232 ms |
| Load gate manifest | 4,096 variants | 1,574–1,634 ms | 880–881 ms |
| List admitted bases | 16 ancestors | 17–18 µs | 2 µs |
| List admitted bases | 64 ancestors | 231–235 µs | 8 µs |
| List admitted bases | 256 ancestors | 3,503–3,870 µs | 31 µs |

Each endpoint is a median of five warmed samples on Windows x64 with .NET 11.0.100 and
tiered compilation disabled. The second pair of measurements reversed the build order.
Gate times include parsing, path validation and row creation. Neither benchmark runs Lean.

Gate validation follows each comparison edge once and indexes its target by profile and
variant. For *V* variants and *R* rows, this part of loading takes expected O(V + R).
Listing bases previously validated the whole remaining lineage at each ancestor. It now
validates the lineage once and returns the same ancestors in nearest-first order.

### Strict-binding parent validation

The dispatch auditor resolves each physical parent from the pinned metadata. If every parent
row precedes its child in the combined table, every edge strictly decreases and every chain
reaches row zero. The auditor checks those edges in one pass. For other row orders it records
the depth of each completed parent chain and reuses that depth at later children. Lean proves
that a successful depth check returns the same result as following every row to its root.
If a chain cannot be certified, the original walk reports its cycle or invalid-row diagnostic.

These kernel rechecks used the same generated chain and a single proof of successful
validation on Lean 4.35.0. The original walk makes *n(n + 1)/2* parent visits on a chain of
*n* rows. The ordered pass checks *n* edges.

| TypeDef rows in chain | Original kernel heartbeats | Ordered pass kernel heartbeats |
| ---: | ---: | ---: |
| 32 | 3,606,393 | 36,391 |
| 64 | 25,098,083 | 67,403 |

The ordered pass took 129,420 heartbeats at 128 rows and 253,447 at 256 rows. These measurements
cover the parent validation step. Catalog reconstruction also reads metadata, selects descendants
and checks their methods.

On the existing `StrictFixture.Shape.Sides` catalog, the complete-declarations proof took
11,166,578 kernel heartbeats, down from 11,214,183 (0.42%). Its parent, abstract-flag and
virtual-flag mutation proof took 39,224,620, down from 39,416,500 (0.49%). Both builds used
the same fixture bytes, test sources and dependencies. The fixture has a shallow hierarchy.

### Dispatch descendant selection

After validating the complete parent graph, the auditor computes a membership bitmap on the
first virtual dispatch query for each owner. Rows that share an ancestor reuse its answer,
including when that ancestor lies outside the owner's subtree. A balanced map bounds the
classification work at O(n log n) for *n* physical rows in either metadata order. Walking from
every candidate independently took O(n²) parent visits on a chain. The verifier reads catalog
members in physical row order and checks the target table at each reachable call site.
Exact-class queries select the owner directly. Each queried virtual owner retains one bitmap
for the lifetime of the parent graph.

The chain benchmark selects the middle owner and checks the exact increasing list of physical
rows. Both implementations use the same parent array and Lean 4.35.0. Parent-first order places
the base at row 1. Child-first order places it at the last row.

| TypeDefs | Parent order | Original selection kernel heartbeats | Cached selection kernel heartbeats |
| ---: | --- | ---: | ---: |
| 32 | Parent first | 3,675,215 | 978,990 |
| 32 | Child first | 6,462,326 | 944,263 |
| 64 | Parent first | 25,295,118 | 2,383,656 |
| 64 | Child first | 47,341,238 | 2,240,354 |

At 256 rows, cached selection took 13,107,449 heartbeats in parent-first order and 12,054,085
in child-first order. Measuring validation and selection in the same proof accounts for kernel
work shared by the two stages. At 64 rows the combined cost fell from 25,322,903 to 2,407,356
heartbeats in parent-first order and from 48,073,695 to 3,958,929 in child-first order.

Across every parent assignment for one through five rows, with zero and one out-of-range
target available, all 7,035 owner selections in 1,441 valid forests matched the original
walk. All 16,806 invalid graphs produced the same error and row.

The four physical dispatch fixtures used the same SDK-built images, proof sources and
Lean dependencies on both runs. The totals include all 40 existing theorem rechecks.

| Physical fixture | Theorems | Original kernel heartbeats | Updated kernel heartbeats | Reduction |
| --- | ---: | ---: | ---: | ---: |
| Shape.Sides declarations and mutations | 2 | 50,391,274 | 50,370,738 | 0.041% |
| Class tests | 12 | 201,840,419 | 201,773,537 | 0.033% |
| Two-assembly catalogs | 14 | 411,777,022 | 411,466,946 | 0.075% |
| Dispatch overrides and pins | 12 | 276,392,086 | 276,196,212 | 0.071% |
| Total | 40 | 940,400,801 | 939,807,433 | 0.063% |

Compiling the verifier module itself took 24,795,458 frontend heartbeats, up from 22,502,699.
Rechecking its own theorems took 510,405 kernel heartbeats, up from 463,545. This cost is paid
when building the library.

### Class field slot lookup

The extractor indexes inherited and declared fields once per class reference in each read-only
layout pass. For a class with F fields and A slot requests, field enumeration and lookup take
expected O(F + A) work, down from O(F × A). Class validation and proof checking are separate costs.

On Windows x64, each scan looked up every field in reverse order and checked its slot. The indexed
times include building the index from scratch. Each process took the median of five samples of
at least 100 ms. The second pair of processes reversed the build order.

| Fields | Original scan | Indexed scan | Original bytes allocated | Indexed bytes allocated |
| ---: | ---: | ---: | ---: | ---: |
| 16 | 0.0197–0.0198 ms | 0.0022 ms | 22,968 | 2,808 |
| 64 | 0.1911–0.1919 ms | 0.0057 ms | 263,736 | 7,008 |
| 256 | 2.3092–2.3319 ms | 0.0187 ms | 3,807,288 | 23,976 |

Full extraction timings include process startup. Across three interleaved runs per version,
the median went from 390 to 373 ms for a method reading 256 fields and from 907 to 608 ms
for 1,024 fields. It went from 371 to 375 ms for `ItemPool::Rent` and from 334 to 346 ms
for `Examples.Objects::Describe`. Both extractors
emitted byte-identical Lean evidence and symbols for every measured input.

## Fold discovery

`docs/performance/fold-roles/ThrowScaling.lean` measures the kernel evaluating `foldRoles` on
4,096 message loads with no admitted throw fold. The statement uses `decide +kernel`;
[fold discovery](../VALIDATION-EXPORTS.md#fold-discovery) bounds the scan at each message load.

Build the imported module, then time the file:

```sh
lake build CIL.Extraction.Folds
lake env lean -Dprofiler=true docs/performance/fold-roles/ThrowScaling.lean
```

To check scaling, double the size (`4096`, at each occurrence in the file) in a scratch copy
and compare. The time should about double; a fourfold increase indicates an unbounded scan per
load. There are no reference figures for this file. The `lookups` suite checks addressed locals
with a failing limit.

## Bound constructor packages

A single caller whose throw is bound to a CoreLib constructor defines `boundPackage` with
`cil_evaluated` (see [proof binding](../PROOFS-BINDING.md)). The kernel evaluates the binding
once, in `boundPackage_eq`, and checks the package rows once, in `Extracted.translation_valid`. Every
later check, in the extraction or in a consumer proof, reads the literal. A proof that reduces
`managedPackage` rather than `boundPackage` evaluates the binding again, about 6 s per check.

After the `evidence` suite has written `artifacts/Throws/Percent`, time the extraction and its
boundary proof:

```sh
dir=artifacts/Throws/Percent
sep=:; [ "$OS" = Windows_NT ] && sep=';'
lake env lean -Dprofiler=true -Dprofiler.threshold=100 -o $dir/Extracted.olean $dir/Extracted.lean
lake env sh -c "LEAN_PATH=\"\$LEAN_PATH$sep$dir\" lean -Dprofiler=true $dir/BoundaryProof.lean"
```

Reference figures for `Examples.Throws::Percent(uint)` on one Windows x64 workstation, as the
range over four runs:

| Declaration | Kernel time |
| --- | --- |
| `boundPackage_eq` | 5.2 to 8.6 s |
| `Extracted.translation_valid` | 6.4 to 10.1 s |
| All of `Extracted.lean` | 12.1 to 19.5 s |
| All of `BoundaryProof.lean` (four `translation_valid.invoke` goals and one program lookup) | 0.7 to 1.3 s |

Checking the eight rows, the caller and seven CoreLib methods, takes about 6 s of `Extracted.translation_valid`.

### ItemPool.Rent

`ItemPool::Rent()` binds a caller in a multi-method program to six CoreLib rows. For the
same scalar extraction on Windows x64 with Lean 4.35.0, the full generated module cost:

| Measurement | Merged main | Checked body and rows | Checked whole caller and rows |
| --- | ---: | ---: | ---: |
| Frontend heartbeats | 581,810,172 | 213,492,476 | 181,647,462 |
| Kernel recheck heartbeats | 534,376,031 | 186,944,740 | 154,762,131 |
| Frontend heartbeats for the entry method's evidence theorem | 92,559,531 | 305,996 | 313,273 |

Checking the body and rows took 27.1–29.0s to compile and 24.2–24.9s to replay, against
75.3–88.6s and 79.7–81.5s for the original. Each version compiled and replayed twice in
alternating order (original, changed, changed, original). Its olean grew from 3,083,024 to
3,308,584 bytes. The complete `pool` suite fell from 17m56s to 9m40s with that change.
The suites ran once each in separate checkouts on the same workstation, with the same example
DLL and kernel-replayed library. Their runs overlapped. Suite time excludes tool builds.

With the final library, another pair of builds in the same alternating order compared the
original extraction with the checked whole caller. Original compiles took 93.8–105.7s,
against 35.0s for each final compile. Original kernel replays took 96.8–102.1s, against
30.1–53.3s for the final replays. The other verification runs shared the workstation.
The final olean was 3,240,768 bytes, 5.1% larger than the original.

The final complete `Tests/ItemPool.cs` run took 7m33s with the certified library already built,
the same example DLL and successful-proof caching disabled. It exercised Rent, IsIdle, both
profile templates, the moved-row rejection and every IL mutation. Against the original
17m56s suite run, this was a 58% reduction on the workstation.

Checking the whole bound caller also shares the computation between its original method, body
and links. Its equation costs 16.8 million frontend heartbeats. Reading the original method
and the body costs about 8,000 each. The kernel checks the runtime row equation once.
The evidence, attribution, static identity and translation theorems then read those checked values.
The runtime validation theorem still checks the rows. Its frontend cost fell from 53.4 million
to 27.7 million heartbeats.

Run the pool suite to generate the extraction, then collect the per-command profile:

```sh
dotnet run --file scripts/Test.cs -- --suite pool
lake env lean --run scripts/ProofCost.lean Extracted \
  artifacts/ItemPool/Rent/Extracted.lean artifacts/ItemPool/rent-cost.json
```
