# UInt256 composition measurements, November 2026

<!-- audience: maintainers -->

Snapshot-aware checked stepping removes consumer execution bookkeeping while retaining arithmetic,
exact carry/borrow flags, finite checked return, permitted overlap, runtime assumptions and
caller-memory guarantees. UInt256 arithmetic remains in the consumer. The implementation and
migration are in [LeanCIL #554](https://github.com/NethermindEth/LeanCIL/pull/554) and the existing
[int256 #141](https://github.com/NethermindEth/int256/pull/141).

## Whole-path proof measurements

The baseline is consumer `bc1cc19f78f3b5faed2c50a0e75f6ed3036025ad`; the measured migration is
`8fbb1fba00efe56a9e0c5c0cde2ed98cf0d8ed75`. Both sides use Lean 4.35.0 and the same compiled framework implementation
from LeanCIL `a5ecdca0`. The corrected measuring frontend is in `e5cfed26`.
All twelve baseline and candidate modules pass independent elaboration with that frontend.
It collects errors from every command and nested snapshot, so a failed proof followed by a
successful command cannot produce a report. Earlier failed experiments are excluded.

The counts include the shared consumer definitions added by the migration. Module names are
relative to `UInt256/Methods`, except `UInt256/Safety/InputLocalSafety.lean`. Heartbeats measure work,
not elapsed time. Compiled bytes cover each module's `.olean` parts.

| Module | Source lines | Elaboration heartbeats | Kernel heartbeats | Compiled bytes |
| --- | ---: | ---: | ---: | ---: |
| `Add/ARMSmallPrefix.lean` | 308 → 31 | 59,074,670 → 1,119,553 | 2,369,133 → 1,423 | 2,570,632 → 227,848 |
| `Add/ARMSmallState.lean` | 470 → 173 | 8,878,354 → 3,992,340 | 794,184 → 421,546 | 1,021,400 → 426,016 |
| `Add/ARMSmallContract.lean` | 256 → 282 | 7,661,932 → 52,214,239 | 292,914 → 1,189,092 | 516,360 → 900,000 |
| `Add/PortableSmall.lean` | 625 → 565 | 83,635,328 → 60,639,834 | 4,631,499 → 3,864,408 | 2,787,072 → 1,504,616 |
| `UInt256/Safety/InputLocalSafety.lean` | 49 → 35 | 1,295,165 → 1,312,202 | 48,570 → 41,130 | 109,072 → 87,440 |
| `Multiply/FullSafety.lean` | 952 → 673 | 44,438,054 → 70,890,731 | 7,433,627 → 7,160,617 | 1,609,952 → 1,632,904 |
| `AddSubtract/RippleState.lean` | 107 → 171 | 1,973,783 → 4,636,534 | 205,337 → 401,066 | 257,928 → 411,376 |
| `AddSubtract/Vector128Ripple.lean` | 244 → 245 | 22,962,693 → 24,246,760 | 1,134,457 → 1,020,435 | 1,065,248 → 775,344 |
| `Add/SSERepair.lean` | 271 → 174 | 4,989,138 → 2,287,394 | 352,452 → 59,910 | 530,928 → 207,616 |
| `Subtract/Vector128Repair.lean` | 275 → 177 | 4,922,934 → 2,259,917 | 351,525 → 60,357 | 537,824 → 214,480 |
| `Multiply/FullSafetyAvx2Top.lean` | 227 → 106 | 22,146,207 → 40,562,085 | 1,991,658 → 1,433,220 | 1,333,872 → 511,304 |
| `Multiply/FullSafetyAvx512Top.lean` | 48 → 45 | 11,005,142 → 16,478,130 | 506,303 → 448,426 | 475,400 → 262,128 |

Across the twelve modules, maintained source falls **3,832 → 2,677 lines (−1,155; −30.1%)**.
Elaboration is **272,983,400 → 280,639,719 (+2.80%)**; kernel work is
**20,111,659 → 16,101,630 (−19.94%)**; proof objects are **370,283 → 190,783 (−48.48%)**;
compiled bytes are **12,815,688 → 7,161,072 (−44.12%)**.

The ARM closure includes the prefix, state, contract and portable fallback: **1,659 → 1,051
lines**, a reduction of **608 (36.6%)**. Elaboration falls **25.9%** and kernel work **32.3%**.
`ARMSmallState` alone falls from 470 to 173 lines, but the closure count includes the larger
combined contract. A single WP path replaces nine prefix execution theorems. ARM and portable
execution share actual storage, snapshot and caller-preservation evidence. Unknown writable
homes still cannot be read before initialization.

The Add/Subtract repair pair shares five-home initialization and the actual output-storage call
and flag return. AVX2 multiplication composes mixed word/vector stores using existing vector
arithmetic rules. No removed arithmetic proof is relocated into LeanCIL.

The reduction comprises **589 theorem-header lines**, **413 proof-body lines** and **153 other
lines**. Named typed binder groups fall **1,308 → 708**. Add's SSE repair and Subtract's Vector128
repair each remove 26 header lines and 29 binder groups; shared initialization adds 16 header
lines and 21 binder groups once. The full Multiply path falls **952 → 673 lines** using one WP
predicate and local assertions, with kernel work **7,433,627 → 7,160,617**.

Externally checked arithmetic and invocation contracts are unchanged. Internal execution statements
may change from explicit existential continuations to WP, and duplicated internal setup/segment
declarations are removed. The pilot's percentage is not the entire proof library's reduction.

Source reduction does not make every proof cheaper. Full Multiply elaboration rises 59.5%, AVX2
83.2% and AVX512 49.7%, while their kernel costs fall. The larger ARM contract absorbs removed
prefix proofs; the four-file ARM total falls in both counters. The declaration comparator reports
15 regressions, not a blanket pass. The final Multiply call fact abstracts its four word arguments
before instantiation, avoiding repeated checking of expanded arithmetic expressions.

## Broader consumer reuse

Across the complete migration, maintained consumer Lean falls **43,299 → 39,450 lines**
(**−3,849; −8.9%**), including supporting proofs, handwritten bindings and unchanged Lean tests.
Supporting proofs alone fall **40,392 → 37,896**. This total includes the twelve-module migration
and all subsequent changes described below; it does not count ignored generated output as deleted
proof work.

The subsequent migration replaces 18 handwritten method-body definitions with specializations
of extracted, profile-parametric templates: **1,135 fewer maintained Lean lines**, or **1,097
fewer lines** after generator and lifecycle changes. One invocation of the existing template
emitter shares 28 managed methods across 20 root/profile extractions. Universal definitional
equality checks cover every flag and callee parameter, including the regression variants;
20 affected modules and the actual Add/Subtract vector proof chains elaborate successfully.

The manifest now generates **142 bindings**, including 79 previously handwritten bindings
whose 1,353 lines are reproduced exactly. Registry validation rejects missing, duplicate or
altered metadata. The same bindings and templates are materialized before source identity,
snapshot creation and compiled-library auditing. All 188 registrations and mutation selections
remain unchanged. Generated output still carries the same proof and extraction obligations.

Shared carry/borrow initialization removes another **53 lines** across five modules
(1,022 → 969), including all added adapters. Elaboration falls 30,166,998 → 27,951,875,
kernel work 2,581,166 → 2,424,223 and compiled bytes 2,661,808 → 2,563,864.
All 83 paired rows pass the existing cost policy without waivers. Charging the upstream
12-line writable-home projection once leaves 41 fewer lines and 89,528 fewer compiled bytes.
The 22 retained theorem headers are unchanged; the shared initializer accepts writable homes
while retaining its complete state conclusion.

AVX2 subtraction and its small scalar helper remove **15 private stepping bridges**, using
existing shared equations and checked stepping. The focused measurements below isolate those
changes from generated-body specialization. All 20 public theorem statements are unchanged.

| Module | Elaboration heartbeats | Kernel heartbeats | Compiled bytes |
| --- | ---: | ---: | ---: |
| `Subtract/Vector256Steps.lean` | 48,322,067 → 36,927,196 | 5,829,129 → 5,481,612 | 2,443,232 → 1,436,080 |
| `Subtract/Vector256Blended.lean` | 64,724,501 → 52,122,749 | 6,318,214 → 4,652,168 | 5,046,104 → 1,911,600 |
| `Subtract/SmallHelper.lean` | 47,265,520 → 35,239,798 | 2,656,281 → 2,703,742 | 1,253,616 → 1,390,728 |

The small helper shrinks 498 → 446 lines, but its compiled size rises 10.9% and its input-prefix
declaration costs 19.4% more elaboration. These are explicit tradeoffs, not blanket comparator
passes. The earlier twelve-module results are a separate snapshot; overlapping initializer
modules must not be counted twice.

## Shared cost and source accounting

Snapshot stepping adds **202 net production Lean lines** across `LocalSnapshotSteps`,
`SymbolicExecution` and `MethodContract`. It extends existing checked stepping and WP rules;
there is no second interpreter, wrapper engine or arithmetic model. The complete PR also includes
the earlier 27-line `WP.call_framed` rule, the 12-line writable-home projection and a 10-line
constructive byte-decoding repair: **251 production Lean lines**, counted once.

The three complete upstream modules are measured before and after the snapshot implementation:

| Measure | Before | After |
| --- | ---: | ---: |
| Source lines | 2,734 | 2,936 |
| Elaboration heartbeats | 181,423,311 | 199,397,383 |
| Kernel heartbeats | 835,411 | 878,575 |
| Proof objects | 36,027 | 36,314 |
| Compiled bytes | 15,407,144 | 16,873,640 |

Including these three complete upstream modules once, combined elaboration is
**454,406,711 → 480,037,102 (+5.64%)**, kernel work **20,947,070 → 16,980,205 (−18.94%)**,
and compiled size **28,222,832 → 24,034,712 bytes (−14.84%)**. The 27-line framed-call rule is
already in this cost baseline; its source cost is included in the complete PR accounting below.

The following accounting charges the complete upstream PR against the consumer migration,
excluding the earlier 52-line saving. Upstream changes are relative to main `062d43b5`;
consumer changes are relative to `bc1cc19`. Shared additions, tests, generators and documentation
are included, not just selected deletions.

| Source category | Net lines |
| --- | ---: |
| Maintained consumer Lean | −3,849 |
| Consumer generators/tooling | +452 |
| Consumer tests, configuration and documentation | +49 |
| Shared CIL proof/automation | +251 |
| Upstream measurement/verifier tooling | +36 |
| Upstream tests | +407 |
| Upstream documentation | +271 |
| **Maintained source, both repositories** | **−2,383** |

Generated bodies grow **642 → 2,279 lines**; generated bindings grow **1,354 → 2,707 lines**.
Their combined increase is **2,990 lines**. The additional bindings exactly reproduce removed
handwritten source; their generation reduces maintenance, not emitted source. Removing the
642 previously tracked generated lines is likewise excluded from the maintained-source saving.
Including all generated output gives **+607 net lines** across both repositories.
This distinguishes substantially less authored proof code from total generated source size.

The earlier 52-line reduction is already in `bc1cc19` and is not counted again. Foundation PR
#546 added 5,998 net lines across production, tests, documentation and tooling; that is an
earlier interval, not source eliminated by this migration.

## Issue evidence

| Issue | Consumer result and shared support |
| --- | --- |
| [#511](https://github.com/NethermindEth/LeanCIL/issues/511) | Actual private-home calls retain `WP.local_call` and footprint transitions. ARM/portable saves and mixed-vector multiplication use shared snapshots instead of bespoke frame structures. Unknown homes, stale contents, aliasing and lifetime checks remain obligations. |
| [#512](https://github.com/NethermindEth/LeanCIL/issues/512) | Scalar, SSE and vector equality and reporting forwarders retain their earlier migration; its 94-line saving is not counted again. The new shared repair suffix composes the actual storage invocation and flag return. Named call/frame evidence preserves the distinction between cell preservation and confinement. |
| [#513](https://github.com/NethermindEth/LeanCIL/issues/513) | Measured ARM/portable execution, the Add/Subtract SIMD repair pair and mixed-vector Multiply consume checked stepping and actual write facts. Controls reject wrong carries, lanes, stale snapshots, early overlapping writes and changed helper bodies. |
| [#518](https://github.com/NethermindEth/LeanCIL/issues/518) | Numeric homes and local snapshots carry initialized values through stores. Actual helper invocation supplies frame/allocation evidence; retaining bytes still requires a footprint. Automation cannot manufacture a snapshot after an arbitrary call. |
| [#535](https://github.com/NethermindEth/LeanCIL/issues/535) | The ARM path uses one WP execution proof, eliminating repeated segment headers and continuation binders. Add/Subtract repair shares setup and suffix proofs. Structural rules use the same execution relation and adequacy theorem. Budget/fault tests retain explicit budgets where those are the property tested. |
| [#553](https://github.com/NethermindEth/LeanCIL/issues/553) | A real Lake regression reproduces source-matching modules from different compiled generations forcing an extraction rebuild during proof checking. Restoration requires one authenticated, complete extraction generation; otherwise preparation runs before the integrity snapshot. The two historical intermittent incidents cannot be attributed retrospectively. |
| [#515](https://github.com/NethermindEth/LeanCIL/issues/515) | Source, statement, kernel and compiled-size results include shared consumer and upstream additions. The final consumer workflow retains all 188 certificates, the supporting-library audit and regression workload; results and timings are recorded on PR #141. |

## Validation and reproduction

The upstream CIL tree at `674b3e53` passes all 544 library build jobs. The 396 paired rows for unchanged
shared tactic tests pass without cost waivers. The real-Lake generation regression, incomplete
closure rejection, and six fresh/restored integrity-mutation and sibling-isolation controls pass.
Changed C# files pass final IDE0005 analyzer builds. The integrity guard is unchanged.

Upstream [run 42999679732](https://github.com/NethermindEth/LeanCIL/actions/runs/42999679732)
identified four failures: repeated fixed-reference compilation, a memory stepping fixture whose
byte-decoding dependency acquired `Classical.choice`, one compiler-generated closure missing from
the admission baseline, and abbreviated consumer filenames parsed as upstream Lean names.
The fixes retain the integrity check and strict axiom guard. The exact fixed-reference assertion,
unchanged memory fixture, refreshed admission baseline and documentation-name check pass locally.
Full-suite results belong to the subsequent CI run, not these focused reproductions.

Constructive byte decoding changes no statement or result form. Its isolated module costs rise:
420,092 → 903,411 elaboration heartbeats, 16,164 → 102,847 kernel heartbeats, 910 → 3,377 proof
objects and 39,208 → 81,400 compiled bytes. The 10 added source lines and checking cost remove
the unwanted axiom dependency; they are not reported as a cost improvement.

Consumer [run 42998596133](https://github.com/NethermindEth/int256/actions/runs/42998596133)
at `3b1df363` passes all 188 certificates and the supporting-library audit. This certifies the
initial whole-path migration, not the subsequent generator and proof-reuse changes. The current
workflow linked from [PR #141](https://github.com/NethermindEth/int256/pull/141) must check those
changes against the same workload; focused elaboration is not a compiled-method certificate.

The following observations compare baseline consumer `bc1cc19` / framework `d187e600`
([run 42933021229](https://github.com/NethermindEth/int256/actions/runs/42933021229)) with
consumer `3b1df363` / framework `f997a7c6`. Both certify the identical ordered 188 entries in
eight batches. All 16 jobs use runner 2.338.2 and Ubuntu 24.04 image 20261101.360.1; hosted
machines, regions and load differ. Neither run finds reusable main-branch support.

| Stage | Samples | Sum seconds, before → after | Median seconds, before → after |
| --- | ---: | ---: | ---: |
| Shared support build | 8 | 1,027.47 → 921.44 | 122.28 → 106.60 |
| Extraction certificate check | 188 | 3,545.08 → 3,131.09 | 11.568 → 10.963 |
| Fresh proof/dependency build | 188 | 940.39 → 883.44 | 3.195 → 3.299 |
| Joint kernel replay | 188 | 1,726.22 → 1,595.41 | 6.185 → 6.273 |

These inclusive stages may overlap. Their sums are not workflow elapsed time, and separate
hosted runs do not establish a causal speedup. Build and replay medians increase slightly.

To reproduce the source comparison, check out both consumer revisions, compile the framework
once, and run `scripts/ProofCost.lean` for each listed module in dependency order, with that
side's consumer imports and an output `.olean` path. The 84 unchanged dependency modules were
checked against source hashes; changed modules were rebuilt in separate directories. Count
physical source lines, including comments and blanks. Statement counts include theorem headers
through `:= by`; body counts start on the following line. Shared definitions are counted once.

Full command reports and source hashes are retained locally under consumer
`verification/artifacts/composition-final/paired-cost/`; upstream reports are under
`artifacts/int256/arm-small-pilot/` and `artifacts/snapshot-wp/`. These measurement artifacts are
separate from the public certificate trace archives linked on the pull requests.
Incremental initializer, vector and small-helper reports are under consumer
`verification/artifacts/ripple-initial-reuse/`, `verification/artifacts/vector256-reuse/` and
`verification/artifacts/small-helper-reuse/`; generator equality checks are under
`verification/artifacts/template-reuse/`. Their source intervals are recorded separately.
