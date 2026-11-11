# UInt256 composition measurements, November 2026

<!-- audience: maintainers -->

Snapshot-aware checked stepping removes consumer execution bookkeeping while retaining arithmetic,
exact carry/borrow flags, finite checked return, permitted overlap, runtime assumptions and
caller-memory guarantees. UInt256 arithmetic remains in the consumer. The implementation and
migration are in [LeanCIL #554](https://github.com/NethermindEth/LeanCIL/pull/554) and the existing
[int256 #141](https://github.com/NethermindEth/int256/pull/141).

## Consumer source and proof costs

The baseline is consumer `bc1cc19f78f3b5faed2c50a0e75f6ed3036025ad`; the measured migration is
`8fbb1fba00efe56a9e0c5c0cde2ed98cf0d8ed75`. Both sides use Lean 4.35.0 and the same compiled framework implementation
from LeanCIL `a5ecdca0`. The corrected measuring frontend is in `e5cfed26`.
All twelve baseline and candidate modules pass independent elaboration with that frontend.
It collects errors from every command and nested snapshot, so a failed proof followed by a
successful command cannot produce a report. Earlier failed experiments are excluded.

The counts include the shared consumer definitions added by the migration. Module names are
relative to `UInt256.Methods`, except `UInt256.Safety.InputLocalSafety`. Heartbeats measure work,
not elapsed time. Compiled bytes cover each module's `.olean` parts.

| Module | Source lines | Elaboration heartbeats | Kernel heartbeats | Compiled bytes |
| --- | ---: | ---: | ---: | ---: |
| `Add.ARMSmallPrefix` | 308 → 31 | 59,074,670 → 1,119,553 | 2,369,133 → 1,423 | 2,570,632 → 227,848 |
| `Add.ARMSmallState` | 470 → 173 | 8,878,354 → 3,992,340 | 794,184 → 421,546 | 1,021,400 → 426,016 |
| `Add.ARMSmallContract` | 256 → 282 | 7,661,932 → 52,214,239 | 292,914 → 1,189,092 | 516,360 → 900,000 |
| `Add.PortableSmall` | 625 → 565 | 83,635,328 → 60,639,834 | 4,631,499 → 3,864,408 | 2,787,072 → 1,504,616 |
| `UInt256.Safety.InputLocalSafety` | 49 → 35 | 1,295,165 → 1,312,202 | 48,570 → 41,130 | 109,072 → 87,440 |
| `Multiply.FullSafety` | 952 → 673 | 44,438,054 → 70,890,731 | 7,433,627 → 7,160,617 | 1,609,952 → 1,632,904 |
| `AddSubtract.RippleState` | 107 → 171 | 1,973,783 → 4,636,534 | 205,337 → 401,066 | 257,928 → 411,376 |
| `AddSubtract.Vector128Ripple` | 244 → 245 | 22,962,693 → 24,246,760 | 1,134,457 → 1,020,435 | 1,065,248 → 775,344 |
| `Add.SSERepair` | 271 → 174 | 4,989,138 → 2,287,394 | 352,452 → 59,910 | 530,928 → 207,616 |
| `Subtract.Vector128Repair` | 275 → 177 | 4,922,934 → 2,259,917 | 351,525 → 60,357 | 537,824 → 214,480 |
| `Multiply.FullSafetyAvx2Top` | 227 → 106 | 22,146,207 → 40,562,085 | 1,991,658 → 1,433,220 | 1,333,872 → 511,304 |
| `Multiply.FullSafetyAvx512Top` | 48 → 45 | 11,005,142 → 16,478,130 | 506,303 → 448,426 | 475,400 → 262,128 |

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

## Shared cost and source accounting

Snapshot stepping adds **202 net production Lean lines** across `LocalSnapshotSteps`,
`SymbolicExecution` and `MethodContract`. It extends existing checked stepping and WP rules;
there is no second interpreter, wrapper engine or arithmetic model. The complete PR also includes
the earlier 27-line `WP.call_framed` rule: **229 production Lean lines**, counted once.

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

This table charges the complete upstream PR against only the new consumer migration, excluding
the earlier 52-line saving. Upstream changes are relative to main `062d43b5`; consumer changes
are relative to `bc1cc19`. Shared additions and tests are included, not just selected deletions.

| Source category | Net lines |
| --- | ---: |
| Maintained consumer Lean | −1,155 |
| Shared CIL proof/automation | +229 |
| C# verifier | +9 |
| Lean measurement tooling | +6 |
| Lean regression fixtures | +220 |
| C# regression harnesses | +168 |
| Documentation, both repositories | +192 |
| Generated source and configuration | 0 |
| **All categories** | **-331** |

Generated source changes by zero. The 188 method/profile registrations, independent arithmetic,
extraction bindings and mutation selections are unchanged. The earlier 52-line consumer reduction
is already in `bc1cc19` and is not counted again in the twelve-module comparison. Foundation PR
#546 added 5,998 net lines across production, tests, documentation and tooling; that is an earlier
interval, not source eliminated by this migration.

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

The exact upstream CIL tree passes all 544 library build jobs. The 396 paired rows for unchanged
shared tactic tests pass without cost waivers. The real-Lake generation regression, incomplete
closure rejection, and six fresh/restored integrity-mutation and sibling-isolation controls pass.
Changed C# files pass final IDE0005 analyzer builds. The integrity guard is unchanged.

The final workflow linked from [PR #141](https://github.com/NethermindEth/int256/pull/141) is the
certificate evidence; focused elaboration is not a compiled-method certificate. Baseline
[run 42933021229](https://github.com/NethermindEth/int256/actions/runs/42933021229) passes the same
188 registrations, audit and eleven regression jobs. It records 3,545.08 seconds summed extraction
preparation, 940.39 seconds proof building, 1,726.22 seconds joint replay and 1,027.47 seconds shared
support preparation. These inclusive stages may overlap. Separate hosted runs are observational
comparisons, not controlled wall-time benchmarks; do not add the stages as workflow elapsed time.

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
