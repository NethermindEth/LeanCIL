# UInt256 composition measurements, November 2026

<!-- audience: maintainers -->

This report separates the integrated consumer workload from focused proof-source measurements.
The consumer keeps its arithmetic specifications, exact carry/borrow results, runtime assumptions,
finite checked return, permitted overlap and caller-memory guarantees. LeanCIL's CI uses in-repo
fixtures; consumer certificates and mutation tests run in
[int256 PR 141](https://github.com/NethermindEth/int256/pull/141).

## Shared interfaces and acceptance evidence

| Issue | Shared support and evidence |
| --- | --- |
| [#511](https://github.com/NethermindEth/LeanCIL/issues/511) | `WP.local_call` composes a real invocation with `LoopFrame.after_local_write`. `Tests.LocalCalls` allocates an unknown word beside a vector, calls wide multiplication and reloads the output. `Tests.VectorLocalCalls` covers an actual vector-writing helper beside a live scalar. Controls reject wrong homes, stale contents, uninitialized reads, aliases and escaped homes. |
| [#512](https://github.com/NethermindEth/LeanCIL/issues/512) | Existing forwarders and WP rules compose scalar, SSE and vector equality and reporting wrappers. `Tests.CallingFields` covers feature prefixes, reordered arguments, Boolean narrowing and discarded results. Cell preservation remains separate from `Confined`. |
| [#513](https://github.com/NethermindEth/LeanCIL/issues/513) | Checked operation facts drive scalar carry/borrow and SIMD execution. `Tests.SimdCarryCalls` shares the Add/Subtract proof shape and rejects wrong carry propagation, lane selection, early overlapping stores and changed helpers. Multiply uses the mixed-home transition. |
| [#518](https://github.com/NethermindEth/LeanCIL/issues/518) | `ValidCall`, `LoopFrame` and `LocalSnapshots` distinguish access from current contents. `WP.call_framed` derives named frame and allocation evidence from an arbitrary helper's actual invocation. `Tests.MethodContract.framed_opaque_call` requires no footprint assertion; it does not infer confinement. |
| [#535](https://github.com/NethermindEth/LeanCIL/issues/535) | `WP` is defined over the existing execution relation; loop, segment and contract interfaces use it. Ordinary success proofs use structural rules and checked stepping. Exact-prefix, fuel-limit and interpreter-rejection tests deliberately retain budgets because those are the properties being checked. |
| [#553](https://github.com/NethermindEth/LeanCIL/issues/553) | The consumer integrity fixture rewrites a compiled extraction during proof building and requires an integrity failure with module, part, hashes and preparation provenance. Both fresh and authenticated-restored batches preserve the unaffected sibling's certificate. This reproduces the integrity violation, not the historical intermittent trigger. |
| [#515](https://github.com/NethermindEth/LeanCIL/issues/515) | The complete workload and separate source, heartbeat, compiled-size and certificate-stage measurements are reported below and in the [paired pilot measurements](ProofCost.md#consumer-mixed-snapshots-and-wrappers). |

The local call rule replaces a written home's content evidence with the helper's checked readback.
Preserving another home requires the complete helper footprint and separation evidence. The
allocation rule retains existing descriptors and lifetime tokens; it supplies neither access
permissions nor old byte values. Missing-fact diagnostics distinguish access, current snapshots and
helper preconditions without treating an absent proof as a proved violation.

## Integrated certificate workload

The baseline is consumer `bd336618e23a32b29367642e43c02336a0a656c7`, with LeanCIL
`13740081296a751b03344238ae0123fd8dfcbd0b`, in
[run 42847051258](https://github.com/NethermindEth/int256/actions/runs/42847051258).
The integrated comparison is consumer `850ab571a69a7f16d32a5828d3f31e7b1be70d7f`, with LeanCIL
`8e44f531ef893fd4b253c24a6d95fb4cd15ffbbd`, in
[run 42923779913](https://github.com/NethermindEth/int256/actions/runs/42923779913).
That framework revision is included in merged LeanCIL `062d43b5`.

Both runs certify the same ordered 188 method/profile gates in eight shards. The integrated run's
supporting-theorem audit also passes. The verification workflow and gate selection are unchanged.
These timings are observations of different hosted runners and revisions, not a controlled
benchmark. The floating .NET SDK and runtime also differ. Stages can overlap, so their inclusive
durations must not be added or interpreted as elapsed workflow time.

| Stage | Samples per run | Sum before → after, seconds | Median before → after, seconds |
| --- | ---: | ---: | ---: |
| Extraction certificate | 188 | 3,355.73 → 3,218.15 | 11.265 → 9.513 |
| Fresh proof and dependencies | 188 | 1,041.66 → 804.59 | 2.746 → 2.990 |
| Joint kernel replay | 188 | 1,669.71 → 1,618.77 | 6.165 → 5.531 |
| Shared consumer support | 8 | 980.43 → 912.47 | 120.704 → 103.479 |

The lower aggregate proof time does not mean every proof got faster: its median increased.
These runs measure the integrated predecessor to the follow-up edits; they do not certify a later
consumer pin or measure its performance. No cancelled or failed run contributes to the table.

## Follow-up proof composition

Five consumer modules are measured before and after against the same compiled framework at
`4f0f3d6d`: `Safety.LocalCallSafety`, `Methods.Multiply.Calls`,
`Methods.Add.ScalarCarryPrefix`, `Methods.Subtract.ScalarBorrowSegments` and
`Methods.AddSubtract.Vector128Ripple`, all below `UInt256`. The source comparison is consumer
`850ab571` → `84aef6bc7850cc36782260571bcab831e03bdf8b`.
The comparison includes both shared consumer helper modules. It uses isolated elaboration for
deterministic proof-cost measurement; it is not a compiled-method certificate or a timing claim.

`WP.call_framed` replaces duplicate invocation-preservation proofs. Existing checked stepping
replaces hand-written instruction loops in the carry/borrow segments and the SIMD helper call.
Every declaration header, arithmetic statement, precondition and postcondition is unchanged.

| Measure | Before | After | Change |
| --- | ---: | ---: | ---: |
| Elaboration heartbeats | 75,236,514 | 67,252,419 | −10.61% |
| Kernel heartbeats | 5,551,839 | 4,813,077 | −13.31% |
| Proof objects | 187,512 | 140,006 | −25.33% |
| Compiled `.olean` bytes | 5,695,864 | 4,016,096 | −29.49% |

The consumer edits add 22 and remove 74 maintained proof lines, a net reduction of 52.
Generated source changes by zero. The shared upstream rule adds 27 production lines, separately
from its regression and documentation. Counting production proof source on both sides gives a
net reduction of 25 lines for this follow-up; test and documentation costs remain separate.
The complete upstream follow-up adds 55 net test/fixture lines across eleven files; production
C# and generated source are unchanged. Documentation is separate from those proof-source counts.
The full module measurements are retained in the consumer's
`verification/artifacts/composition-reuse/module-costs.json`.

The Subtract segment's elaboration heartbeats increase from 20,424,380 to 21,434,188 (+4.94%)
while its kernel cost and compiled size fall; the SIMD ripple module's elaboration heartbeats
increase 0.08%. These figures use rebuilt dependencies for the actual extracted scalar methods
and supersede preliminary measurements with reused consumer dependencies. The focused generic
closure passes 286 build jobs, and the extracted Add/Subtract chains pass 18 and 12 module checks.
These checks preserve the distinction between elaboration and final certificates.

The upstream helper is measured too, using the same frontend and compiled imports for the full
`CIL.Safety.MethodContract` source before and after. Its elaboration heartbeats increase from
37,964,679 to 38,163,356; kernel heartbeats from 823,969 to 832,798; proof objects from 35,119 to
35,861; and compiled bytes from 3,799,504 to 3,821,536. The new rule itself takes 193,088
elaboration heartbeats, 8,810 kernel heartbeats and 742 proof objects. Thus its one-time shared
cost is included explicitly rather than concealed by the consumer reduction. Raw frontend
reports are retained under `artifacts/int256/composition-rule/` in LeanCIL.

Including that complete upstream module with the five consumer modules, elaboration heartbeats
fall 6.88%, kernel heartbeats 11.45%, proof objects 21.01% and compiled bytes 17.46%. The combined
compiled totals are 9,495,368 → 7,837,632 bytes. This comparison counts the shared helper once.

### Upstream statement and success-proof migration

Thirteen ordinary success proofs stop choosing budgets manually. Five test interfaces replace
arbitrary postconditions and raw success continuations with exact `Segment` statements. Each
prefix executes three instructions; the segment retains the same state and every suffix result,
including faults. Two normal-outcome callers compose existing WP rules.

| `Tests.MethodContract` theorem | Statement lines | Outer binders |
| --- | ---: | ---: |
| `loaded_unsigned_branch` | 9 → 8 | 12 → 10 |
| `loaded_signed_branch` | 9 → 8 | 12 → 10 |
| `loaded_limb_branch` | 12 → 12 | 16 → 14 |
| `selected_widening` | 10 → 9 | 11 → 9 |
| `ordered_widening` | 12 → 11 | 13 → 11 |

This isolated ten-module source comparison passes 618 measured rows without threshold waivers.
Both sides use the same compiled framework. Elaboration heartbeats change from 365,787,934 to
363,956,374 (−0.50%); compiled bytes from 9,757,880 to 9,782,096 (+0.25%); maintained source grows
9 lines. The two outcome caller modules grow 2.0% and 3.3% in compiled size. Module totals do not
attribute bytes to individual theorems. Reports are retained under
`artifacts/wp-positive-cost/` in the measurement checkout.

Budget bounds, exact-cost interpreter behavior, invocation certificates and rejection diagnostics
still have explicit budgets and continuations in their dedicated tests. Outcome projection
helpers used by negative-postcondition tests also retain their existing witnesses. This is not
a claim that no file under `Tests/` contains a fuel witness.

## Source accounting

From consumer `bd336618` to `850ab571`, maintained proofs add 791 lines and remove 772, a net
increase of 19 across 69 files. Documentation changes by −63, C# fixtures/tooling by +11 and
configuration/data by +10; the whole diff is −23 lines. Production C# is unchanged. Earlier
consumer deduplication, axiom-print removal and manifest cleanup are already in the baseline and
are not counted again.

Including the follow-up consumer commit `84aef6bc`, the maintained-proof delta from `bd336618`
is −33 lines. This includes the earlier +19-line integration cost, rather than reporting only
the new 52-line reduction.

The corresponding upstream implementation, from `13740081` to `8e44f531`, adds 5,998 net lines:
1,711 in CIL production, 3,022 in tests/examples, 595 in documentation, 157 in C# production,
457 in tooling/configuration and 56 in generated/golden data. Thus the integrated migration is
not a system-wide source reduction. The smaller focused pilots in `ProofCost.md` include their
shared helper costs and must not be added to these totals.

The generated proof bindings retain the same certificate obligations. No arithmetic proof is
moved into LeanCIL and no certificate is replaced by a supporting-library build. Raw timing
artifacts and stage totals are retained in the consumer's
`verification/artifacts/ci-141/timing-comparison.json`; the CI runs linked above publish the
per-shard trace archives.
