# Excluded-branch certificate checks

The excluded-branch fixture retains the same compiled method, 802 excluded sites under the
scalar profile and 804 live sites under `x64-v3`. Both full certificates still compile at the
default heartbeat budget. The scalar certificate is compiled by the consumer verifier once,
rather than first compiling it separately and then compiling it again for that verifier.
Success-cache reuse is explicitly disabled for this verification so the scaling test always
performs that compilation. Its translation certificate and consumer proof are independently
replayed and audited as before.

The two negative cases now compile just the relevant `FeatureFlowValid` or `ParameterHomesValid`
obligation, preserving all generated definitions and the exact original mutation. They still
forge the last excluded instruction (site 803) and last excluded parameter load (site 801).
Each failure must report both the expected validator and `is false`, rather than succeeding
because an unrelated certificate obligation failed.

Both narrowed sources also have positive controls in the consumer proof module. These retain
their declarations and exact obligation types and reuse the original, fully checked certificate
theorems through `CheckedEvidenceControl`. Their axiom reports and independent replay are part
of that consumer verification; no validator is replaced or bypassed.

Serialized Windows runs on the same checkout and warm certified library measured:

| Work | Previous | Updated |
| --- | ---: | ---: |
| Complete fixture | 155.02 s | 84.97 s |
| Feature-flow negative | 23.65 s | 6.65 s |
| Parameter-home negative | 22.65 s | 4.63 s |
| Standalone scalar certificate | 23.58 s | Removed duplicate |
| Full live certificate | 26.42 s | 25.69 s |
| Consumer's full scalar certificate | 25.75 s | 24.56 s |
| Consumer proof compilation | 2.74 s | 14.74 s |
| Consumer joint kernel replay | 3.18 s | 3.74 s |

The positive controls add proof compilation work; the complete fixture still improves by
70.05 s (45%). Consumer stages are included in the complete fixture, not additional savings.
The updated run forces fresh certification, including on later repeated runs, whereas the
previous consumer verification allowed success-cache reuse. These are local measurements,
not predictions of hosted CI duration. Both complete runs passed, the updated logs contain
no `sorryAx`, and the final C# analyzer build passed.
