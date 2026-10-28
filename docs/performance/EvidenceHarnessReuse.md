# Evidence harness reuse

The generated-batch failure controls now live in `RejectedEvidenceTests.cs`, alongside the
rejection-harness controls. They reuse its otherwise-valid theorem instead of checking a full
generic extraction twice. A valid first case still cannot hide an invalid second case. The
ordinary false proof must fail with `decide` / `is false`; the unchecked forged declaration
must compile and then fail independent `leanchecker` replay with a declaration type mismatch.
Generic extraction positives and all metadata mutations remain unchanged.

The focused existing script and analyzer rebuilds passed. The two moved controls took 6.07 s
locally, including independent replay. This is not a whole-suite timing comparison; CI runs
the broader suite.

## Discarded cross-fixture batching prototype

On Windows at `1eff818`, 12 captured real positive batches (113 cases) took 93.86 s separately
and 75.21 s through three bounded groups, including required independent replay. Every input
hash matched and the original batches reconstructed byte-for-byte. However, completion,
identity and replay regression controls added 10.72 s, leaving only about 7.9 s net improvement
for substantial new orchestration. The suite deferral API and its extra controls were discarded.
A direct pinned-Lean invocation also showed no material improvement over `lake env lean`.

Local investigation artifacts are under `artifacts/evidence-next`: `PositiveGroupsBench.cs`,
`BoundedBench.cs`, `AuditBatches.cs`, their logs and `final-consolidated-trace`. The bounded prototype helper depends on the discarded implementation.
