# Performance investigations

Measurements here describe their exact workloads, machines and validation boundaries.
Local gains are not automatically whole-job CI gains; inclusive stage times can overlap.

| Investigation | Report |
| --- | --- |
| Shared Lean installation and compression | [Toolchain distribution](ToolchainDistribution.md) |
| Authenticated certified-library transport | [Library distribution](LibraryDistribution.md) |
| Consumer harness compilation | [Consumer harness](ConsumerHarness.md) |
| Current-file declaration lookup | [Import declarations](ImportDeclarations.md) |
| Feature-flow mutation checks | [Evidence harness reuse](EvidenceHarnessReuse.md) |
| Long excluded-branch certificates | [Excluded-branch scaling](ExcludedBranchScaling.md) |
| Generic constraint certificates | [Generic evidence](GenericEvidence.md) |
| Typed runtime-case deduplication | [Runtime bits](RuntimeBits.md) |
| Embedding, scalar and span proof work | [Proof work](ProofWork.md) |

## Extraction and certificates

Generated external-call identities use shared, kernel-checked UTF-8 chunks. This avoids
re-encoding long assembly-qualified signatures while retaining exact byte identities and
all translation validators. See [validation coverage](../VALIDATION.md) for the fixed-input
compilation and replay benchmark.

Generic value-type constraints also share exact byte-backed identities between extraction
and validation. Their [equivalence proofs and measurements](GenericEvidence.md)
retain the original scoped metadata strings and rejection rules.

Published-interface declaration discovery uses Lean's local constant map for current-file
queries, avoiding scans of imported declarations while retaining ownership checks and
full-traversal regression coverage. See [import declaration measurements](ImportDeclarations.md).

Caller proofs can register proved interfaces with `@[cil_contract]` and use
`cil_contract_steps` to compose calls. The stepper checks the callee binding and
precondition and exposes the postcondition; it can also reuse proved child invocations.
See [contract composition](../PROOFS.md) for explicit and automatic call proofs.

Feature and division getter recognition use exact byte comparisons with kernel-checked
equivalence to their original signature rules. This reduces certificate replay work while
preserving metadata rejection. Feature-flow checks share an indexed classification of local
types and address exclusions, proved equivalent to the original metadata scans.
Managed-call certificates use structural equality proofs for
matching metadata, reducing repeated string comparisons during replay. Primitive metadata also
shares the exact runtime assembly identity. Reachable external calls reuse their complete
identities as checked UTF-8 byte constants, avoiding repeated decoding in the kernel. See
[certificate validation](../PROOFS.md).
Fold discovery indexes local-use counts once and bounds exception-message prefix scans;
both changes have exact equivalence proofs to the original checks.
Constrained dispatch compares linked UTF-8 byte keys and decodes ASCII metadata without repeated
indexed reads. Checked equivalence preserves Unicode handling and the original dispatch rules.

## Proofs and test reuse

Array, layout, parameter and generic fixtures batch independent extractions to share immutable
assembly reads and signature validation. Positive evidence also shares Lean imports in
generated batches, with independent kernel replay. Rejection batches restore Lean's environment
after each case and require that case's own expected diagnostics. The evidence suite compiles its
regression modules directly against the certified library, avoiding another CIL build.
See [validation coverage](../VALIDATION.md) for reproducible measurements.

Embedding proofs close impossible operand cases before splitting further, and control-flow
proofs eliminate impossible bind errors. Scalar evidence groups related checks to share metadata
reductions; span contract fixtures reuse the certificates checked alongside their execution tests.
The proof statements and rejection cases remain unchanged. See [proof timings](ProofWork.md).

Integer Math boundary tests encode all 21,804 runtime comparisons as checked data. A generic
execution proof covers every table entry, preserving narrowing and exact arithmetic faults
without elaborating a separate execution-proof application for each input.

Core consumer tests batch fixed rejection cases to reuse certified-library setup while keeping
source, environment and cache-invalidation checks isolated. Their harness compiles once and
dispatches each check to a separate process, avoiding repeated compilation of shared verifier code.
See the reproducible comparison in
[validation coverage](../VALIDATION.md).

Edited consumer proofs reuse authenticated extraction preparation without starting a redundant
certificate build. Rechecked proofs still independently replay and audit the generated certificate
and check that proof elaboration leaves its compiled bytes unchanged.
Generated certificate preparation also survives unrelated consumer package configuration changes;
its own generated sources, configuration, framework artifacts and toolchain remain bound.
Rejected joint replays use native per-module checking, preserving isolated failure attribution
without elaborating a temporary checker script.

Prepared certified libraries include canonical fingerprints of their compiled modules.
Consumer verification reuses them only while module bytes and the normalizer match,
avoiding repeated framework serialization even when local receipts are disabled.

## Verification and CI reuse

Eligible standalone proofs, generated batches and consumer groups audit the environment returned
by kernel replay, avoiding a second import. Consumer groups retain each request's theorem and
dependency scope. Duplicate declarations and audits requiring source locations or module metadata
retain the separate audit path; theorem and artifact checks still apply.
After a merge, CI can reuse the same-repository PR head's certified library when its complete Git
tree matches the push commit. Source binding, artifact authentication and kernel replay still apply.
Main republishes the validated library under its own run so later PRs can reuse it too.

Standalone verification directly audits the generated translation theorem, as consumer verification
does, avoiding a separate wrapper compilation while retaining exact-type checks and kernel replay.

See [CI operation](../CI.md) and [validation coverage](../VALIDATION.md).
