# Generic constraint certificate normalization

Generic evidence repeatedly compares the exact scoped `System.ValueType` and unmanaged
constraint strings. Normalizing their concatenated UTF-8 representations was a substantial
part of the specialization proofs for packed values, vectors, swaps and buffer helpers.
The validator and extractor now share byte-backed constants for those two exact identities.
Kernel-checked equality theorems identify them with the previous scoped strings; unknown
identities remain literal metadata. No constraint, runtime identity, mutation or proof limit
changes.

Generated constraint lists now refer to `Extraction.valueTypeConstraint` and
`Extraction.unmanagedTypeConstraint` instead of string literals. This is a generated-source
representation change only. Consumers inspecting these lists can use the corresponding
`_eq` theorems to recover the original strings.

Measurements used an isolated Apple M4 checkout, Lean 4.35.0 and the same authenticated
library preparation procedure, with no concurrent benchmarks. These are complete
`dotnet run --file Tests/GenericEvidence.cs` times, including positive evidence,
independent kernel replay, negative mutations and batch failure controls. Library
preparation occurred before timing in both variants.

| Full fixture | Original | Shared constraints |
| --- | ---: | ---: |
| First run | 35.09 s | 26.89 s |
| Repeat | 33.64 s | 26.75 s |

The improvement is 20–23% locally; hosted CI timings are not yet measured. Changing only
the validator constants took 33.59 s, so sharing the representation with generated evidence
accounts for most of the gain. Disabling asynchronous elaboration made the positive batch
slower (10.56 s to 11.48 s) and was discarded.

Both complete fixtures passed, including independent rejection of forged declarations.
The updated library also passed independent kernel replay. The exact-identity equality
proofs introduce no unchecked axioms. The extractor build with code-style analyzers
completed with no warnings or errors.

These measurements predate moving harness-only invalid-batch probes into
`RejectedEvidenceTests`. That fixture now reuses its existing valid control for those
probes; generic specialization claims and independent metadata mutations remain here.
