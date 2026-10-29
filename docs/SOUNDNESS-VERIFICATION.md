# Trusted verification and artifact integrity

## Trusted computing base

The [trust table](SOUNDNESS.md#trusted-components-and-deployment-assumptions) identifies the trusted
components. Lean's admitted foundational axioms are `propext`, `Quot.sound` and `Classical.choice`.
Delivered correctness proofs cannot depend on sorry, custom axioms, native proof evaluation or
unchecked summaries. `rfl`, `decide` and `decide +kernel` produce kernel-checked evidence.
Build failure, missing audits or proof-resource exhaustion cannot produce a successful receipt.

Extraction reads compiled CIL, not a proved source-level semantics. Correspondence between the
model and actual CLR/JIT/hardware behavior remains assumed. The user's specification and its
quantifiers/preconditions determine the theorem's practical meaning.

## Preparation and shared infrastructure

| Mechanism | Required binding | Authority it does not provide |
| --- | --- | --- |
| Certified framework | CIL sources/configuration, platform, pinned Lean tools, producer manifest and independent trusted digest | Rehashing an untrusted artifact does not certify it. Transport must preserve its bytes. |
| Source-only extension | Existing sources/configuration/artifacts unchanged; added sources cannot shadow modules; stability checked before publication | Added helpers have no certified declarations until their ordinary compilation, replay and audit. |
| Incremental preparation | Authenticated donor and matching configuration; affected declarations rebuilt and required replay performed | Import analysis alone is not proof that arbitrary elaborator dependencies are tracked. |
| Factored extraction modules | Deterministic source transformation, exact regenerated input hash, compiled graph, stability and certificate audit | No proved Lean source-transformation theorem; module names alone grant no trust. |
| Import location resolution | Selected sidecar/DLL bytes checked against independent pins by extraction | deps.json, assets, RID graphs and location attributes are discovery inputs, not evidence. |

UTF-8 identity chunk proofs validate the emitted bytes and exact concatenation. They do not prove
that metadata decoding serialized the intended assembly identity. Preparation and distribution
commands belong in [CI operation](CI.md) and [validation](VALIDATION.md).

## Artifact integrity

The extractor reads assembly bytes without executing them. Selection and validation bind assembly
identity, target framework, Release metadata, method/type signatures, layouts, profiles and reachable
instructions. Ambiguous method selection fails before unsupported candidates can be filtered out.
Assembly SHA-256, MVID, canonical identity, extractor hash and generated-source hashes bind artifacts.
These checks establish identity and consistency, not semantic correctness of the extractor.

Verification requires regenerated extraction, compiled proof dependencies, kernel replay, extraction
certificate audit, selected theorem audit and final source/artifact stability. Generated code and
proofs use isolated module roots. A failed attempt removes its previous output report. Verification
settings select the theorem but are not evidence. Reports record the actual audited statement,
inputs and library identity; their prose is not an independent specification.

| Operation | What it establishes | Limit |
| --- | --- | --- |
| `leancil verify` | Full verification workflow for the selected theorem | Theorem hypotheses and runtime assumptions remain obligations. |
| Repository `--check` | Recorded selection and input/artifact identity | No kernel rerun and no signature against an attacker controlling the report/toolchain. |
| `leancil check` | Extraction artifact integrity | No user-theorem verification. |
| `leancil list` | Metadata method discovery | Listing does not imply admission or correctness. |
| `audit-library` | Kernel-replayed compiled declarations and namespace theorem audit | Not proof that a package build directory was compiled from its current sources. |

`Extracted.signatures` selects method indices and is hash-bound, not part of `TranslationValid`.
Bindings are kernel-checked against the actual program. PDB names and locations are similarly
untrusted selection aids: they cannot change `Extracted.lean` or its translation evidence.
Proofs importing `Symbols.lean` compile/replay it and bind its hash; forged names cannot make the
kernel prove a different statement. PDB bytes are not covered by the assembly hash.

### Cached artifacts and fingerprints

Certified framework artifacts are read-only inputs to private proof sessions. Local receipts
authenticate manifests; supplied manifests require independent trusted digests. Receivers also
check source/toolchain identity and rely on authenticated transport for base-byte integrity.
Installed tools and certified base files are not continuously rehashed. A concurrent writer able
to replace them, the driver or the checker is outside the model.

Consumer support reuse requires authenticated receipts, matching source and compiled-import
closures, file hashes and unchanged artifacts after building. Imports of `Extracted` and
`ExtractedSymbols` do not gain extraction-independent reuse authority. Restored extraction-dependent
modules and closed generated certificates still undergo required kernel replay when proof checking.
Certificate/theorem audits and extraction regeneration remain mandatory.

Canonical fingerprints deserialize every available olean part with the pinned Lean toolchain,
remove only the diagnostic `Lean.Linter.lintLogExt`, and reserialize. Constants, private declarations,
import modifiers, other extensions and source paths in definitions remain covered. Canonical files
are temporary hash inputs, never proof artifacts. A changed fingerprint invalidates dependents.

Normalization receipts bind module name, compiled-part presence and hashes, normalization policy,
toolchain and auditor identities. Local receipts additionally bind the verifier binary; portable
producer tables are covered by independently trusted certified manifests. Raw input/tool stability
is checked around normalization and publication. These caches reproduce fingerprints, not proof
success or source provenance. Fresh/disabled-cache requests bypass local normalization receipts.

Tracked environment keys cover Lean/Lake/elan configuration. Elaborator-specific dependencies on
other variables need `LEANCIL_CACHE_ENVIRONMENT` or `--fresh`. Kernel replay validates the output
when first certified; it does not infer every environmental dependency of arbitrary elaborator code.

### Batch isolation

Identical generated CIL may share build/replay work. Other requests share only certified
extraction-independent support. Support scheduling scans source imports, but the compiled import
graph and replay determine trust. Unrecognized import syntax and failed optional prebuilds fall
back to ordinary group work; they cannot certify unfinished modules.

Each request's audit loads its own replayed closure without running code, notations or elaborators.
A replay failure in that closure or its extraction certificate fails the request. Every
non-certified module built in a workspace is replayed before its outputs are shared.

## Theorem audit

Lean proof/publisher source can execute macros, elaborators, instances, `run_cmd` and initializers.
`leancil-audit`, built before proof elaboration, imports replayed oleans with extensions disabled.
It executes no proof-source code and places pinned toolchain modules ahead of proof search paths.
It requires theorem declarations, structurally compares explicitly required types/values without
unfolding or instance resolution, and computes axiom closure by walking declaration bodies rather
than trusting stored summaries. Namespace audit requests must match at least one theorem.
See [the auditor](../CIL/OleanAudit.lean) for the request/result formats.

Auditing is not type checking: it is sound only for bytes accepted by kernel replay. Isolated
replay follows the pinned Lean checker, including private parts, and uses separate target
environments. The driver binds compiled inputs, replayed files and audited files with identity and
stability checks. Certified modules can be exempt only under their authenticated closure policy.

Hashes do not contain a malicious build that leaves a process running or replaces tools between
checks. Untrusted source needs a disposable container/account, restricted writable state and
process-tree termination before verification continues. Nothing that build could modify may be
trusted afterwards. Printed theorem text also needs care: notation is disabled, but numeral
instances can affect interpretation; exact statements are guaranteed only where structural audit
explicitly checks the expected type.
