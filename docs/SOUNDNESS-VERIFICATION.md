# Trusted verification and artifact integrity

## Trusted computing base

- Lean 4.35.0's kernel and its standard foundations. Allowed audited axioms are `propext`, `Quot.sound`, and `Classical.choice` only.
- The definitions faithfully representing the intended supported CIL/runtime behaviour. Their correspondence to .NET is a reviewed modelling assumption, not a formal CLR implementation proof.
- Mono.Cecil, the .NET runtime running the extractor, metadata/signature validation, instruction translation and source emission.
- The verifier, filesystem, SHA-256 implementation, elan/toolchain selection and process execution, for binding the compiled assembly to the generated definitions and checked theorem.
- The user's specification and interpretation of its quantifiers/preconditions. A theorem about one concrete input is not a universal contract.

The C# compiler/JIT is not assumed to prove a source-level contract. Extraction reads the compiler's
actual output, but executing that output on a real runtime still relies on the runtime
correspondence assumptions above. Hardware and platform implementation correctness are not proved
here.

No `sorry`, `admit`, new axioms, native proof evaluation, or unchecked correctness summaries are
used in the delivered proofs. `rfl` and `decide` generate kernel-checkable proofs; generated
evidence uses `decide +kernel`, which reduces the decision procedure in the kernel instead of the
elaborator, adds no axioms, and keeps certificates for long method bodies within the default
heartbeat budget. A failed build, unexpected diagnostic, resource exhaustion or missing audit is a
verification failure, not a successful negative semantic test.

## Preparation and shared infrastructure

`scripts/PrepareLibrary.cs <output> --extend <base> <trusted-manifest-sha256>` can add CIL source
modules to an authenticated base without changing its certified compiled declarations. Every
existing source and configuration file must match, and the base identity must match the current
platform and Lean tools. Added sources must not shadow any compiled module. The producer copies and
authenticates the old artifacts, binds all added source bytes in a new manifest, and checks source
stability before publication. The digest must come independently from a trusted producer;
self-rehashing corrupted artifacts cannot renew it.

The extension certifies no new declarations. When a proof imports an added helper, ordinary
compilation, kernel replay and theorem auditing still apply. Changes or removals of existing sources
require normal fresh preparation. This is not a general incremental build or an assertion that
arbitrary elaborator dependencies can be inferred from module imports.

External-call metadata identities are serialized as their UTF-8 bytes. Generated proofs check the
validity of bounded chunks and compose them with `ByteArray.IsValidUTF8.append`; the kernel also
checks that the concatenation is exactly the emitted byte array. Every existing signature and
instruction validator consumes that unchanged identity. As with other raw metadata fields,
correspondence between the serialized bytes and the assembly remains an extractor assumption.
Identity evidence consists of `externalIdentityNBytes_valid` and shared
`externalIdentityChunkN_valid` proofs.

Consumer batches may factor regenerated extraction source into content-named header and method
modules. This is a deterministic transformation in the trusted verifier implementation, not a proved
Lean source-equivalence theorem. The exact input hash is checked again before staging; all staged
sources and compiled artifacts participate in the existing stability checks. Lean still validates
the full program and call connections, and the compiled certificate is audited. Only unchanged
components with an authenticated source/import closure and unchanged artifact bytes can reuse an
earlier kernel replay. A matching module name alone never authorizes reuse.

`leancil resolve-imports` is untrusted location selection outside extraction. deps.json, NuGet
assets, the RID graph and the LeanCilContracts attribute only choose the sidecar and DLL paths
passed to `extract`, which never reads them. Extraction hashes the files it is given against the
independent implementation and interface pins, so a wrong selection can only fail, never certify
other bytes.

## Artifact integrity

Native isolated replay follows the pinned `LeanChecker.replayFromImports`: read every available
module part, import the exported imports without extensions, replay the most private part's
constants with `Lean.Kernel.Environment.replay`, then free the imported regions. Each target has its
own environment and failure report. The native wrapper also frees regions on failure; it does not
share declarations between independent targets.

The extractor reads assembly bytes without loading/executing the assembly. It checks the requested
assembly name or full identity, target framework, Release configuration, method/type metadata,
supported layouts, reachable call graph, feature configuration and instructions. Method selectors
resolve against all matching metadata methods before validation, including unsupported candidates.
C# aliases and omitted return types change only selection; ambiguity is rejected with full candidate
signatures, and the manifest stores the resolved canonical entry signature. Short assembly names are
matched exactly against the assembly metadata name; a supplied full identity must match in full. It
emits the assembly SHA-256, MVID, full metadata identity and instructions together with
generated-source and extractor-binary hashes.

The verification driver builds and kernel-replays a source-keyed library before publishing it to a
local cache. The key binds CIL sources, build configuration, platform and selected Lean compiler.
Cache manifests cover every cached file and are hashed when an entry is published; a receipt that
authenticates the manifest lets later runs read the entry in place. Each verification reads the
validated base in place as a path dependency of a private session package, so support and proof
builds write only inside that session. The producer hashes every file of a supplied certified
library into its manifest; a receiver checks only the trusted manifest digest, library key and
source binding, and relies on the artifact transport for byte integrity. The driver does not re-hash
the base or the auditor during a run; a process that can rewrite them could equally replace the
verifier or the toolchain, so such writers are outside this model. `--fresh` and CI runs bypass the
local cache; CI may instead reuse a library built by a run of the same commit or by a main push,
taking its digest from that run's log ([VALIDATION](VALIDATION.md)). Reports record the library key
and whether the base was freshly built or reused. The installed `leancil verify` command uses the
Lean sources bundled with the tool and the same verification implementation as the repository
scripts. Library builds use temporary directories; generated code and proofs use an explicit
isolated Lean module root. Within one process the driver may reuse that session only while source
hashes remain identical. Every generated program and proof uses a separate fresh module directory.
The generated module, proof module and privately built support modules are independently
kernel-replayed, so disabling kernel type checking during elaboration cannot manufacture a
successful report. Locally cached consumer modules that import `Extracted` are restored only to skip
rebuilding: they are always kernel-replayed against the freshly built extraction, which is itself
never restored. `Extracted.lean` omits the assembly hash; the extraction integrity check and the
report bind the actual assembly. Transitive theorem axioms are audited separately. Reports use
schema 3 and require an independently kernel-replayed extraction certificate as well as the selected
theorem; older reports must be regenerated. A report is written only after a second identity/source
check. A failed proof attempt removes the previous report at its output path.

The repository script's `--check` checks the report's selected theorem, proof/framework/tool inputs,
generated artifact and assembly identity. It does not rerun the kernel and is not a cryptographic
signature against a party able to forge the entire report and toolchain. `leancil check` checks
extraction artifacts only. `leancil verify` always reruns verification using the selected proof and
theorem. `verification.json` stores that selection separately from results, survives failed proofs
and is hashed into the report's inputs. An older report can supply the initial selection during
migration; neither settings nor an earlier report are proof evidence. The displayed statement is the
selected theorem's type as the theorem audit prints it, not a generated English claim of
correctness. It is printed without the proof's notations, so operators appear as their functions
(`HAdd.hAdd`); numerals still print as digits whatever `OfNat` instance they use, so a statement is
checked against a stated type only where an audit names one.

`Extracted.signatures` lists each method's emitted metadata signature in program order. It is
covered by the generated-source hash and the extraction integrity check, not by `TranslationValid`;
`CIL.MethodIdentity` uses it only to choose an index, and every binding it emits is a kernel-checked
`rfl` over the same `Extracted.program`.

`Symbols.lean` (`ExtractedSymbols`) holds PDB local names, scopes and sequence points. The PDB is
not under the assembly hash, so it is outside the trusted base and never affects `Extracted.lean` or
`TranslationValid`. `leancil check` compares it with the regenerated file only when a matching PDB
is present. `local_named` only chooses a slot number that the proof then states and the kernel
checks against `Extracted.program`; a stale or forged PDB can make a proof fail, not prove a
different statement. Verification compiles and kernel-replays the module only for proofs that import
it, directly or, in consumer packages, through their own modules, and binds its hash into the proof
cache key; consumer support caches never hold its importers.

`leancil list` is metadata discovery only. It includes methods whose types or instructions the
verifier does not support. Listing a signature does not bypass extraction validation or establish
any correctness property.

Portable consumer support manifests require an independently trusted SHA256 and bind the verifier,
framework, toolchain, source snapshot and compiled import closure. Schema 2 fingerprints deserialize
every `.olean`, `.olean.server` and `.olean.private` part with the pinned Lean toolchain, remove
only the `Lean.Linter.lintLogExt` diagnostic extension, then reserialize with Lean's compactor and
hash the result. This extension records linter messages and source locations, not kernel
declarations. All constants (including private declarations), import modifiers and other extensions
remain covered. Source paths inside definitions are retained. A changed fingerprint invalidates all
dependents. The consumer is still built from fresh sources, extraction-dependent modules are
replayed, and raw artifact hashes are checked for stability across fingerprinting, replay and
theorem audit. Canonical files are temporary fingerprint inputs and are never loaded as proof
artifacts.

Canonical normalization receipts may be reused across verifier processes. Each authenticated receipt
binds the module name, freshly hashed presence and bytes of every compiled part, the verifier
policy, toolchain release, Lean executable and auditor executable. Files of an installed release are
not rehashed; a same-user writer is outside the model. Cache misses normalize private copies whose
hashes match that snapshot; input and tool identities are checked again before publication. Cached
values preserve the exact linter-stripped fingerprints and do not certify source provenance or proof
success. Source/import closure checks, raw artifact stability checks, theorem audits and required
kernel replay still run. Fresh and disabled-cache requests do not use or publish local receipts.

A prepared certified library can supply the same canonical transformation results in
`canonical-fingerprints.json`, covered by its independently trusted manifest digest and
source/toolchain binding. The producer pins this table before publishing the artifact; the receiver
pins it before executing consumer code. Reuse requires the exact module name, presence and raw hash
of every compiled part, plus the normalization schema, native auditor, toolchain release and Lean
executable hash. These bindings are rechecked after normalization. The transformation schema is
independent of the producer/receiver driver assembly, so the repository preparation script can
supply the packaged verifier without treating their different binary identities as interchangeable
proof policies. Local receipts still bind the complete verifier binary. Framework fingerprints grant
no additional certification or replay exemption: each consumer's existing source, import and proof
checks remain mandatory.


Local consumer support generations are a cache, not part of the trusted base. A restored module is
reused only when its local HMAC receipt and every file hash verify, its recorded source hashes and
compiled imports match the current snapshot, and Lake leaves its bytes unchanged after the build;
otherwise every module is replayed. Each such artifact was kernel-replayed (or restored under the
same rules) by an earlier successful verification. The key binds the variables Lean, Lake and elan
read, not the whole process environment: an elaborator that reads another variable is not tracked by
Lake's own traces either, and its output is still kernel-replayed when first certified. Name such
variables in `LEANCIL_CACHE_ENVIRONMENT`, or use `--fresh`.

These receipts also retain compilation outputs for `Extracted` and `ExtractionAudit`, bound to the
exact generated program and audit source through their compiled import closure. When a consumer
proof is rechecked, restored certificates and their extraction-dependent importers still undergo
kernel replay. The certificate and theorem audits, extraction regeneration, assembly hashes and
source-stability checks remain mandatory.

A separate generation contains only the closed generated certificate module set. Its key binds all
generated sources, the generated package configuration, certified framework artifacts and the same
toolchain/environment inputs. It can survive unrelated consumer package configuration changes, but
restores no consumer-owned modules and grants no replay exemption. Publication requires unchanged
generated inputs after successful verification.

Batch verification shares a source snapshot across requests. Requests with identical generated CIL
share a workspace build and kernel replay; other groups may share only certified
extraction-independent support. Each request's theorem audit loads only its own proof module's
replayed oleans and runs none of their code, so no request's notations or elaborators can affect any
printed statement or axiom report. A request fails for any replay failure in its own import closure
or in the extraction certificate, and every non-certified module in the workspace is replayed.

For multi-extraction consumer batches, the first workspace prebuilds support found in all requests'
source import closures. This scheduling scan recognizes repeated import commands, including
`public`, `meta`, `import all` and nested comments; ambiguous sources and unrecognized syntax remain
ordinary per-group work. The scan grants no trust. Every built module enters the compiled import
graph and kernel replay, including modules outside the first proof's closure. Only after replay,
theorem audits and source/artifact stability checks pass are extraction-independent artifacts shared
with later workspaces. The compiled graph excludes indirect imports of `Extracted` and
`ExtractedSymbols` even when their source imports were not recognized by the scheduling scan. Failed
optional support builds do not bypass normal group builds or certify their unfinished outputs.

## Theorem audit

Proof and publisher Lean source is untrusted. Elaborating it runs its code: `elab_rules`, macros,
instances, `run_cmd` and, in any module importing it, `initialize`. Audits therefore never elaborate
a module whose import closure contains such source, and never read its output. `leancil-audit`
(`CIL/OleanAudit.lean`, built with the library before any proof) imports the replayed oleans with
`importModules (loadExts := false)`: no environment extension, attribute, elaborator, notation or
initializer from them runs, and toolchain modules precede `LEAN_PATH` so none can be shadowed. For
each requested theorem it requires a `theorem` declaration, compares its type structurally (after
removing metadata, without unfolding or instance resolution) with an expected expression when one is
given, computes the axiom closure itself by walking declaration bodies, ignoring the axiom summaries
stored in oleans, and reports a `Not (... .Holds ...)` refutation. It writes JSON that the driver
checks against the allowed axioms. Request and result formats are documented at the top of the
source; constants can also be required to have an exact value.

The audit does not type-check: it is sound only on bytes that kernel replay accepted. The driver
hashes every olean of the session library and the proof directory before building the proof,
requires the build to leave them unchanged and to add only the proof module's own oleans, replays
them, audits, and rehashes the set afterwards; the checker executable is hashed when the library is
built and before every run, and each audited module must resolve to the hashed file. This binds the
replayed and audited bytes against anything the proof build does while it runs. It does not contain
a build that leaves a process behind, which could exchange files between hashing and reading or
alter the toolchain, the checker or this driver. Building untrusted source must therefore run
isolated: a disposable container or user account, with its process tree ended before verification
continues and nothing it could write trusted afterwards.

A namespace request audits every `theorem` that the listed modules declare under given namespace
prefixes, by the same kernel-declaration walk, and reports the count; a prefix matching no theorem
is an error. `leancil audit-library` builds a Lake package, kernel-replays every module in the
import closure of the listed modules (skipping only CIL modules that, with every module they import,
are byte-identical to the certified library), audits those replayed oleans and requires them
unchanged afterwards. It certifies the replayed bytes, not that the package's build directory was
compiled from its current sources.

