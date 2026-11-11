# Consumer packages and batch verification

Read this page when your proofs live in your own Lake package: it covers verifying a package
(`--proof-root`), catalogs and batches, the editor workspace and `watch`, what verification
caches and replays, library audits, and publishing or importing verified contracts. Single
commands and their output are in the [CLI reference](CLI.md).

| Task | Section |
| --- | --- |
| Verify a proof that imports your own modules | [Consumer proof packages](#consumer-proof-packages) |
| Verify every method, profile and proof of a project | [Run a proof catalog](#run-a-proof-catalog) |
| Verify a list of existing extractions | [Batch verification](#batch-verification) |
| Compile proofs without certifying them | [Check compilation](#check-compilation) |
| Edit a proof with live goals | [Proof-authoring workspace](#proof-authoring-workspace) |
| Share compiled support between machines | [Portable support across machines](#portable-support-across-machines) |
| Audit a Lean library's theorems | [Library audits](#library-audits) |
| Publish contracts for callers in other assemblies | [Publishing verified contracts](#publishing-verified-contracts) |
| Verify a caller against published contracts | [Published contract imports](#published-contract-imports) |

## Run a proof catalog

```text
leancil gates manifest.json [--method name] [--profile name] [--changed path]... [--check]
    [--fresh] [--rebuild-library] [--trace] [--parallel count] [--results results.json]
    [--format text|json]
```

`leancil gates` extracts every entry of an explicit catalog, then verifies them as one
[batch](#batch-verification). Paths for assemblies, `proofRoot`, `outputRoot` and custom
`@profile.json` files are relative to the manifest; proof paths are relative to `proofRoot`. Each
profile gets its own extraction and result, in
`<outputRoot>/<gate name>/<profile hash>/<variant name>`, where the gate's own assembly is the
variant `production`. The generated batch manifest is `<outputRoot>/requests.json`.

```json
{
  "schema": 1,
  "proofRoot": "verification",
  "outputRoot": "artifacts/gates",
  "gates": [{
    "name": "add",
    "assembly": "bin/Arithmetic.dll",
    "method": "Arithmetic::Add(ulong,ulong)",
    "profiles": ["scalar", "x64-v3"],
    "proof": "Add.lean",
    "theorem": "Add.correctness",
    "variants": [{
      "name": "commuted",
      "assembly": "variants/Commuted.dll",
      "expect": "certifies"
    }, {
      "name": "wrong-operation",
      "assembly": "variants/Wrong.dll",
      "expect": "rejected"
    }]
  }]
}
```

Gate and variant names use letters, digits, `_`, `.` and `-` and must be unique ignoring case; a
variant cannot be named `production`, and `profiles` must not repeat a profile. Unknown manifest
properties are rejected.

Each variant applies the unchanged production proof to the variant assembly:

| `expect` | Passes when |
| --- | --- |
| `certifies` | The proof verifies against the variant, as for the production assembly. |
| `rejected` | The proof is rejected; no `verified.json` is left. A variant that verifies fails. |

A gate may also give `initializedTypes` and `typeArguments`, with the meaning of the `extract`
options `--assume-initialized` and `--type-argument`.

| Option | Meaning |
| --- | --- |
| `--method name` | Select gates whose `method` contains this substring. |
| `--profile name` | Select one exact profile name. |
| `--changed path` | Select gates affected by a changed file; repeatable, relative to the working directory. |
| `--check` | [Compile only](#check-compilation); an error when a selected variant expects `rejected`. |
| `--fresh`, `--rebuild-library`, `--trace`, `--parallel`, `--results`, `--format` | As for [`verify-batch`](#batch-verification). |

`--changed` selects as follows. Selection makes no verification claim about omitted gates, and a
selection that matches nothing is an error.

- A `.lean` file selects the proofs whose import closure includes it.
- A `.cs` file selects the gates whose extracted reachable methods have PDB sequence points in
  it. A gate without debug information, or with referenced assemblies, is selected.
- An assembly selects the gates extracted from it.
- A `.csproj`, `.props` or `.targets` file selects every candidate.

## Check compilation

`leancil verify-batch requests.json --check` compiles each proof and its import closure against
the selected extraction. It reports every request as `Checked` or failed, with source locations
for elaboration errors. Shared support is compiled once where possible, and the compiled
artifacts are private to the invocation. A compile check skips consumer kernel replay and the
theorem axiom audit, removes existing `verified.json` files and issues no certificate: it makes
no trust claim and does not replace verification. A request that expects `rejected` is an error
under `--check`.

## Consumer proof packages

For proofs split across a consumer's own Lean modules, pass the Lake package root:

```sh
leancil verify artifacts/Add --proof proofs/Add.lean --proof-root . --theorem MyProof.correctness
```

The package must depend on `leancil`, use the bundled Lean toolchain, and have a
resolved `lake-manifest.json` (`lake update`). Both `lakefile.toml` and
`lakefile.lean` are supported. Dependencies must be resolved git packages pinned
to full revisions, using the standard `.lake/packages` directory. The consumer's
CIL sources must match the verifier's bundled framework, allowing LF/CRLF
differences. Mismatches fail explicitly and name the revision to pin; `leancil --version`
prints that revision, the toolchain and the `[[require]]` block. Only `CIL.*` modules come
from the framework; LeanCIL's own example and test modules are not available to consumers.

Verification copies the consumer's Lean sources, Lake configuration and resolved
dependency sources into a temporary package, without trusting the package's compiled caches.
It supplies the selected `Extracted` module before Lake builds the proof and its
imports, so shared consumer modules can themselves import `Extracted`.

The report binds all copied `.lean`, `.toml`, `.json` and `lean-toolchain` files
and dependency revisions. Sources are checked again before writing the report;
new or changed consumer and dependency modules undergo kernel replay, and
the selected theorem's transitive axioms are audited with the same policy as
single-file verification. `verification.json` remembers the package root.

## Generated proof bindings

File-based C# runners can include [ProofBindingCatalog.cs](../scripts/ProofBindingCatalog.cs)
from their pinned LeanCIL package. A `ProofGate` names the exact method, profile, proof path
and theorem. Each `ProofBinding` supplies the complete Lean source from an explicit,
consumer-reviewed recipe. `ProofBindingCatalog.Sources` checks the recipe identities against
the catalog and rejects missing or duplicate entries, changed profiles or theorem names,
conflicting sources and unsafe output paths. Recipes cover every catalog profile of each
method they generate; other methods may keep handwritten proofs.

Call `ProofBindingCatalog.Materialize(root, catalog, recipes)` before selecting imports or
capturing verification sources. It emits deterministic UTF-8 files with LF endings. Pass
`check: true` to reject missing or changed bytes without writing files. Identical source shared
by several gates is emitted once. Proof-family recipes and arithmetic specifications belong
in the consumer; the catalog does not infer them from method names.

Generated files participate in the ordinary source identity, extraction binding and kernel
audit described above. Generation writes binding text; it discharges no proof obligation.
Use the extractor's [profile templates](PROOFS-BINDING.md#generated-profile-templates) for shared
extracted
bodies; binding recipes do not replace its reachable-helper or static-metadata checks.

## Proof-authoring workspace

`leancil workspace` generates one method's extraction into the proof's Lake package so the proof
file shows live goals in the editor; `leancil watch` keeps it current. The options of both are
in the [CLI reference](CLI.md#editor-workspace). Generate the selected extraction into the
package:

```sh
leancil workspace path/to/Library.dll 'Type::Method(parameter-types)' --profile arm64-advsimd --proof proofs/Method.lean --theorem MyProof.correctness --proof-root .
```

Use the exact assembly and method selector for the consumer build. The command
requires an explicit profile and proof. It finds the nearest Lake package when
`--proof-root` is omitted. Run `lake update` in that source package first. The
same pinned Git dependencies and framework/toolchain checks as consumer
verification apply. `--assembly` and `--assume-initialized` have the extraction
command's meaning. `--theorem` names the theorem `leancil watch` verifies.

### One module per method

Each selected method and profile gets its own module, so proofs of different
methods share a package and stay open at once. The command prints the import:

```text
Editor extraction: Workspace.Wide::get_IsZeroOrOne() (scalar)
  Import: import Extracted.Wide_get_IsZeroOrOne_1f0c2a9e, import ExtractedSymbols.Wide_get_IsZeroOrOne_1f0c2a9e
```

The module name is `Extracted.KEY`, and `ExtractedSymbols.KEY` for PDB names.
KEY is the method's type and name followed by the first eight hex digits of the
SHA-256 of the assembly's simple name, the method's full signature, the profile
name and the initialization assumptions, so a rebuild or an assembly version
change keeps it and overloads or profiles of one method get different keys. The
declarations keep the `Extracted` and `ExtractedSymbols` namespaces, so a proof
names `Extracted.program` whichever key it imports. The command warns when the
proof imports plain `Extracted` or another method's key and names the import to
use.

The editor library, `LeanCILEditor`, reads its sources from the package's
ignored `.lake/leancil` directory. In a package that pins `leancil`, the command
writes `.lake/package-overrides.json`, which Lake applies over the manifest: the
`leancil` requirement then resolves to `.lake/leancil-framework`, a lakefile
whose source and build directories are the certified library in the
[library cache](CLI.md#library-cache) and which brings in
`.lake/leancil-editor`, the package that declares that library, so the package compiles no
framework module and holds no framework build. The manifest and the pinned
checkout are untouched, and the command refuses a package that already has
overrides it did not write. On a machine without the certified library, the first
`workspace` builds it whole, as `verify --proof-root` would. For a package the library is
cached in CI too, where `verify` bypasses the cache, because the package must require a
library that stays on disk. The command
extracts the method, writes `Extracted/KEY.lean` and `ExtractedSymbols/KEY.lean`
there and builds them with Lake, so the import resolves in the proof and in any
helper module of the package, and Lake rebuilds helpers that import it when that
extraction changes. Other methods' modules are left as they are. A LeanCIL
checkout is the framework package: its lakefile declares the editor library and
it builds its own framework modules. A package the command generates declares
the library itself. No plain `Extracted` module is generated: a proof that names no
method fails at its import instead of checking against whichever method was
selected last. `ExtractedSymbols.KEY` exists only while the assembly has a
matching portable PDB. `selections/KEY/selection.json` records the selection
and its proofs. `leancil workspace --remove KEY` drops a method: it deletes that
directory, both modules and their Lake outputs, and rebuilds nothing. A method
selector in place of KEY works when it names one recorded profile, or with
`--profile`. `leancil new-proof` writes the keyed import, so a generated outline
resolves in the editor without editing.
Consumer sources named `Extracted.lean` or `ExtractedSymbols.lean`, or inside an
`Extracted` or `ExtractedSymbols` directory, are rejected because they would
shadow an extraction. That includes the output directory of `leancil extract`:
keep it outside the proof package, as the message says when it finds one inside.
A proof root that has no lakefile, or no `lake-manifest.json` because
`lake update` has not run there, is rejected with that cause and the fix.

The loop is:

1. Open the proof in the editor and edit it in place.
2. After changing and rebuilding the C# assembly, run the same `leancil workspace`
   command, or keep `leancil watch` running. Either regenerates the extraction in
   place; an unchanged method changes no file and rebuilds nothing.
3. Restart the file in the editor (Lean 4: Restart File) to load the new
   extraction. From a terminal, `lake lean proofs/Method.lean` checks the proof
   the way the language server does.

### Watch

```sh
leancil watch . --project src/Library/Library.csproj
```

`leancil watch [package] --project app.csproj...` keeps every selection the
package records current. It polls the projects' C# and MSBuild files, the
selected assemblies and the package's Lean sources. After a change it runs
`dotnet build` when C# changed, extracts each selection again into a scratch
directory, replaces the modules of the methods whose extraction changed and
builds those, then runs ordinary `leancil verify --format json` for each proof
whose extraction or sources (the proof, the package modules its imports reach
and the Lake configuration) changed since its last run. Each proof is verified
against its own copy of the extraction under `selections/KEY/proofs/`.
`--configuration` defaults to `Release`, `--once` runs one cycle and exits with
status 1 unless every proof verified or names no theorem, and `--format json` prints each cycle as
one JSON line.

`--goals` runs each verification with [`verify --goals`](CLI.md#goals-of-an-unfinished-proof)
and prints, under each proof, the goal at every `sorry`, before every failing tactic and left
unsolved, so a terminal shows what is left to prove after each save. The goals of a proof whose
inputs did not change are printed again from its last run, and each result's `goals` holds them
in the JSON line; without `--goals` it is `null`.

Each proof gets one status per cycle:

| Status | Meaning |
| --- | --- |
| `verified` | ordinary verification passed |
| `failed` | verification failed; the verify report locates each error in the Lean source and, for a stepping tactic, the C# line |
| `stale` | the C# build failed; its errors are listed with their C# locations, and every proof's earlier certificate is deleted |
| `missing` | the method no longer extracts (deleted or renamed); its editor modules are removed, so the proof fails at its import, and the selection stays recorded until the method returns or its directory is deleted |
| `unverified` | the selection names no `--theorem`; only the editor modules were refreshed |

A result whose inputs did not change is reported again with `rechecked` false.
That is a statement about byte-identical extraction text and sources, not a new
certificate: its `verified.json` still names the assembly it was verified
against. A failed build never leaves a green result, because it deletes every
certificate and the next good build verifies every proof again.

On Windows the command also checks that the environment `lake serve` hands Lean
fits Lean's 32,767-byte limit, and fails with the largest variables instead of
leaving the editor without `LEAN_PATH`; see
[environment size on Windows](CLI.md#environment-size-on-windows).

A proof with no `lakefile.toml` or `lakefile.lean` in its directory or above it
needs no setup. The command makes that directory a Lake package: it writes a
`lakefile.toml` that declares the editor library and a `lean-toolchain` beside
the proof, and runs `lake update` without network access. The package requires
`leancil` by `path` from `.lake/leancil-framework`, a lakefile whose source and
build directories are the certified library in the
[library cache](CLI.md#library-cache), so the package holds no framework
sources or build and is about 0.4 MB with one extraction. Building in the
package, `lake env lean` and the language server leave an up-to-date library
unwritten. Lake would rebuild a framework module it found out of date inside
the library, so `workspace` and `watch` fail if their build changed any file
there, and the next run checks the cache entry against its manifest and
replaces one that no longer matches. A
tool with different framework sources has a library under another cache key;
the next `workspace` or `watch` rewrites `.lake/leancil-framework` to name it,
building it first when absent. It creates no Git repository or commit, so Git
settings such as `commit.gpgsign` do not apply. Verification accepts only
dependencies pinned by a Git revision, so pass such a proof to ordinary
`leancil verify <extraction> --proof <file>` without `--proof-root`; `watch` does
that for such a package.

**Editor checking is not a certificate.** The workspace command writes no
`verified.json`, trusted support manifest or verification receipt. Run ordinary
verification on the same files:

```sh
leancil extract path/to/Library.dll 'Type::Method(parameter-types)' artifacts/Method arm64-advsimd
leancil verify artifacts/Method --proof proofs/Method.lean --proof-root . --theorem MyProof.correctness --fresh
```

Verification never reads the editor library. Its fresh source package skips
`.lake`, takes `Extracted` from the extraction it checks, and builds on a
certified library whose lakefile does not declare `LeanCILEditor`. For each
`Extracted.KEY` or `ExtractedSymbols.KEY` the proof's closure imports, it
generates a module containing only `import Extracted` (or `import
ExtractedSymbols`), after checking that KEY is the key of the extraction it
checks; a key of another extraction is rejected. The theorem and certificate
audits read `Extracted` itself, with extraction identity checks and
independent kernel replay. A forged or stale editor module therefore changes
nothing verification reads, and a certificate rests on the pinned `leancil`
revision.

## Local support cache

Successful runs locally certify extraction-independent support artifacts for reuse
across method gates.

**Cache key.** A support generation is keyed by:

- the effective Lake configuration files, ordered resolved import paths and dependency revisions;
- the `lean`, `leanchecker` and `lake` binaries, the certified framework's source identity
  and compiled module hashes, and the verifier;
- the environment variables Lean, Lake and elan read: `LEAN_*` except
  `LEAN_NUM_THREADS`, `LAKE_*`, `ELAN_*` and `RESERVOIR_*`. Unrelated variables
  such as `DOTNET_HOST_PATH` do not affect reuse. If consumer elaborators read
  other variables, list them in `LEANCIL_CACHE_ENVIRONMENT` (comma-separated).

**What is restored.**

- Lean sources are bound per module: each generation records, for every module,
  the hashes of its candidate source files, its compiled imports and its artifacts.
- A later run restores the largest import-closed set of modules whose sources are
  unchanged, so editing one helper or adding unrelated proof files keeps the rest.
- Modules that transitively depend on `Extracted` (but not on the extraction
  certificate audit or a proof module) are also recorded, bound additionally to the
  generated `Extracted.lean` text. `Extracted.lean` carries no assembly hash, so an
  assembly change outside the extracted program keeps it byte-identical. Each
  workspace then restores those modules for its own extraction, which skips their
  rebuild but never their kernel replay against the freshly built `Extracted`.
  The certificate still binds the actual assembly through the extraction integrity
  check and `assemblySha256` in the report.
- Lake still decides reuse from its own traces; if it rebuilds any restored
  extraction-independent module, every module is replayed again.
- An unchanged proof may reuse its authenticated successful result only for the same
  extraction identity, theorem and inputs; extraction integrity is checked again.

**Integrity.**

- A rebuilt framework with different compiled bytes cannot restore support from the
  previous build, even when its sources are identical. This includes generated extraction
  certificates, whose Lake traces depend on those compiled imports.
- Modified or unsigned cache files fall back to rebuilding and kernel replay.
- Republishing the same module set from a new session is a no-op, concurrent
  verifiers publish through an atomic rename, and a corrupt entry is replaced.
- `--fresh` disables both consumer caches while retaining the source-bound CIL library cache.
  Add `--rebuild-library` when the CIL library itself must be rebuilt.
- These receipts are local to the machine. A certified library supplied through
  `LEANCIL_CERTIFIED_LIBRARY` can supply the base library on another machine; see
  [library cache](CLI.md#library-cache).

**Storage.**

- Entries live in `success-v1` under the [library cache](CLI.md#library-cache) directory,
  `LEANCIL_CACHE_DIR`.
- Support generations hard-link files whose bytes an earlier generation already
  holds, so a new generation costs about its changed modules. Each entry is still
  authenticated on its own, and in-place damage to a shared file rejects every
  entry holding it.
- A generation not restored or republished for `LEANCIL_SUPPORT_RETENTION_DAYS`
  (default 7) is evicted when a later one is published, together with staging
  directories left by killed runs.
- A cache that cannot be written, for example on a full disk, prints a warning with
  its location and free space; the verification result stands.

## Replay

Kernel replay and the theorem audit run the pinned toolchain's `leanchecker` and the
library's `leancil-audit` directly with the `LEAN_PATH` that `lake env` resolves after
the build (and `LEAN_SYSROOT` set to that toolchain), instead of starting Lake again
for each step. The audit reads the replayed oleans and elaborates no consumer source. The
resolved import paths are still compared with those resolved before the build.

## Batch verification

```text
leancil verify-batch requests.json [--check] [--fresh] [--rebuild-library] [--trace]
    [--parallel count] [--results results.json] [--format text|json]
```

`leancil verify-batch` verifies many requests against one consumer snapshot in one session:

```json
{
  "schema": 1,
  "proofRoot": ".",
  "requests": [
    { "output": "artifacts/Add", "proof": "proofs/Add.lean", "theorem": "MyProof.correctness" },
    { "output": "artifacts/Mutant", "proof": "proofs/Refutation.lean", "theorem": "Mutant.refuted" },
    { "output": "artifacts/Mutant", "proof": "proofs/Add.lean", "theorem": "MyProof.correctness", "expect": "rejected" }
  ]
}
```

Paths are relative to the manifest. Each `output` is an extraction directory written by
`leancil extract` and must lie outside the consumer sources (for example under `artifacts/`).
A request's optional `expect` is `verified` (the default) or `rejected`. Unknown manifest
properties are rejected. `verify-batch` does not extract again: an output whose assembly changed
is reported as a stale input.

| Option | Meaning |
| --- | --- |
| `--check` | [Compile only](#check-compilation); no certificate. |
| `--fresh`, `--rebuild-library` | As for [`verify`](CLI.md#verify). |
| `--trace` | Trace every request's proof; see [trace the proof's steps](CLI.md#trace-the-proofs-steps). |
| `--parallel count` | How many workspaces after the first run at once. Default: processor count / 8, at least 1. |
| `--results results.json` | Write every outcome as JSON, in request order. |
| `--format json` | Print one JSON document instead of the per-request lines; see [batches](CLI.md#batches). |

**Output.** Each request prints `PASS verified`, `PASS rejected` or `FAIL` with its stage and
diagnostics as soon as its outcome is final (an unchanged-result cache hit, or the end of its
workspace), so lines follow completion order. The exit code is `0` only when every request met
its expectation.

- Only the last request for an output writes its `verification.json` and `verified.json`.
- Each `--results` entry has `output`, `proof`, `theorem`, `expect`, `status`, `stage`, `error`,
  `axioms`, `libraryBuild`, `failure` and `elapsedSeconds`. `failure`, and the `failed.json` of each
  failed
  or rejected output, hold the report described in [failure reports](CLI.md#failure-reports).
- `elapsedSeconds` is the time from the start of batch verification until that request's result
  is known, including shared preparation and waiting for earlier workspaces and excluding later
  workspace cleanup. Requests that share work can finish together, so do not sum these times as
  independent costs. Normal verification and compile checks report the same measure.

**Expectations.** A request with `"expect": "rejected"` passes only when its proof fails during
proof checking with unchanged inputs and an intact extraction. It stops there, never writes a
certificate, removes any earlier `verified.json` and writes `failed.json` describing the
rejection.

**What a batch shares.** The session takes one source snapshot, restores certified support once
and checks each extraction's integrity.

- Requests whose `Extracted.lean` is identical share one Lake workspace: one `lake build` of all
  their proof modules, one extraction certificate audit and one kernel replay of the union of
  non-certified modules. Requests with different extractions need separate workspaces because
  `Extracted` is a single module name.
- The first workspace certifies the extraction-independent support, and later workspaces reuse
  exactly those artifacts.
- Each request keeps an independent certificate. It is audited in its own Lean process importing
  only its own proof module, and it fails only for build or replay failures in its own import
  closure or in the shared extraction certificate.
- With `LEANCIL_EXPORT_CONSUMER_SUPPORT` set, a batch writes one
  [portable support](#portable-support-across-machines) manifest: the union of the
  extraction-independent support of every workspace that passed replay, audits and stability
  checks. A module whose bytes differ between workspaces is left out, together with its
  importers.

**Shared method evidence.** Related multi-method extractions reuse identical generated method
evidence within a batch. The verifier selects a first workspace containing the largest common
source body and factors its shared profile/layout header and method declarations into modules
named by their content hashes. Unique wrappers stay in `Extracted`, and a single extraction or a
group without shared method evidence is compiled as extracted.

- The regenerated source hash is checked before factoring. Component identities include their
  exact sources and imported component identities; the authenticated
  [support cache](#local-support-cache) also binds the framework, toolchain, verifier policy and
  source/import closure.
- Later workspaces copy only components whose complete source dependency closure matches.
  Changed artifact bytes prevent replay reuse.
- Call connections, constrained calls, the complete translation certificate, the compiled axiom
  audit and the final input checks run for every extraction.
- Only components of the first workspace are shared. Method indices are not renamed to find
  structurally equivalent methods, so unrelated groups can repeat evidence absent from that
  workspace. Generated components are not exported as portable support.

**Changed extraction module.** If a proof build changes an extraction's compiled module,
verification fails at `extraction integrity` and issues no certificate for that request. The
diagnostic names each changed module part and its before/after SHA-256 hashes, whether
preparation restored or built the certificate, the isolated package path, and artifact/trace
modification times and trace hashes. These details distinguish changed artifact bytes from an
ordinary unproved theorem; a timestamp alone does not establish why Lake rebuilt a module.

## Portable support across machines

A trusted producer can export the extraction-independent support it certified so that another
machine skips its kernel replay.

| Variable | Set on | Meaning |
| --- | --- | --- |
| `LEANCIL_EXPORT_CONSUMER_SUPPORT` | producer | Output directory. A successful consumer verification writes the manifest `<digest>.json` and its artifacts `<digest>.files/` there and prints the SHA-256. In GitHub Actions it also writes the `consumer-support-sha256` step output. |
| `LEANCIL_DISABLE_SUCCESS_CACHE=true` | producer | Disable local receipts. Needed when a new export is required, since an unchanged whole-proof cache hit skips publication. It does not disable a supplied portable manifest. |
| `LEANCIL_CONSUMER_SUPPORT` | receiver | Manifest path, or several separated by the platform path separator. |
| `LEANCIL_CONSUMER_SUPPORT_SHA256` | receiver | The independently trusted digest of each manifest, comma-separated in the same order (for example, a producer job output). Never derive it from an untrusted download. |
| `LEANCIL_RESTORE_CONSUMER_SUPPORT=true` | receiver | Copy the manifest's compiled artifacts before building, so Lake reuses them instead of rebuilding. |
| `LEANCIL_CACHE_ENVIRONMENT` | both | Extra variables that elaborators read, bound into the cache keys. |

No local receipt secret is exported. Each manifest is authenticated by its own digest: a missing
or incorrect trusted digest fails verification, and an incompatible manifest (another schema,
verifier policy, library, source snapshot or toolchain) falls back to replay. Reports record
`consumerSupportSha256` when portable support was used. `--fresh` bypasses portable reuse.

**What the receiver skips.** The receiver builds fresh sources. It skips kernel replay only when
the verifier, certified framework, installed Lean artifacts, normalized source snapshot, pinned
dependencies and **entire compiled support import closure** match the producer.

- Fingerprints use the pinned Lean serializer on all compiled module parts, excluding only
  `Lean.Linter.lintLogExt`: persisted linter diagnostics include temporary absolute source
  filenames. All declarations, imports and other extensions are covered, including source paths
  stored in semantic values.
- The compiled files are never rewritten, and their raw hashes must stay stable throughout
  verification. Environment differences are allowed only if the fingerprints match.
- A changed dependency invalidates every dependent module, even when a referencing theorem's own
  bytes are unchanged.
- Extraction-dependent modules and the public proof are always checked.

**Restoring artifacts.** A manifest names each module's compiled artifacts and their hashes,
plus a digest of the Lean, Lake and checker binaries and of the variables bound into local cache
keys (`LEAN_*`, `LAKE_*`, `ELAN_*`, `RESERVOIR_*` and those named in `LEANCIL_CACHE_ENVIRONMENT`;
values are never written). With `LEANCIL_RESTORE_CONSUMER_SUPPORT=true`, a receiver whose
binaries and bound variables match copies those artifacts before building.

- Each restored file must match its manifest hash, or verification fails. A manifest without its
  files falls back to a fresh build.
- Restored bytes are the producer's, as with local receipts: an elaborator that reads the source
  path or an undeclared variable keeps the producer's result. Declare such variables in
  `LEANCIL_CACHE_ENVIRONMENT`.
- Replay is skipped only for modules whose bytes match a manifest fingerprint.

**Framework fingerprints.** `scripts/PrepareLibrary.cs` records canonical framework fingerprints
inside the certified library. Its independently trusted manifest digest covers this table along
with the library sources and artifacts. A receiver reuses entries only for the same module name,
exact compiled-part presence and hashes, and matching normalization version, Lean executable and
native auditor bytes, toolchain release and runtime identifier. Relocating unchanged artifacts
does not invalidate them. Changed modules and tools fall back to normalization; changed
authenticated table bytes fail verification. This reuse of a pure byte transformation also
applies when local receipts are disabled or `--fresh` uses a supplied certified library. It does
not change portable support eligibility, source/import checks, theorem audits or kernel replay.

## Replay profiling

Set `LEANCIL_PROFILE_CONSUMER_REPLAY=true` with `LEANCIL_TRACE_DIRECTORY` to
record JSON timings for each replayed module. This invokes the pinned toolchain's
`LeanChecker.replayFromImports` serially, including each module's import loading.
It is a diagnostic mode, not a prediction of normal parallel checker throughput.
Normal consumer replay uses the same routine in parallel and records timings too;
the serial option isolates each module's cost. Both modes use the exact resolved
module list instead of repeatedly scanning the complete search path for prefixes,
and retain the final theorem/axiom audit and source/artifact stability checks.
Replay explicitly passes `LEAN_NUM_THREADS` to the Lean frontend (default two)
to bound concurrent imported environments; the frontend otherwise uses hardware
concurrency even when that environment variable is set.

## Library audits

`leancil audit-library` checks compiled library theorems through independent kernel replay and
native axiom auditing. An elaborated `run_cmd` audit or `#print axioms` output is insufficient,
because the audited code can forge that output:

```sh
leancil audit-library --project . --module MyLib --prefix MyLib. --prefix MyLemmas. \
  --axioms propext,Quot.sound,Classical.choice
```

- It runs `lake build` for each `--module` in the package, resolves `LEAN_PATH` with `lake env`, and
  takes the import closure of the listed modules outside the toolchain.
- Every module in that closure is kernel-replayed with the pinned `leanchecker` routine. A CIL
  module skips
  replay only when it and every module it imports are byte-identical to the verifier's certified
  library.
- `leancil-audit` then reads those replayed oleans with `loadExts := false` and audits every
  `theorem`
  they declare under a prefix: private theorems by their user name, auto-generated ones included. A
  prefix
  names whole components, so `MyLib.` and `MyLib` match `MyLib.foo` but not `MyLibrary.foo`.
- It fails when any prefix matches no theorem, when an axiom closure leaves `--axioms` (default
  `propext`, `Quot.sound`, `Classical.choice`), or when an olean changes during the audit.
  On success it prints the theorem count per prefix and the union of the axioms used.
- `--results results.json` writes the audited modules, counts, axioms and rejected theorems.

The package must pin the bundled Lean toolchain; it need not depend on `leancil`. Unlike `verify`,
the
audit reads the package's own build directory rather than a fresh copy, so it certifies the replayed
bytes,
not that they were compiled from the current sources. Building runs the package's Lake configuration
and
elaborators; the replay and the audit do not.

## Limits

These limits apply to verification of a consumer package (`--proof-root`, `verify-batch` and
`gates`). It supports Lean source packages; local path dependencies, custom Lake
cache directories, symlinked sources and native/precompiled dependencies are not
supported. Build/artifact directories (`.lake`, `.git`, `artifacts`, `generated`,
`bin`, `obj`, `.work`) and the selected extraction output directory are excluded.
Place handwritten proofs outside them.
`Extracted.lean` is reserved for the selected artifact; do not keep another copy
among consumer sources. Lake configuration and Lean elaborators are executable
code, so use this mode with packages you trust.

## Publishing verified contracts

```text
leancil export-contracts manifest.json [--output Lib.leancil.contracts] [--bundle directory]
```

A library producer runs `leancil export-contracts`. The command
checks every selected export with fresh ordinary verification, an exact canonical
contract theorem, extraction-certificate audit and independent kernel replay. It
publishes a sidecar only after every export and the final input checks succeed.
A caller imports the sidecar as [contract interfaces](CONTRACT-INTERFACES.md) describes.

```json
{
  "schema": 1,
  "assembly": "bin/Lib.dll",
  "proofRoot": "proofs",
  "interface": [{ "module": "Lib.Contracts", "source": "proofs/Lib/Contracts.lean" }],
  "exports": [{
    "method": "Lib.Library::AddOne(ulong)",
    "artifact": "artifacts/AddOne",
    "contract": "Lib.Contracts.addOne",
    "theorem": "Lib.Proof.addOne_correct"
  }]
}
```

Paths are relative to the manifest. Each artifact must already contain an
extraction identity and `verification.json` naming the author's proof source.
The recorded method must be the export entry, its DLL must match `assembly`, and
its execution profile must be an exact built-in profile. The consumer package
under `proofRoot` must have resolved pinned dependencies. One method may list
several artifact entries for different profiles; duplicate method/profile pairs
fail. Unknown and duplicate JSON properties are rejected. Each `interface` source
must be byte-identical to the module of that name under `proofRoot`, the module
the author proof compiled against, so the published text is what was audited.

The contract constant must have type `CIL.Safety.MethodContract` or
`CIL.Safety.OutcomeContract`. The named author declaration must be a theorem with
the exact canonical `Holds` proposition for the extracted program at entry zero.
An unrelated theorem, a proof definition, user-defined field notation or extra
assumptions do not establish this guarantee. The generated ExportAudit module
imports the exact author proof copy in the same fresh verification session.

Published interface modules must check with only the declared interface sources
and the bundled framework/toolchain. They cannot require private implementation
proofs or an `Extracted` module. Canonical contract closures are checked both in
this isolated interface and in the actual proof environment. Their exact results
must agree. Custom axioms, sorry and valueless opaque interface declarations are
not exportable. Contract predicates and their reachable definitions determine the
closure digest; the name alone does not determine it.

Exports are public or protected, static, non-virtual, closed methods. A non-generic method
over primitive types uses sidecar format 1; a closed instance of a generic method, selected with
`typeArguments`, uses format 2 (see [closed method instances](TYPED-IMPORTS.md)). Open generic
methods and methods of generic types are rejected.

- A separately compiled derived class can import a protected base method's contract for a
  statically resolved call. Metadata that disagrees with the deployed DLL's visibility is
  rejected. Virtual dispatch across this boundary is not supported.
- An export that calls another library's contract is certified conditionally on that import
  (`HoldsGiven ... ImportsHold`); see [transitive contract imports](#transitive-contract-imports).
- RVA static sites are supported. Each certification records the exact scoped static
  identities, and the producer checks their set against the generated program in Lean.
- Typed sidecars carry named initialization premises, scoped by assembly and profile, into each
  caller's generated identity and report.
- An extraction with recorded static-value assumptions cannot be exported. This restriction does
  not weaken the extractor's admission or profile rules.

Static identities are stable across separate extractions and body-only rebuilds.
They use the full assembly identity and full field name. `StaticWorldValid`
describes the fields in its descriptor list and permits other loaded immutable
fields in the same valid registry. Its `append`, `left`, `right` and `mono` lemmas
support worlds over the same memory. Append requires equal identities to name equal
descriptors, so two exports that read one shared table compose.

An export that can run after its tables are loaded, including a repeated call,
should take `StaticWorldValid published memory` as its precondition and restate it
for the final memory in its postcondition. `published` lists literal descriptors
(identity, assembly identity, field name and bytes) in an interface module. A
published descriptor that differs from the extracted one leaves the author proof
unprovable, so no separate equality audit is needed. `StaticIdentitiesAbsent`
suits only a first-use contract: after the first call the field is loaded and the
premise is false.

[Forced full verification](FULL_VERIFICATION.md) replays libraries with RVA tables against their
current DLLs and proves `linkChecked` for the composed program inside
`LeanCILFullComposition.certified`, which rejects conflicting descriptors and
names both fields. A published-certification import has no linked program; there
the extractor's static identity checks and the `StaticWorldValid` premises guard
collisions. The raw `link` API is a pure construction without that check.

**Output.** The default output is `<assembly-simple-name>.leancil.contracts` next to the DLL.
Use `--output path.leancil.contracts` to select another path. Publication is atomic
and a failed command leaves an existing sidecar unchanged. A sidecar binds the hash of the DLL
it was exported for and cannot certify a changed implementation. A
body-only rebuild can keep the same public interface and contract closure
digests while its implementation hash and certification change. Consumers
check the selected deployment bytes and independently pin the interface with
`--import-interface-sha256 Lib=<digest>`.

`--bundle directory` also writes an immutable content-addressed source bundle.
Its inventory binds the original producer inputs, complete consumer/dependency
source closure, exact bundled framework sources, generated extraction and audit
sources, and checked export statement metadata. The consumer's own
`.lake/packages/leancil` copy is omitted because `framework/` already pins those
sources. Every bundled file must still match the hash taken in the export's input
snapshot, which includes the framework sources; a change fails the export
before the bundle or sidecar is published. It contains no compiled DLL,
`.olean`, local receipt or build cache. The selected implementation DLL remains a
separate input. The bundle publishes before the sidecar, and its source locator
is recorded in the sidecar. A source bundle is not proof certification and is not
accepted as a trusted cache. Independent verification of a published library is
a separate workflow.

`bundle.json` also records `frameworkKey`, the strict compatibility key that the
sidecar carries, and `leanCilRevision`, the leancil revision pinned by the
producer's `proofRoot`. The revision is diagnostic: it names the sources to
rebuild with, while acceptance compares only the framework key and file hashes.
Any change to the framework sources under `CIL/` or to the toolchain changes the framework key,
so a verifier rejects sidecars and bundles exported with another framework. Re-export with the
verifier's LeanCIL revision, or verify with the revision the bundle records.

## Published contract imports

A consumer can verify a caller against an imported contract without the library's
implementation proof package. Supply the contract sidecar and independently
obtained implementation SHA-256 during extraction, as described in
[Contract interfaces](CONTRACT-INTERFACES.md). Only the interface source modules
are supplied to the consumer. The full-verification locator is not fetched.
`leancil resolve-imports` locates the sidecars and implementations in SDK output; see
[resolving imports](CONTRACT-INTERFACES.md#resolving-imports-from-sdk-assets). It only locates
files: the pins, caller audit, kernel replay and deployment obligations are required as without
it.

The interface stage compiles those sources, rejects undeclared dependencies and
forbidden declarations, and checks each canonical exported-constant closure.
It binds definition values, theorem types, inductive constructors and recursor
computation rules. A postcondition helper cannot change behind an unchanged name
and retain its old closure digest. Framework and toolchain stopping uses the
constant's defining module, not its namespace.

The App theorem must retain `HoldsGiven Extracted.program Extracted.ImportsHold
claim`. Its imported conditions use the canonical `MethodContract.Holds` or
`OutcomeContract.Holds` predicates at their absolute slots. The implementation
proofs are not elaborated or replayed. The axiom audit applies to the
caller theorem; imports are explicit hypotheses.

Schema-4 reports identify these imports as `published-certification`. They record
the accepted certification theorem and statement, current implementation digest,
interface digest and deployment obligation. The publisher's certification is an
explicit trust input. A digest does not prove that certification. Deployment must
provide the exact implementation and satisfy the imported contracts.

Proof reuse keys bind interface/closure digests, interface source bytes and
`ExtractedImports`, independently of library implementation hashes and provenance.
Each cache hit still checks current DLL/sidecar/profile identities and writes a
new report with current deployment records. `--fresh` bypasses proof reuse.
Reference-only input can check a caller proof for authoring, but exits with status
1 and produces neither `verified.json` nor a successful proof receipt.

## Transitive contract imports

A library can export a theorem conditional on its own imports. Its exact statement
is `CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold
(fun linked => CIL.Safety.MethodContract.Holds contract linked 0)`, with the
corresponding canonical `OutcomeContract.Holds` for an outcome contract.
The producer freshly checks that statement and records the dependency identities.
It does not claim that the open extracted prefix is closed.

Supply every graph node with `--import`, `--import-sha256` and
`--import-interface-sha256`; `--import-implementation` selects
its DLL path. A dependency record binds its full assembly identity, implementation
SHA-256 and interface digest. Each dependency must match the independently pinned
node. A shared dependency has one identity and one selected implementation.
Conflicting hashes, missing nodes and cycles fail before extraction. Cycle errors
name the complete cycle path.

The extraction identity records all nodes in `importGraph`. A verification report
records their deployment bindings in `contractDependencies`. Only methods actually
called by the selected App entry receive import slots. Published certifications
remain the stated trust boundary for library implementations; caller proofs remain
conditional on the published contracts. A source bundle or graph digest does not
prove that those contracts hold.

`MethodContract.relocateGiven` and `OutcomeContract.relocateGiven` turn a prefix
proof into a contract at a relocated entry. They require an explicit closed
completion, its prefix relation, satisfaction of imported contracts in that
completion, and a relocation of the completion into the target program.
Transitive graph implementation changes conservatively invalidate proof reuse.
Initialization premises propagate through these conditional exports. They remain
explicit runtime assumptions; forced full verification rejects them. Constructor-
initialized field values cannot be exported.
