# Consumer packages and batch verification

`leancil resolve-imports` derives `--import` and `--import-implementation` from
SDK deps/NuGet asset selection; see [resolving imports](CONTRACT-INTERFACES.md#resolving-imports-from-sdk-assets).
It only locates files. Pins, caller audits, kernel replay and deployment
obligations are unchanged.

The [README](../README.md#consumer-packages-and-batches) shows the commands. This page states what
consumer and batch verification check, what they reuse, and how support is shared across machines.

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
differences. Mismatches fail explicitly.

Verification copies the consumer's Lean sources, Lake configuration and resolved
dependency sources into a temporary package, without trusting the package's compiled caches.
It supplies the selected `Extracted` module before Lake builds the proof and its
imports, so shared consumer modules can themselves import `Extracted`. There is
no need to flatten the proof or put consumer files in LeanCIL's examples.

The report binds all copied `.lean`, `.toml`, `.json` and `lean-toolchain` files
and dependency revisions. Sources are checked again before writing the report;
new or changed consumer and dependency modules undergo kernel replay, and
the selected theorem's transitive axioms are audited with the same policy as
single-file verification. `verification.json` remembers the package root.

## Proof-authoring workspace

Materialize the same source package and selected extraction for editor tooling:

```sh
leancil workspace path/to/Nethermind.Int256.dll 'Type::Method(parameter-types)' --profile arm64-armbase --proof proofs/Method.lean --proof-root .
```

Use the exact assembly and method selector for the consumer build. The command
requires an explicit profile and proof. It finds the nearest Lake package when
`--proof-root` is omitted. Run `lake update` in that source package first. The
same pinned Git dependencies and framework/toolchain checks as consumer
verification apply. `--assembly` and `--assume-initialized` have the extraction
command's meaning.

The default output is `.work/leancil/<request-key>` under the source package.
Use `--output directory` to choose an external directory, or one under the
package's excluded `.work`, `artifacts`, `generated`, `bin` or `obj` tree. The
output must not already contain unrelated files.

Open the printed workspace directory with the Lean language server. Edit
`LeanCILProofWorkspace.lean`, or check it with:

```sh
lake build +LeanCILProofWorkspace:olean
```

The workspace copies source dependencies and configuration. It supplies
`Extracted` and, when the assembly has a matching portable PDB, `ExtractedSymbols`
as Lake targets. It does not import consumer build caches or certified artifacts.
The editor proof starts with exactly the selected proof's bytes. Editor changes
stay separate from the recorded generated/support sources.

Re-run the same workspace command before checking after an input change.
It hashes the assembly, PDB presence and bytes, extractor, profile configuration,
exact bundled framework sources and configuration, consumer sources, dependency sources
and pinned revisions. It also checks the
recorded generated modules, framework, Lake configuration and toolchain pin in
the workspace. Changed inputs or managed files cause an explicit rejection;
select a new `--output` directory after preserving proof edits. Reopening an
unchanged workspace preserves the edited proof and Lake build outputs. Editor
tooling itself does not watch or invalidate an external assembly automatically.

**Editor checking is not a certificate.** The command writes no `verified.json`,
trusted support manifest or verification receipt. Copy only the edited proof
source back to the original consumer proof path, then run ordinary verification:

```sh
leancil extract path/to/Nethermind.Int256.dll 'Type::Method(parameter-types)' artifacts/Method arm64-armbase
leancil verify artifacts/Method --proof proofs/Method.lean --proof-root . --theorem MyProof.correctness --fresh
```

Keep workspace generated files, caches and manifests out of that source package.
The ordinary verifier still requires extraction identity checks, its fresh source
package, exact theorem and certificate audits, and independent kernel replay.
The workspace root itself is not a supported `--proof-root` because it contains
reserved generated modules. The CI workspace fixture builds the real `Nethermind.Int256`
consumer at revision `00fcecf53e22b5c9090052779e14b3ba246fb117` and opens
`Nethermind.Int256.UInt256::get_IsZeroOrOne()` under the scalar profile. It uses the
existing `--assume-initialized Nethermind.Int256.UInt256` caller premise; assembly
and method admission rules are unchanged. The fixture checks transitive consumer and
symbol imports, then verifies the unchanged selected-method proof through ordinary fresh
verification. This tests workspace reproducibility, not an arithmetic contract for every
UInt256 operation.

## Local support cache

Successful runs locally certify extraction-independent support artifacts for reuse
across method gates.

**Cache key.** A support generation is keyed by:

- the effective Lake configuration files, ordered resolved import paths and dependency revisions;
- the `lean`, `leanchecker` and `lake` binaries, the certified framework and the verifier;
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

- Modified or unsigned cache files fall back to rebuilding and kernel replay.
- Republishing the same module set from a new session is a no-op, concurrent
  verifiers publish through an atomic rename, and a corrupt entry is replaced.
- `--fresh` disables both consumer caches.
- These receipts are local to the machine; the existing certified CIL producer
  artifact can still supply the base library.

**Storage.**

- Entries live in `success-v1` under `LEANCIL_CACHE_DIR` (default
  `<local application data>/LeanCIL/libraries`).
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

`leancil verify-batch requests.json` verifies many requests against one consumer
snapshot in one session:

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

Paths are relative to the manifest. Outputs must lie outside the consumer
sources (for example under `artifacts/`). The session takes one source snapshot,
restores certified support once and checks each extraction's integrity. Requests
whose `Extracted.lean` is identical share one Lake workspace: one `lake build`
of all their proof modules, one extraction certificate audit and one kernel
replay of the union of non-certified modules. Requests with different
extractions need separate workspaces because `Extracted` is a single module name.
The first workspace certifies the extraction-independent support and later
workspaces reuse exactly those artifacts; `--parallel count` bounds how many
later workspaces run at once (default: processor count / 8).

Each request keeps an independent certificate. It is audited in its own Lean
process importing only its own proof module, and it fails only for build or
replay failures in its own import closure or in the shared extraction
certificate. A request with `"expect": "rejected"` passes only when its proof
fails during proof checking with unchanged inputs and an intact extraction; it
stops there, never writes a certificate, removes the stale `verified.json`
and writes `failed.json` describing the rejection. As in sequential runs, only the last request for an output writes its
`verification.json` and `verified.json`. Each request prints `PASS verified`,
`PASS rejected` or `FAIL` with its stage and diagnostics as soon as its
outcome is final (an unchanged-result cache hit, or the end of its workspace),
so lines follow completion order; `--results` writes the outcomes as JSON in
request order. Each outcome's `failure` field and each failed or rejected
output's `failed.json` hold the classified, located failure report described in
[Failure reports](CLI.md#failure-reports). The exit code is 0 only when every request met its
expectation. With `LEANCIL_EXPORT_CONSUMER_SUPPORT` set, a batch writes one
manifest: the union of the extraction-independent support of every workspace
that passed replay, audits and stability checks. A module whose bytes differ
between workspaces is left out, together with its importers.

## Portable support across machines

For reuse across machines, set `LEANCIL_EXPORT_CONSUMER_SUPPORT` to an output
directory on a trusted producer. A successful consumer verification writes a
content-addressed JSON manifest and prints its SHA256. Give a receiver that file
through `LEANCIL_CONSUMER_SUPPORT` and the independently trusted digest through
`LEANCIL_CONSUMER_SUPPORT_SHA256` (for example, a producer job output). Never
derive the trusted digest from an untrusted download. No local receipt secret
is exported. In GitHub Actions the producer also writes the
`consumer-support-sha256` step output; the manifest filename is `<digest>.json`.
Run the producer with `LEANCIL_DISABLE_SUCCESS_CACHE=true` when a
new export is required, since an unchanged whole-proof cache hit skips publication.

The receiver still builds fresh sources. It skips kernel replay only when the
verifier, certified framework, installed Lean artifacts, normalized source
snapshot, pinned dependencies and **entire compiled support import closure**
match the producer. Schema 2 fingerprints use the pinned Lean serializer on all
compiled module parts, excluding only `Lean.Linter.lintLogExt`: persisted linter
diagnostics include temporary absolute source filenames. All declarations,
imports and other extensions remain covered, including source paths stored in
semantic values. The original compiled files are never rewritten, and their raw
hashes must remain stable throughout verification. Environment differences are
allowed only if these fingerprints match. A changed dependency invalidates every dependent module, even
when a referencing theorem's own bytes are unchanged. Extraction-dependent
modules and the public proof are always checked. Incompatible manifests fall
back to replay; a missing or incorrect trusted digest fails verification.
Reports record `consumerSupportSha256` when portable support was used.

Schema 3 manifests also name each module's compiled artifacts and their hashes,
shipped beside the manifest in `<digest>.files/`, plus a digest of the Lean,
Lake and checker binaries and of the variables bound into local cache keys
(`LEAN_*`, `LAKE_*`, `ELAN_*`, `RESERVOIR_*` and those named in
`LEANCIL_CACHE_ENVIRONMENT`; values are never written). Several manifests may
be supplied: separate the paths in `LEANCIL_CONSUMER_SUPPORT` with the platform
path separator and their trusted digests in `LEANCIL_CONSUMER_SUPPORT_SHA256`
with commas, in the same order; each manifest is authenticated by its own digest.
With `LEANCIL_RESTORE_CONSUMER_SUPPORT=true` a receiver whose binaries and bound
variables match copies those artifacts before building, so Lake reuses them
instead of rebuilding. Each restored file must match its manifest hash, or
verification fails; a manifest without its files falls back to a fresh build.
Restored bytes are the producer's, as with local receipts: an elaborator that
reads the source path or an undeclared variable keeps the producer's result.
Declare such variables in `LEANCIL_CACHE_ENVIRONMENT`. Replay is still skipped
only for modules whose bytes match a manifest fingerprint.
`--fresh` bypasses portable reuse too; `LEANCIL_DISABLE_SUCCESS_CACHE` disables
local receipts without disabling an explicitly supplied portable manifest.

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

`leancil audit-library` replaces an elaborated `Audit.lean` (`run_cmd` over `env.constants` with
`collectAxioms`, or `#print axioms`), which the audited code can forge:

```sh
leancil audit-library --project . --module MyLib --prefix MyLib. --prefix MyLemmas. \
  --axioms propext,Quot.sound,Classical.choice
```

- It runs `lake build` for each `--module` in the package, resolves `LEAN_PATH` with `lake env`, and
  takes the import closure of the listed modules outside the toolchain.
- Every module in that closure is kernel-replayed with the pinned `leanchecker` routine. A CIL module skips
  replay only when it and every module it imports are byte-identical to the verifier's certified library.
- `leancil-audit` then reads those replayed oleans with `loadExts := false` and audits every `theorem`
  they declare under a prefix: private theorems by their user name, auto-generated ones included. A prefix
  names whole components, so `MyLib.` and `MyLib` match `MyLib.foo` but not `MyLibrary.foo`.
- It fails when any prefix matches no theorem, when an axiom closure leaves `--axioms` (default
  `propext`, `Quot.sound`, `Classical.choice`), or when an olean changes during the audit.
  On success it prints the theorem count per prefix and the union of the axioms used.
- `--results results.json` writes the audited modules, counts, axioms and rejected theorems.

The package must pin the bundled Lean toolchain; it need not depend on `leancil`. Unlike `verify`, the
audit reads the package's own build directory rather than a fresh copy, so it certifies the replayed bytes,
not that they were compiled from the current sources. Building runs the package's Lake configuration and
elaborators; the replay and the audit do not.

## Limits

This mode supports Lean source packages; local path dependencies, custom Lake
cache directories, symlinked sources and native/precompiled dependencies are not
supported. Build/artifact directories (`.lake`, `.git`, `artifacts`, `generated`,
`bin`, `obj`, `.work`) and the selected extraction output directory are excluded.
Place handwritten proofs outside them.
`Extracted.lean` is reserved for the selected artifact; do not keep another copy
among consumer sources. Lake configuration and Lean elaborators are executable
code, so use this mode with packages you trust.

## Publishing verified contracts

A library producer runs `leancil export-contracts manifest.json`. The command
checks every selected export with fresh ordinary verification, an exact canonical
contract theorem, extraction-certificate audit and independent kernel replay. It
publishes a sidecar only after every export and the final input checks succeed.

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

Version 1 supports public or protected static, non-virtual, non-generic exports
without imports. RVA static sites are supported. Each certification records the
exact scoped static identities, and the producer checks their set against the
generated program in Lean. It rejects recorded static-value and
initialization assumptions because this sidecar version does not transport them.
This restriction does not weaken the extractor's admission or profile rules.

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

Forced full verification replays libraries with RVA tables against their
current DLLs and proves `linkChecked` for the composed program inside
`LeanCILFullComposition.certified`, which rejects conflicting descriptors and
names both fields. A published-certification import has no linked program; there
the extractor's static identity checks and the `StaticWorldValid` premises guard
collisions. The raw `link` API remains a pure construction without that check.

The default output is `<assembly-simple-name>.leancil.contracts` next to the DLL.
Use `--output path.leancil.contracts` to select another path. Publication is atomic
and a failed command preserves an existing sidecar unchanged. The old sidecar
still binds the old DLL hash and cannot certify a changed implementation. A
body-only rebuild can retain the same public interface and contract closure
digests while its implementation hash and certification change. Consumers still
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
Any LeanCIL change to `CIL/` or the toolchain changes the framework key, so
sidecars and bundles exported with an older framework are rejected by a newer
verifier. Publishers re-export with the new LeanCIL; consumers that cannot upgrade
the publisher keep the LeanCIL revision the bundle records.

Run `dotnet run --file scripts/Test.cs -- --suite exports` for the producer/App
round trip, unchanged caller after a library rebuild, rejecting exports and
source-only bundle checks.

## Published contract imports

A consumer can verify a caller against an imported contract without the library's
implementation proof package. Supply the contract sidecar and independently
obtained implementation SHA-256 during extraction, as described in
[Contract interfaces](CONTRACT-INTERFACES.md). Only the interface source modules
are supplied to the consumer. The full-verification locator is not fetched.

The interface stage compiles those sources, rejects undeclared dependencies and
forbidden declarations, and checks each canonical exported-constant closure.
It binds definition values, theorem types, inductive constructors and recursor
computation rules. A postcondition helper cannot change behind an unchanged name
and retain its old closure digest. Framework and toolchain stopping uses the
constant's defining module, not its namespace.

The App theorem must retain `HoldsGiven Extracted.program Extracted.ImportsHold
claim`. Its imported conditions use the canonical `MethodContract.Holds` or
`OutcomeContract.Holds` predicates at their absolute slots. The implementation
proofs are not elaborated or replayed. The unchanged axiom audit applies to the
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
`--import-interface-sha256`. The existing `--import-implementation` option selects
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
Static and initialization assumptions still cannot be exported in this feature.
