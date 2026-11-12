# Consumer packages and batch verification

Read this page when you keep your proofs in your own Lake package. It covers verifying a package
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

`leancil gates` builds, extracts and verifies an explicit catalog of methods, their proofs and
regression variants in one run, verifying every proof as one [batch](#batch-verification).
Assembly, project, `proofRoot`, `outputRoot` and custom `@profile.json` paths are relative to the
manifest; proof and template paths are relative to `proofRoot`. Each profile of each variant gets
its own extraction and result in `<outputRoot>/<gate name>/<profile hash>/<variant name>`, where
the gate's own assembly is the variant `production`. The generated batch manifest is
`<outputRoot>/requests.json`.

```json
{
  "schema": 1,
  "proofRoot": "verification",
  "outputRoot": "artifacts/gates",
  "generatedRoot": "Generated",
  "projects": {
    "fixture": {
      "path": "fixtures/Arithmetic.csproj",
      "assembly": "Arithmetic.dll",
      "properties": { "Configuration": "Release", "FixtureCase": "Production" }
    }
  },
  "gates": [{
    "name": "add",
    "build": { "project": "fixture" },
    "method": "Arithmetic::Add(ulong,ulong)",
    "profiles": ["scalar", "x64-v3"],
    "proof": "Add.lean",
    "theorem": "Add.correctness",
    "variants": [{
      "name": "commuted",
      "build": { "project": "fixture", "properties": { "FixtureCase": "Commuted" } },
      "expect": "certifies",
      "program": "different",
      "proof": "Commuted.lean",
      "theorem": "Commuted.correctness"
    }, {
      "name": "wrong-carry",
      "build": { "project": "fixture", "properties": { "FixtureCase": "WrongCarry" } },
      "profiles": ["scalar"],
      "expect": "rejected",
      "program": "different",
      "refutation": {
        "template": "Refutation.lean.in",
        "theorem": "Witness.refuted",
        "values": { "LEFT": "1", "RIGHT": "1" }
      }
    }]
  }]
}
```

Gate, variant and project names use letters, digits, `_`, `.` and `-`; gate and variant names
must be unique ignoring case. A variant cannot be named `production`, and `profiles` must not
repeat a profile. Unknown manifest properties are rejected. A gate may also give
`initializedTypes` and `typeArguments`, with the meaning of the `extract` options
`--assume-initialized` and `--type-argument`.

| Key | Meaning |
| --- | --- |
| `assembly` or `build` | Exactly one per gate and variant: a built assembly, or a project of `projects` to build. |
| `projects.<name>` | The project's `path`, the file name of the `assembly` it builds and default build `properties`. |
| `build.properties` | Build properties that replace the project's defaults of the same name. |
| `variants[].profiles` | A nonempty subset of the gate's profiles; the default is all of them. |
| `variants[].proof`, `variants[].theorem` | Given together, they replace the gate's proof and theorem for the variant. |
| `variants[].initializedTypes` | Replaces the gate's list. |
| `variants[].program` | `same`, `renamed` or `different`: how the variant's program must relate to production's. |
| `variants[].refutation` | Required when `expect` is `rejected`: a `theorem`, and a `proof` or a `template` with `values`. |
| `generatedRoot` | Required with any template: the directory under `proofRoot` that receives instantiated refutations. |

`gates` builds each distinct project and property set once with `dotnet build`, into
`<outputRoot>/builds/<key>/`. It sets `BaseOutputPath`, `OutputPath` and `OutDir` to that
directory's `bin/`, and `BaseIntermediateOutputPath`, `IntermediateOutputPath` and
`MSBuildProjectExtensionsPath` under its `obj/`, as global properties that a
`Directory.Build.props` cannot override, and uses the project's `assembly` from `bin/`. Property
names are MSBuild identifiers other than those paths, and values hold no `;`, `,`, `%` or quote.
Global properties also reach referenced projects, so a project built this way should not
reference other projects, and a multi-targeted project should select one framework with a
`TargetFramework` property. A build failure fails every variant that uses it; the other variants
still run. The build runs the consumer's project, which is executable code like its Lake package.

`program` compares the method bodies of the variant's `Extracted.lean` with those of production's
extraction for the same gate and profile: `same` when the bodies and the method signatures are
equal, `renamed` when only the signatures differ, `different` otherwise. Assembly identities,
digests, paths and metadata tokens are ignored. A comparison that does not hold fails the variant at
stage `program comparison`, and its proof is not checked.

A template is a text file under `proofRoot`. `gates` replaces each `@NAME@` in it with
`values.NAME` and changes nothing else; a placeholder without a value, or a value no placeholder
uses, fails the variant at stage `refutation template`. Before any proof request is built or any
source is hashed, it writes the result with LF endings to
`<proofRoot>/<generatedRoot>/<gate>/<profile>/<variant>.lean`, so the instantiated text is a
consumer source like any other. A custom profile is named by a hash of its path there. The tool
writes and deletes only those exact files, refuses to write through a link, and rejects a
`generatedRoot`, gate or profile directory that verification excludes (see [limits](#limits)). A
generated refutation gains no trust from being generated: it is verified like any other proof.

```text
import Extracted
import CIL.Safety.MethodContract
open CIL.Safety
theorem Witness.refuted : ¬ ∀ (left right : CIL.W64) (memory : Memory),
    ∃ fuel, invoke Extracted.program fuel 0 [.scalar (.i64 left), .scalar (.i64 right)]
      memory = .ok (memory, [.scalar (.i64 (left + right))]) := by
  intro holds
  obtain ⟨fuel, ran⟩ := holds @LEFT@ @RIGHT@ Memory.empty
  have returned := congrArg Prod.snd (invoke_ok_unique ran (rfl : invoke Extracted.program 16 0
    [.scalar (.i64 @LEFT@), .scalar (.i64 @RIGHT@)] Memory.empty = .ok _))
  revert returned
  decide
```

A variant passes as follows:

| `expect` | Passes when |
| --- | --- |
| `certifies` | Its proof verifies against its extraction, as for production. |
| `rejected` | Its refutation verifies against its extraction, with the same kernel replay and axiom audit as any theorem, and its proof fails at proof checking. |

A build, extraction, program comparison or template failure, a missing proof, and a proof whose
check printed an internal error each fail the variant; none counts as a rejection. A `rejected`
variant's refutation and proof are requests on the same output, the proof last, so the output
keeps no `verified.json`: neither the proof's, which was rejected, nor the refutation's, whose
outcome is recorded in the results. LeanCIL checks that the refutation theorem verifies, not that
it states the negation of the gate's contract; state it so.

| Option | Meaning |
| --- | --- |
| `--method name` | Select gates whose `method` contains this substring. |
| `--profile name` | Select one exact profile name. |
| `--changed path` | Select variants affected by a changed file; repeatable, relative to the working directory. |
| `--check` | [Compile only](#check-compilation); an error when a selected variant expects `rejected`. |
| `--fresh`, `--rebuild-library`, `--trace`, `--parallel` | As for [`verify-batch`](#batch-verification). |
| `--results results.json` | Write one result per variant and profile, in manifest order. |
| `--format json` | Print one JSON document instead of the text lines. |

Each result has the [batch](#batch-verification) fields of the variant's proof (`output`,
`proof`, `theorem`, `expect`, `status`, `stage`, `error`, `axioms`, `libraryBuild`, `failure`,
`elapsedSeconds`), where `status` is the variant's verdict, and `gate`, `profile`, `variant`,
`build` (`built`, `failed` or `null` for a given assembly), `extraction` (`extracted` or
`failed`), `program` (`passed`, `failed` or `null`) and `refutation`. `refutation` is `null` or
the refutation's `proof`, `theorem`, `status`, `stage`, `error` and `axioms`. When a variant fails
before its proof is checked, `stage` and `error` name that step. The JSON document has `schema`,
`passed` and `failed` counted over these results, `variants` holding them, and `requests` as
`verify-batch --format json` prints them. The exit code is `0` only when every variant passed.

Selection makes no verification claim about omitted variants, and a selection that matches
nothing is an error. `--changed` selects by file kind:

- A `.lean` file selects the variants whose proof or refutation imports it, directly or not.
- A template selects the variants instantiated from it, and the manifest selects every variant.
- A file under a project's directory selects every variant built from that project.
- A `.cs` file selects the variants whose extracted reachable methods have PDB sequence points
  in it. A variant without debug information, or with referenced assemblies, is selected.
- An assembly selects the variants extracted from it.
- A `.csproj`, `.props` or `.targets` file selects every candidate.

A variant whose program is compared still extracts production for that gate and profile, whether
or not production is selected.

## Check compilation

`leancil verify-batch requests.json --check` compiles each proof and its import closure against
the selected extraction and reports every request as `Checked` or failed, with source locations
for elaboration errors. Shared support is compiled once where possible, and the compiled
artifacts are private to the invocation. A compile check skips consumer kernel replay and the
theorem axiom audit, removes existing `verified.json` files and issues no certificate: it makes
no trust claim and does not replace verification. A request that expects `rejected` is an error
under `--check`.

## Consumer proof packages

For proofs split across your own Lean modules, pass the Lake package root:

```sh
leancil verify artifacts/Add --proof proofs/Add.lean --proof-root . --theorem MyProof.correctness
```

The package must meet these requirements:

- It depends on `leancil`, uses the bundled Lean toolchain and has a resolved
  `lake-manifest.json` (run `lake update`). `lakefile.toml` and `lakefile.lean` are both
  supported.
- Its dependencies are resolved git packages pinned to full revisions, in the standard
  `.lake/packages` directory.
- Its CIL sources match the verifier's bundled framework, allowing LF/CRLF differences. A
  mismatch fails and names the revision to pin; [`leancil --version`](CLI.md#version) prints
  the `[[require]]` block that pins it.

Further restrictions are under [limits](#limits).

Verification copies the consumer's Lean sources, Lake configuration and resolved dependency
sources into a temporary package, without trusting the package's compiled caches. It supplies
the selected `Extracted` module before Lake builds the proof and its imports, so shared consumer
modules can themselves import `Extracted`.

The report binds all copied `.lean`, `.toml`, `.json` and `lean-toolchain` files and the
dependency revisions. Sources are checked again before the report is written. New or changed
consumer and dependency modules undergo kernel replay, and the selected theorem's transitive
axioms are audited with the same policy as single-file verification. `verification.json`
records the package root.

## Generated proof bindings

File-based C# runners can include [ProofBindingCatalog.cs](../scripts/ProofBindingCatalog.cs)
from the `leancil` checkout that Lake pins, at
`.lake/packages/leancil/scripts/ProofBindingCatalog.cs`, with an `#:include` directive. The
installed `leancil` tool does not contain this file. A `ProofGate` names the exact method,
profile, proof path and theorem. Each `ProofBinding` supplies the complete Lean source from an explicit,
consumer-reviewed recipe. `ProofBindingCatalog.Sources` checks the recipe identities against
the catalog and rejects missing or duplicate entries, changed profiles or theorem names,
conflicting sources and unsafe output paths. Recipes cover every catalog profile of each
method they generate; other methods may keep handwritten proofs.

Call `ProofBindingCatalog.Materialize(root, catalog, recipes)` before selecting imports or
capturing verification sources. It emits deterministic UTF-8 files with LF endings, and emits
source shared by several gates once. Pass `check: true` to reject missing or changed bytes
without writing files. Proof-family recipes and arithmetic specifications belong in the
consumer; the catalog does not infer them from method names.

Generated files participate in the ordinary source identity, extraction binding and kernel
audit. Generation writes binding text; it discharges no proof obligation. Use the extractor's
[profile templates](PROOFS-BINDING.md#generated-profile-templates) for shared extracted bodies;
binding recipes do not replace its reachable-helper or static-metadata checks.

## Proof-authoring workspace

`leancil workspace` generates one method's extraction into the proof's Lake package so the proof
file shows live goals in the editor; `leancil watch` keeps it current. The synopses and options
of both are in the [CLI reference](CLI.md#editor-workspace).

```sh
leancil workspace path/to/Library.dll 'Type::Method(parameter-types)' --profile arm64-advsimd --proof proofs/Method.lean --theorem MyProof.correctness --proof-root .
```

Use the exact assembly and method selector of the consumer build. Run `lake update` in the
package first; the pinned Git dependency and framework/toolchain checks of
[consumer verification](#consumer-proof-packages) apply.

### Editor extraction modules

Each selected method and profile gets its own module, so proofs of different methods share a
package and stay open at once. The command prints the import:

```text
Editor extraction: Workspace.Wide::get_IsZeroOrOne() (scalar)
  Import: import Extracted.Wide_get_IsZeroOrOne_1f0c2a9e, import ExtractedSymbols.Wide_get_IsZeroOrOne_1f0c2a9e
```

The module is `Extracted.KEY`, with `ExtractedSymbols.KEY` for PDB names; `ExtractedSymbols.KEY`
exists only while the assembly has a matching portable PDB. KEY is the method's type and name
followed by the first eight hex digits of the SHA-256 of the assembly's simple name, the method's
full signature, the profile name and the initialization assumptions. A rebuild or an assembly
version change therefore keeps the key, and overloads and profiles of one method get different
keys.

The declarations keep the `Extracted` and `ExtractedSymbols` namespaces, so a proof names
`Extracted.program` whichever key it imports. No plain `Extracted` module is generated: a proof
that names no method fails at its import instead of checking against whichever method was
selected last. The command warns when the proof imports plain `Extracted` or another method's
key and names the import to use. `leancil new-proof` writes the keyed import, so a generated
outline resolves in the editor without editing.

The command writes under the package's ignored `.lake` directory and leaves the manifest and
the pinned checkout untouched:

| Path | Contents |
| --- | --- |
| `.lake/leancil` | The sources of the editor library `LeanCILEditor`, `Extracted/KEY.lean` and `ExtractedSymbols/KEY.lean`. `selections/KEY/selection.json` there records the selection and its proofs. |
| `.lake/package-overrides.json` | Written in a package that pins `leancil`. Lake applies it over the manifest, so the `leancil` requirement resolves to `.lake/leancil-framework`. |
| `.lake/leancil-framework` | A lakefile whose source and build directories are the certified library in the [library cache](CLI.md#library-cache). It brings in `.lake/leancil-editor`, the package that declares the editor library. |

The proof package therefore compiles no framework module and holds no framework build. The
command builds the generated modules with Lake, so the import resolves in the proof and in any
helper module, and Lake rebuilds helpers that import an extraction when it changes. Other
methods' modules are left as they are. A LeanCIL checkout is the framework package: its
lakefile declares the editor library and it builds its own framework modules.

The first `workspace` on a machine without the certified library builds it whole, as
`verify --proof-root` would. `workspace` caches the library in CI too, where `verify` bypasses
the cache, because the package must require a library that stays on disk.

Building in the package, `lake env lean` and the language server leave an up-to-date library
unwritten. `workspace` and `watch` fail if their build changed any library file, and the next
run replaces a cache entry that no longer matches its manifest. A tool with different framework
sources has a library under another cache key; the next `workspace` or `watch` rewrites
`.lake/leancil-framework` to name it, building it first when absent.

[`leancil workspace --remove`](CLI.md#editor-workspace) drops one method's selection.

The command rejects:

- a package that already has overrides it did not write;
- consumer sources named `Extracted.lean` or `ExtractedSymbols.lean`, or inside an `Extracted`
  or `ExtractedSymbols` directory, because they would shadow an extraction. The output directory of
  `leancil extract` holds such a file: keep it outside the proof package;
- a proof root with no lakefile, or with no `lake-manifest.json` because `lake update` has not
  run there. The message gives the cause and the fix.

The editing loop is:

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

`leancil watch` keeps every selection the package records current. It polls the projects' C#
and MSBuild files, the selected assemblies and the package's Lean sources. After a change it:

1. runs `dotnet build` when C# changed;
2. extracts each selection again into a scratch directory, replaces the modules of the methods
   whose extraction changed and builds those;
3. runs ordinary `leancil verify --format json` for each proof whose extraction or sources (the
   proof, the package modules its imports reach and the Lake configuration) changed since its
   last run. Each proof is verified against its own copy of the extraction under
   `selections/KEY/proofs/`.

With `--goals`, each verification runs as
[`verify --goals`](CLI.md#goals-of-an-unfinished-proof) and `watch` prints, under each proof,
the goal at every `sorry`, before every failing tactic and left unsolved. The goals of a proof
whose inputs did not change are printed again from its last run. Each result's `goals` holds
them in the JSON line; without `--goals` it is `null`.

Each proof gets one status per cycle:

| Status | Meaning |
| --- | --- |
| `verified` | Ordinary verification passed. |
| `failed` | Verification failed. The verify report locates each error in the Lean source and, for a stepping tactic, the C# line. |
| `stale` | The C# build failed. Its errors are listed with their C# locations, and every proof's earlier certificate is deleted. |
| `missing` | The method no longer extracts (deleted or renamed). Its editor modules are removed, so the proof fails at its import. |
| `unverified` | The selection names no `--theorem`; only the editor modules were refreshed. |

A `missing` selection stays recorded until the method returns or its directory is deleted.
After a failed build, the next good build verifies every proof again, so no proof keeps a
`verified` status from before the failed build.

A result whose inputs did not change is reported again with `rechecked` false. Such a result
reports byte-identical extraction text and sources and issues no new certificate: its
`verified.json` names the assembly it was verified against.

On Windows the command also checks that the environment `lake serve` passes to Lean fits Lean's
32,767-byte limit, and fails with the largest variables instead of leaving the editor without
`LEAN_PATH`; see [environment size on Windows](CLI.md#environment-size-on-windows).

A proof with no `lakefile.toml` or `lakefile.lean` in its directory or above it needs no setup.
The command makes that directory a Lake package: it writes a `lakefile.toml` that declares the
editor library and a `lean-toolchain` beside the proof, and runs `lake update` without network
access. The package requires `leancil` by `path` from `.lake/leancil-framework`, so it holds no
framework sources or build. The command creates no Git repository or commit. Verification
accepts only dependencies pinned by a Git revision, so pass such a proof to ordinary
`leancil verify <extraction> --proof <file>` without `--proof-root`; `watch` does that for such
a package.

The workspace command certifies nothing: it writes no `verified.json`, trusted support manifest
or verification receipt. Run ordinary verification on the same files:

```sh
leancil extract path/to/Library.dll 'Type::Method(parameter-types)' artifacts/Method arm64-advsimd
leancil verify artifacts/Method --proof proofs/Method.lean --proof-root . --theorem MyProof.correctness --fresh
```

Verification never reads the editor library. Its fresh source package skips `.lake`, takes
`Extracted` from the extraction it checks, and builds on a certified library whose lakefile
does not declare `LeanCILEditor`. For each `Extracted.KEY` or `ExtractedSymbols.KEY` the
proof's closure imports, it generates a module containing only `import Extracted` (or
`import ExtractedSymbols`), after checking that KEY is the key of the extraction it checks; a
key of another extraction is rejected. The theorem and certificate audits read `Extracted`
itself, with extraction identity checks and independent kernel replay. A forged or stale editor
module therefore changes nothing verification reads, and a certificate depends on the pinned
`leancil` revision.

## Local support cache

Successful runs locally certify extraction-independent support artifacts for reuse across
method gates. A support generation is keyed by:

- the effective Lake configuration files, ordered resolved import paths and dependency revisions;
- the `lean`, `leanchecker` and `lake` binaries, the certified framework's source identity
  and compiled module hashes, and the verifier;
- the environment variables Lean, Lake and elan read: `LEAN_*` except
  `LEAN_NUM_THREADS`, `LAKE_*`, `ELAN_*` and `RESERVOIR_*`. Unrelated variables
  such as `DOTNET_HOST_PATH` do not affect reuse. If consumer elaborators read
  other variables, list them in `LEANCIL_CACHE_ENVIRONMENT` (comma-separated).

A later run restores support per module:

- Each generation records every module's source, compiled-import and artifact hashes. A later
  run restores the largest import-closed set of modules whose sources are unchanged, so editing
  one helper or adding unrelated proof files keeps the rest.
- Modules that transitively depend on `Extracted` (but not on the extraction certificate audit
  or a proof module) are also bound to the generated `Extracted.lean` text. That text carries
  no assembly hash, so an assembly change outside the extracted program keeps it
  byte-identical. Restoring these modules skips their rebuild but never their kernel replay
  against the freshly built `Extracted`. The certificate binds the actual assembly through the
  extraction integrity check and `assemblySha256` in the report.
- Lake decides reuse from its own traces; if it rebuilds any restored extraction-independent
  module, every module is replayed again.
- An unchanged proof may reuse its authenticated successful result only for the same
  extraction identity, theorem and inputs; extraction integrity is checked again.

Reuse is authenticated and local to the machine:

- A rebuilt framework with different compiled bytes cannot restore support from the previous
  build, even when its sources are identical. This rule covers generated extraction certificates,
  whose Lake traces depend on those compiled imports.
- Modified or unsigned cache files fall back to rebuilding and kernel replay, and a corrupt
  entry is replaced.
- Concurrent verifiers publish through an atomic rename, and republishing the same module set
  is a no-op.
- [`--fresh`](CLI.md#verify) disables both consumer caches.
- On another machine, `LEANCIL_CERTIFIED_LIBRARY` can supply the base library; see
  [library cache](CLI.md#library-cache).

Entries are stored in `success-v1` under the [library cache](CLI.md#library-cache) directory:

- Generations hard-link files whose bytes an earlier generation holds, so a new generation
  costs about its changed modules. Each entry is authenticated on its own, and in-place damage
  to a shared file rejects every entry holding it.
- A generation not restored or republished for `LEANCIL_SUPPORT_RETENTION_DAYS` (default 7) is
  evicted when a later one is published, together with staging directories left by killed runs.
- A cache that cannot be written, for example on a full disk, prints a warning with its
  location and free space; the verification result stands.

## Replay

Kernel replay and the theorem audit run the pinned toolchain's `leanchecker` and the library's
`leancil-audit` directly, with the `LEAN_PATH` that `lake env` resolves after the build and
`LEAN_SYSROOT` set to that toolchain. The audit reads
the replayed oleans and elaborates no consumer source. The resolved import paths are compared
with those resolved before the build.

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
| `--parallel count` | How many workspaces after the first run at once. The default is processor count / 8, at least 1. |
| `--results results.json` | Write every outcome as JSON, in request order. |
| `--format json` | Print one JSON document instead of the per-request lines; see [batches](CLI.md#batches). |

Each request prints `PASS verified`, `PASS rejected` or `FAIL` with its stage and diagnostics
as soon as its outcome is final (an unchanged-result cache hit, or the end of its workspace),
so lines follow completion order. The exit code is `0` only when every request met its
expectation.

- Only the last request for an output writes its `verification.json` and `verified.json`.
- Each `--results` entry has `output`, `proof`, `theorem`, `expect`, `status`, `stage`, `error`,
  `axioms`, `libraryBuild`, `failure` and `elapsedSeconds`. `failure`, and the `failed.json` of
  each failed or rejected output, hold the report described in
  [failure reports](CLI.md#failure-reports).
- `elapsedSeconds` is the time from the start of batch verification until that request's result
  is known, including shared preparation and waiting for earlier workspaces and excluding later
  workspace cleanup. Requests that share work can finish together, so do not sum these times as
  independent costs. Normal verification and compile checks report the same measure.

A request with `"expect": "rejected"` passes only when its proof fails during proof checking
with unchanged inputs and an intact extraction. It stops there, never writes a certificate,
removes any earlier `verified.json` and writes `failed.json` describing the rejection.

The session takes one source snapshot, restores certified support once and checks each
extraction's integrity. Requests share work as follows:

- Requests whose `Extracted.lean` is identical share one Lake workspace: one `lake build` of all
  their proof modules, one extraction certificate audit and one kernel replay of the union of
  non-certified modules. Requests with different extractions use separate workspaces.
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

Related multi-method extractions reuse identical generated method evidence within a batch. The
verifier picks a first workspace containing the largest common source body and factors its
shared profile/layout header and method declarations into modules named by their content
hashes. Unique wrappers stay in `Extracted`; a single extraction, or a group without shared
method evidence, is compiled as extracted.

- The regenerated source hash is checked before factoring. Component identities include their
  exact sources and imported component identities; the authenticated
  [support cache](#local-support-cache) also binds the framework, toolchain, verifier policy and
  source/import closure.
- Later workspaces copy only components whose complete source dependency closure matches.
  Changed artifact bytes prevent replay reuse.
- Call connections, constrained calls, the complete translation certificate, the compiled axiom
  audit and the final input checks run for every extraction.
- Only components of the first workspace are shared, and method indices are not renamed to
  find structurally equivalent methods, so unrelated groups can repeat evidence. Generated
  components are not exported as portable support.

If a proof build changes an extraction's compiled module, verification fails at
`extraction integrity` and issues no certificate for that request. The diagnostic names each
changed module part with its before/after SHA-256 hashes, whether preparation restored or built
the certificate, the isolated package path, and artifact/trace modification times and trace
hashes. A timestamp alone does not establish why Lake rebuilt a module.

## Portable support across machines

A trusted producer can export the extraction-independent support it certified so that another
machine skips its kernel replay.

| Variable | Set on | Meaning |
| --- | --- | --- |
| `LEANCIL_EXPORT_CONSUMER_SUPPORT` | producer | Output directory for the manifest `<digest>.json` and its artifacts `<digest>.files/`. |
| `LEANCIL_DISABLE_SUCCESS_CACHE=true` | producer | Disable local receipts; a supplied portable manifest stays in use. |
| `LEANCIL_CONSUMER_SUPPORT` | receiver | Manifest path, or several separated by the platform path separator. |
| `LEANCIL_CONSUMER_SUPPORT_SHA256` | receiver | The independently trusted digest of each manifest, comma-separated in the same order. |
| `LEANCIL_RESTORE_CONSUMER_SUPPORT=true` | receiver | Copy the manifest's compiled artifacts before building, so Lake reuses them instead of rebuilding. |
| `LEANCIL_CACHE_ENVIRONMENT` | both | Extra variables that elaborators read, bound into the cache keys. |

- A successful consumer verification writes the export and prints its SHA-256. In GitHub
  Actions it also writes the `consumer-support-sha256` step output.
- Set `LEANCIL_DISABLE_SUCCESS_CACHE=true` when a new export is required, since an unchanged
  whole-proof cache hit skips publication.
- Take each trusted digest from an independent source, for example a producer job output. Never
  derive it from an untrusted download.

No local receipt secret is exported. Each manifest is authenticated by its own digest: a missing
or incorrect trusted digest fails verification, and an incompatible manifest (another schema,
verifier policy, library, source snapshot or toolchain) falls back to replay. Reports record
`consumerSupportSha256` when portable support was used. `--fresh` bypasses portable reuse.

The receiver builds fresh sources. It skips kernel replay only when the verifier, certified
framework, installed Lean artifacts, normalized source snapshot, pinned dependencies and
**entire compiled support import closure** match the producer.

- Fingerprints use the pinned Lean serializer on all compiled module parts, excluding only
  `Lean.Linter.lintLogExt`: persisted linter diagnostics include temporary absolute source
  filenames. All declarations, imports and other extensions are covered, including source paths
  stored in semantic values.
- The compiled files are never rewritten, and their raw hashes must stay stable throughout
  verification. Environment differences are allowed only if the fingerprints match.
- A changed dependency invalidates every dependent module, even when a referencing theorem's own
  bytes are unchanged.
- Extraction-dependent modules and the public proof are always checked.

A manifest names each module's compiled artifacts and their hashes, plus a digest of the Lean,
Lake and checker binaries and of the variables bound into
[local cache keys](#local-support-cache); values are never written. With
`LEANCIL_RESTORE_CONSUMER_SUPPORT=true`, a receiver whose binaries and bound variables match
copies those artifacts before building.

- Each restored file must match its manifest hash, or verification fails. A manifest without its
  files falls back to a fresh build.
- Restored bytes are the producer's, as with local receipts: an elaborator that reads the source
  path or an undeclared variable keeps the producer's result. Declare such variables in
  `LEANCIL_CACHE_ENVIRONMENT`.
- Replay is skipped only for modules whose bytes match a manifest fingerprint.

`scripts/PrepareLibrary.cs` records canonical framework fingerprints inside the certified
library. Its independently trusted manifest digest covers this table along with the library
sources and artifacts. A receiver reuses entries only for the same module name, exact
compiled-part presence and hashes, and matching normalization version, Lean executable and
native auditor bytes, toolchain release and runtime identifier. Relocating unchanged artifacts
does not invalidate them. Changed modules and tools fall back to normalization; changed
authenticated table bytes fail verification. This reuse of a pure byte transformation also
applies when local receipts are disabled or `--fresh` uses a supplied certified library. It does
not change portable support eligibility, source/import checks, theorem audits or kernel replay.

## Replay profiling

Set `LEANCIL_PROFILE_CONSUMER_REPLAY=true` with `LEANCIL_TRACE_DIRECTORY` to record JSON
timings for each replayed module. This diagnostic mode runs the pinned toolchain's
`LeanChecker.replayFromImports` serially, including each module's import loading, to isolate
each module's cost; it does not predict normal parallel checker throughput. Normal consumer
replay runs the same routine in parallel and records timings too. Both modes replay the exact
resolved module list and keep the final theorem/axiom audit and source/artifact stability
checks. Replay passes `LEAN_NUM_THREADS` to the Lean frontend (default two) to bound concurrent
imported environments.

## Library audits

`leancil audit-library` checks compiled library theorems through independent kernel replay and
native axiom auditing. An elaborated `run_cmd` audit or `#print axioms` output is insufficient,
because the audited code can forge that output:

```sh
leancil audit-library --project . --module MyLib --prefix MyLib. --prefix MyLemmas. \
  --axioms propext,Quot.sound,Classical.choice
```

- It runs `lake build` for each `--module` in the package, resolves `LEAN_PATH` with
  `lake env`, and takes the import closure of the listed modules outside the toolchain.
- Every module in that closure is kernel-replayed with the pinned `leanchecker` routine. A CIL
  module skips replay only when it and every module it imports are byte-identical to the
  verifier's certified library.
- `leancil-audit` then reads those replayed oleans with `loadExts := false` and audits every
  `theorem` they declare under a prefix: private theorems by their user name, auto-generated
  ones included. A prefix names whole components, so `MyLib.` and `MyLib` match `MyLib.foo` but
  not `MyLibrary.foo`.
- It fails when any prefix matches no theorem, when an axiom closure leaves `--axioms` (default
  `propext`, `Quot.sound`, `Classical.choice`), or when an olean changes during the audit.
  On success it prints the theorem count per prefix and the union of the axioms used.
- `--results results.json` writes the audited modules, counts, axioms and rejected theorems.

The package must pin the bundled Lean toolchain; it need not depend on `leancil`. Unlike
`verify`, the audit reads the package's own build directory rather than a fresh copy, so it
certifies the replayed bytes. It does not certify that they were compiled from the current
sources. Building
runs the package's Lake configuration and elaborators; the replay and the audit do not.

## Limits

These limits apply wherever a command reads a consumer package: `verify --proof-root`,
`verify-batch`, `gates`, `export-contracts`, and `workspace` and `watch` over such a package:

- Only Lean source packages are supported. Local path dependencies, custom Lake cache
  directories, symlinked sources and native/precompiled dependencies are not supported.
- Build/artifact directories (`.lake`, `.git`, `artifacts`, `generated`, `bin`, `obj`, `.work`)
  are excluded, and `verify --proof-root` also excludes the selected extraction output directory.
  `verify-batch` and `gates` exclude no output directory, so keep each output under an excluded
  directory or outside the package. Place handwritten proofs outside them, and keep the
  `generatedRoot` of `gates` outside them too, since its refutations must be consumer sources.
- `Extracted.lean` is reserved for the selected artifact; do not keep another copy among
  consumer sources.
- Lake configuration and Lean elaborators are executable code, so run these commands only on
  packages you trust.

## Publishing verified contracts

A library producer runs [`leancil export-contracts`](CLI.md#export-contracts) on a manifest.
The command checks every selected export with fresh ordinary verification, an exact canonical
contract theorem, extraction-certificate audit and independent kernel replay. It publishes a
sidecar only after every export and the final input checks succeed. A caller imports the sidecar
as [contract interfaces](CONTRACT-INTERFACES.md) describes.

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

Paths are relative to the manifest. Unknown and duplicate JSON properties are rejected.

- Each artifact must already contain an extraction identity and a `verification.json` naming
  the author's proof source. The recorded method must be the export entry, its DLL must match
  `assembly`, and its execution profile must be an exact built-in profile.
- The consumer package under `proofRoot` must have resolved pinned dependencies.
- One method may list several artifact entries for different profiles; duplicate method/profile
  pairs fail.
- Each `interface` source must be byte-identical to the module of that name under `proofRoot`,
  the module the author proof compiled against, so the published text is what was audited.

The contract constant must have type `CIL.Safety.MethodContract` or
`CIL.Safety.OutcomeContract`. The named author declaration must be a theorem with the exact
canonical `Holds` proposition for the extracted program at entry zero. An unrelated theorem, a
proof definition, user-defined field notation or extra assumptions do not establish this
guarantee. The generated ExportAudit module imports the exact author proof copy in the same
fresh verification session.

Published interface modules must check with only the declared interface sources and the bundled
framework/toolchain. They cannot require private implementation proofs or an `Extracted`
module. Canonical contract closures are checked both in this isolated interface and in the
proof environment, and their exact results must agree. Custom axioms, sorry and
valueless opaque interface declarations are not exportable. Contract predicates and their
reachable definitions determine the closure digest; the name alone does not determine it.

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
- Typed sidecars carry named initialization premises, as the
  [sidecar schema](CONTRACT-INTERFACES.md#sidecar-schema-1) describes.
- An extraction with recorded static-value assumptions cannot be exported. This restriction does
  not weaken the extractor's admission or profile rules.

Static identities are stable across separate extractions and body-only rebuilds. They use the
full assembly identity and full field name. `StaticWorldValid` describes the fields in its
descriptor list and permits other loaded immutable fields in the same valid registry. Its
`append`, `left`, `right` and `mono` lemmas support worlds over the same memory. Append
requires equal identities to name equal descriptors, so two exports that read one shared table
compose.

An export that can run after its tables are loaded, including a repeated call, should take
`StaticWorldValid published memory` as its precondition and restate it for the final memory in
its postcondition. `published` lists literal descriptors (identity, assembly identity, field
name and bytes) in an interface module. A published descriptor that differs from the extracted
one leaves the author proof unprovable, so no separate equality audit is needed.
`StaticIdentitiesAbsent` suits only a first-use contract: after the first call the field is
loaded and the premise is false.

[Forced full verification](FULL_VERIFICATION.md) proves `linkChecked` for the composed program
inside
`LeanCILFullComposition.certified`, which rejects conflicting descriptors and names both
fields. A published-certification import has no linked program; there the extractor's static
identity checks and the `StaticWorldValid` premises guard collisions. The raw `link` API is a
pure construction without that check.

The default output is `<assembly-simple-name>.leancil.contracts` next to the DLL;
`--output path.leancil.contracts` selects another path. Publication is atomic, and a failed
command leaves an existing sidecar unchanged. A sidecar binds the hash of the DLL it was
exported for and cannot certify a changed implementation. A body-only rebuild can keep the same
public interface and contract closure digests while its implementation hash and certification
change. Consumers check the selected deployment bytes and independently pin the interface with
`--import-interface-sha256 Lib=<digest>`.

`--bundle directory` also writes an immutable content-addressed source bundle:

- Its inventory binds the original producer inputs, complete consumer/dependency source
  closure, exact bundled framework sources, generated extraction and audit sources, and checked
  export statement metadata. The consumer's own `.lake/packages/leancil` copy is omitted
  because `framework/` already pins those sources.
- Every bundled file must match the hash taken in the export's input snapshot, which includes
  the framework sources; a change fails the export before the bundle or sidecar is published.
- The bundle contains no compiled DLL, `.olean`, local receipt or build cache. The selected
  implementation DLL remains a separate input.
- The bundle publishes before the sidecar, and the sidecar records its source locator.
- A source bundle is not proof certification and is not accepted as a trusted cache.
  [Independent verification](FULL_VERIFICATION.md) of a published library is a separate
  workflow.

`bundle.json` also records `frameworkKey`, the strict compatibility key that the sidecar
carries, and `leanCilRevision`, the leancil revision pinned by the producer's `proofRoot`. The
revision is diagnostic: it names the sources to rebuild with, while acceptance compares only
the framework key and file hashes. Any change to the framework sources under `CIL/` or to the
toolchain changes the framework key, so a verifier rejects sidecars and bundles exported with
another framework. Re-export with the verifier's LeanCIL revision, or verify with the revision
the bundle records.

## Published contract imports

A consumer can verify a caller against an imported contract without the library's
implementation proof package. Supply the contract sidecar and the independently obtained
implementation SHA-256 and interface digest during extraction, as
[contract interfaces](CONTRACT-INTERFACES.md) describes; that page also states the form the
caller theorem must have and what the result establishes. Only the interface source modules are
supplied to the consumer, and the full-verification locator is not fetched.
[`leancil resolve-imports`](CONTRACT-INTERFACES.md#resolving-imports-from-sdk-assets) locates
the sidecars and implementations in SDK output; the pins, caller audit, kernel replay and
deployment obligations are required as without it.

The interface stage rejects undeclared dependencies and forbidden declarations and checks each
canonical exported-constant [closure](CONTRACT-INTERFACES.md#sidecar-schema-1), so a
postcondition helper cannot change behind an unchanged name and retain its old closure digest.
Framework and toolchain stopping uses the constant's defining module and ignores its namespace.

The implementation proofs are not elaborated or replayed. The axiom audit applies to the caller
theorem; imports are explicit hypotheses.

Reports identify these imports as `published-certification`; their fields are listed under
[verify with imported contracts](CLI.md#verify-with-imported-contracts). The publisher's
certification is an explicit trust input. A digest does not prove that certification.
Deployment must provide the exact implementation and satisfy the imported contracts.

Proof reuse keys bind interface/closure digests, interface source bytes and `ExtractedImports`,
independently of library implementation hashes and provenance. Each cache hit checks current
DLL/sidecar/profile identities and writes a new report with current deployment records.
`--fresh` bypasses proof reuse.

## Transitive contract imports

A library can export a theorem conditional on its own imports. Its exact statement is
`CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold
(fun linked => CIL.Safety.MethodContract.Holds contract linked 0)`, with the corresponding
canonical `OutcomeContract.Holds` for an outcome contract. The producer freshly checks that
statement and records the dependency identities. It does not claim that the open extracted
prefix is closed.

Supply every graph node with `--import`, `--import-sha256` and `--import-interface-sha256`;
`--import-implementation` selects its DLL path. A dependency record binds its full assembly
identity, implementation SHA-256 and interface digest, and each dependency must match the
independently pinned node. A shared dependency has one identity and one selected
implementation. Conflicting hashes, missing nodes and cycles fail before extraction, and a
cycle error names the complete cycle path. The per-node checks are in
[transitive imports](CONTRACT-INTERFACES.md#transitive-imports).

The extraction identity records all nodes in `importGraph`. A verification report records their
deployment bindings in `contractDependencies`. Only methods that the selected App
entry calls receive import slots. Published certifications remain the stated trust boundary for
library implementations; caller proofs remain conditional on the published contracts. A source
bundle or graph digest does not prove that those contracts hold.

`MethodContract.relocateGiven` and `OutcomeContract.relocateGiven` turn a prefix proof into a
contract at a relocated entry. They require an explicit closed completion, its prefix relation,
satisfaction of imported contracts in that completion, and a relocation of the completion into
the target program. Transitive graph implementation changes conservatively invalidate proof
reuse. Initialization premises propagate through these conditional exports as the
[sidecar schema](CONTRACT-INTERFACES.md#sidecar-schema-1) describes. Constructor-initialized
field values cannot be exported.
