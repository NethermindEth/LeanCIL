# Verify many methods of a library

Read this when the user wants proofs for several methods, profiles or assembly variants checked
in one run, locally or in CI. `leancil gates` extracts and verifies a catalog; `leancil
verify-batch` verifies extractions that already exist.

## Requirements

- The proofs are in one Lake package set up as
  [package setup](bridge-model-proof.md#package-setup) describes.
- Proofs and extraction outputs are in different directories. Verification skips `.lake`,
  `.git`, `artifacts`, `generated`, `bin`, `obj` and `.work` inside the package, so keep proofs
  out of those and put outputs under `artifacts/`.
- Lake configuration and Lean elaborators are executable code. Run a batch only on a package the
  user trusts.

## Catalog with leancil gates

Write one manifest that names every method, its profiles, its proof and its theorem, and the
regression variants each proof must accept or reject:

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
      "name": "wrong-operation",
      "build": { "project": "fixture", "properties": { "FixtureCase": "Wrong" } },
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

```sh
leancil gates gates.json
```

| Manifest key | Meaning |
| --- | --- |
| `proofRoot`, `outputRoot`, `assembly`, `@profile.json`, `projects.<name>.path` | Paths relative to the manifest |
| `gates[].name`, `variants[].name` | Letters, digits, `_`, `.` and `-`; unique ignoring case. A variant cannot be named `production` |
| `gates[].method`, `gates[].theorem` | A selector and a fully qualified theorem name, as for `extract` and `verify` |
| `gates[].profiles` | Built-in names, `profiles` names or `@profile.json`, without repeats; each is extracted and verified separately |
| `gates[].proof`, refutation `proof` and `template` | Paths relative to `proofRoot` |
| `gates[].initializedTypes`, `gates[].typeArguments` | As `--assume-initialized` and `--type-argument` of `extract` |
| `assembly` or `build` | Exactly one per gate and variant: a built assembly, or `{ "project", "properties" }` to build |
| `projects.<name>` | A project's `path`, the `assembly` file name it builds and default build `properties` |
| `variants[].expect` | `certifies`, `rejected` or `unchanged` |
| `variants[].profiles` | A nonempty subset of the gate's profiles |
| `variants[].proof`, `variants[].theorem` | Together, replace the gate's proof and theorem for this variant; `proof` may be `{ "template", "values" }` |
| `variants[].statement` | `independent` for a `certifies` theorem that is not production's statement |
| `variants[].initializedTypes` | Replaces the gate's list |
| `variants[].program` | `same`, `renamed` or `different` from production's program for the same profile; required with `unchanged` |
| `variants[].programOf` | Another variant whose program `program` compares with instead of production's |
| `variants[].refutation` | Required for `rejected`: a `theorem` and a `proof`, or a `template` and optional string `values` |
| `templates.<name>` | A template `path` and default `values`, which a use's own `values` override |
| `profiles.<name>` | An `@file` profile, relative to the manifest, used by name; not a built-in name |
| `generatedRoot` | Required with a template: where instantiated proofs are written under `proofRoot` |
| `defaults` | `assembly` or `build`, `initializedTypes` and `typeArguments` for each gate that gives none |
| `selection.all`, `selection.ignore` | Path prefixes for `--changed`: a path under `all` selects every row, one under `ignore` nothing; they must not overlap |
| `catalogs` | Binding catalogs whose generated gates join the manifest; see below |

An unknown manifest key is an error. A `certifies` variant passes when its proof verifies and the
kernel accepts its theorem at production's statement `T`, unless its `statement` is
`independent`. A `rejected` variant passes only when its refutation verifies against the
variant's extraction, the kernel accepts the refutation at `¬ T`, and its proof fails at proof
checking; use one to show that a proof detects a wrong implementation. An `unchanged` variant
requests no proof and passes when its program comparison holds. A build, extraction, program
comparison, template or statement identity failure, a missing proof or an internal error fails
the variant and never counts as a rejection. The variant's output keeps no `verified.json`.

The kernel compares statements in the variant's own environment, structurally and then by
definitional unfolding within 200000 heartbeats, so a statement may name `Extracted.entryIndex`
where production says `0`. Each constant of `T` must be the same declaration of the same module
in the variant's environment, so name shared definitions from a module both proofs import.
Production verifies before the variants it is compared with. `--check` compares no statement.

`gates` builds each distinct project and property set once into `<outputRoot>/builds/`. A
template's `@NAME@` placeholders take `values.NAME`, which may be empty or span lines; every
placeholder needs a value and every value a placeholder. A `template` that names a `templates`
entry uses that entry, otherwise a file. The result is written to
`<proofRoot>/<generatedRoot>/<gate>/<profile>/<variant>/Refutation.lean` or `Proof.lean` before
verification hashes the sources, and is verified like any other proof.

Each result goes to `<outputRoot>/<gate name>/<profile hash>/<variant name>`, where the gate's
own assembly is the variant `production`; that variant under that profile is a row with id
`<gate>/<profile>/<variant>`. Before building or extracting a row, `gates` removes its
`verified.json` and `failed.json`. `gates` writes the requests of both its batches to
`<outputRoot>/requests.json`. The `--results` file holds `manifest` (a digest of the manifest and
its catalogs), `revision` (`git rev-parse HEAD`, or `null`) and `rows`. Each row has its `id`
and the `verify-batch` fields of the variant's proof, with `status` the variant's verdict, plus
`gate`, `profile`, `variant`,
`build`, `extraction`, `program`, `refutation` (the refutation's `status`, `stage`, `error`
and `axioms`, or `null`) and `statement` (its `status`, `same`, `different`, `unavailable` or
`independent`, and the `production` and `variant` statements, or `null`).

| Option | Meaning |
| --- | --- |
| `--method name` | Select gates whose `method` contains this substring |
| `--profile name` | Select one exact profile name |
| `--only id-prefix` | Select rows whose id is the prefix or starts with it and `/`; repeatable |
| `--changed path` | Select variants affected by a changed `.lean`, `.cs`, template, assembly, manifest or project file, or a file under a project's directory; repeatable. Omitted variants get no verification claim |
| `--check` | [Compile only](#compile-check) |
| `--fresh`, `--rebuild-library`, `--trace`, `--parallel count`, `--results file`, `--format json` | As for `verify-batch` |

A selection that matches no gate is an error, except under `--plan`.

## Split a catalog over CI jobs

```sh
leancil gates gates.json --plan 8 --costs earlier/results.json --format json > plan.json
leancil gates gates.json --plan-group plan.json job-1 --results results/job-1/results.json
leancil gates gates.json --require-results results --plan plan.json
```

`--plan count` selects as a run would and prints at most `count` nonempty groups, keeping every
row of one gate and profile together; it verifies nothing. Costs are each row's mean
`elapsedSeconds` in the `--costs` files, else the median of the method's recorded gates, else
the median of all, else 1, and the same inputs give the same plan. `--plan-group` runs one
group, after checking that the plan's `manifest` digest matches the manifest and catalogs.
`--require-results` fails unless every row the plan selected has exactly one result that passed,
in results files carrying the plan's `manifest` and `revision`; it names each `MISSING`,
`DUPLICATE`, `FAILED` and `FOREIGN` row. Restore portable support in a job only from a trusted
run, with the digest taken from that run's output.

## Generated bindings

`leancil bindings catalog.json [--check]` writes, or with `--check` only compares, one proof file
per row of a binding catalog: the product of `dimensions`, minus `exclude`, plus `rows`, with
`assign` adding variables and `handwritten` entries giving a row its own proof and theorem. Each
row yields a gate from the `gate` patterns and a source from the template by exact `@NAME@`
replacement. A missing value, an unused variable, a duplicate gate, conflicting sources at one
path and, under `--check`, a stale or stray file under `generatedRoot` are errors. List the
catalog in a gate manifest's `catalogs` to verify its gates; `gates` writes the sources first.
Generation proves nothing; each source is verified like a handwritten one
([binding catalogs](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CONSUMERS.md#binding-catalogs)).

## Batch with leancil verify-batch

Run `leancil extract` for each method first, then list the requests:

```json
{
  "schema": 1,
  "proofRoot": ".",
  "requests": [
    { "output": "artifacts/Add", "proof": "proofs/Add.lean", "theorem": "MyProof.correctness" },
    { "output": "artifacts/Mutant", "proof": "proofs/Add.lean", "theorem": "MyProof.correctness", "expect": "rejected" }
  ]
}
```

```sh
leancil verify-batch requests.json --results results.json
```

Paths are relative to the manifest. `expect` is `verified` (the default) or `rejected`.
`verify-batch` does not extract again: an output whose assembly changed fails as a stale input.

| Option | Meaning |
| --- | --- |
| `--check` | [Compile only](#compile-check) |
| `--fresh`, `--rebuild-library` | Bypass reuse of earlier results; also rebuild the framework library |
| `--trace` | Trace every request's proof |
| `--parallel count` | Workspaces run at once after the first. The default is processor count / 8, at least 1 |
| `--results results.json` | Write every outcome as JSON in request order: `output`, `proof`, `theorem`, `expect`, `status`, `stage`, `error`, `axioms`, `libraryBuild`, `failure` and `elapsedSeconds` |
| `--format json` | Print one JSON document with `passed`, `failed` and each request's report |

## Output

Each request prints one line when its outcome is final, in completion order:

```text
PASS verified artifacts/Add MyProof.correctness (12.345s batch-to-result latency)
PASS rejected artifacts/Mutant MyProof.correctness (proof checking)
FAIL artifacts/Other MyProof.other (stage: proof checking)
```

A `FAIL` line is followed by the diagnostic `verify` prints, and the request's output gets a
`failed.json` ([failures.md](failures.md)). The exit code is `0` only when every request met its
expectation. A verified request writes `verified.json` into its output; when several requests
share one output, only the last writes `verification.json` and `verified.json`.

Audit each verified statement as "Reporting a result" in SKILL.md describes. A request passes
when its named theorem verifies, whatever that theorem states.

## Compile check

`leancil verify-batch requests.json --check` and `leancil gates gates.json --check` compile each
proof and its imports against its extraction and print `PASS Checked` or `FAIL` per request. A
compile check skips kernel replay and the axiom audit, removes existing `verified.json` files and
issues no certificate. A request or variant that expects `rejected` is an error under `--check`.

## Profiles

List every deployment profile in `profiles`. A method whose body differs by hardware profile
needs a proof that holds for each extraction.
`leancil templates output-directory extraction-directory...` generates one shared body with a
profile parameter and a binding per input extraction; `--check` compares committed output,
`--namespace`, `--module` and `--omit-equations` shape the shared module
([profile templates](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-BINDING.md#generated-profile-templates)).

## Further tools

- `leancil blockers assembly.dll --manifest blockers-manifest.json` reports, for a list of method
  and profile pairs, every construct that blocks extraction, without stopping at the first. Run
  it before estimating work on a library
  ([blockers](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#report-extraction-blockers)).
- Contract export for callers in other assemblies and
  audits of a whole Lean library are described in the
  [consumer guide](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CONSUMERS.md).
