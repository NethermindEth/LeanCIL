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
| `gates[].profiles` | Built-in names or `@profile.json`, without repeats; each is extracted and verified separately |
| `gates[].proof`, refutation `proof` and `template` | Paths relative to `proofRoot` |
| `gates[].initializedTypes`, `gates[].typeArguments` | As `--assume-initialized` and `--type-argument` of `extract` |
| `assembly` or `build` | Exactly one per gate and variant: a built assembly, or `{ "project", "properties" }` to build |
| `projects.<name>` | A project's `path`, the `assembly` file name it builds and default build `properties` |
| `variants[].expect` | `certifies` or `rejected` |
| `variants[].profiles` | A nonempty subset of the gate's profiles |
| `variants[].proof`, `variants[].theorem` | Together, replace the gate's proof and theorem for this variant |
| `variants[].initializedTypes` | Replaces the gate's list |
| `variants[].program` | `same`, `renamed` or `different` from production's program for the same profile |
| `variants[].refutation` | Required for `rejected`: a `theorem` and a `proof`, or a `template` and string `values` |
| `generatedRoot` | Required with a template: where instantiated refutations are written under `proofRoot` |

An unknown manifest key is an error. A `certifies` variant passes when its proof verifies. A
`rejected` variant passes only when its refutation verifies against the variant's extraction and
its proof fails at proof checking; use one to show that a proof detects a wrong implementation.
A build, extraction, program comparison or template failure, a missing proof or an internal error
fails the variant and never counts as a rejection. The variant's output keeps no `verified.json`.
LeanCIL does not check that the refutation states the negation of the contract, so write it so.

`gates` builds each distinct project and property set once into `<outputRoot>/builds/`. A
template's `@NAME@` placeholders take `values.NAME`; every placeholder needs a value and every
value a placeholder. The result is written to
`<proofRoot>/<generatedRoot>/<gate>/<profile>/<variant>.lean` before verification hashes the
sources, and is verified like any other proof.

Each result goes to `<outputRoot>/<gate name>/<profile hash>/<variant name>`, where the gate's
own assembly is the variant `production`. `gates` writes the batch manifest it runs to
`<outputRoot>/requests.json`. Each `--results` entry has the `verify-batch` fields of the
variant's proof, with `status` the variant's verdict, plus `gate`, `profile`, `variant`,
`build`, `extraction`, `program` and `refutation` (the refutation's `status`, `stage`, `error`
and `axioms`, or `null`).

| Option | Meaning |
| --- | --- |
| `--method name` | Select gates whose `method` contains this substring |
| `--profile name` | Select one exact profile name |
| `--changed path` | Select variants affected by a changed `.lean`, `.cs`, template, assembly, manifest or project file, or a file under a project's directory; repeatable. Omitted variants get no verification claim |
| `--check` | [Compile only](#compile-check) |
| `--fresh`, `--rebuild-library`, `--trace`, `--parallel count`, `--results file`, `--format json` | As for `verify-batch` |

A selection that matches no gate is an error.

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
profile parameter and a binding per input extraction
([profile templates](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-BINDING.md#generated-profile-templates)).

## Further tools

- `leancil blockers assembly.dll --manifest blockers-manifest.json` reports, for a list of method
  and profile pairs, every construct that blocks extraction, without stopping at the first. Run
  it before estimating work on a library
  ([blockers](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#report-extraction-blockers)).
- Proof files generated from C# recipes, contract export for callers in other assemblies and
  audits of a whole Lean library are described in the
  [consumer guide](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CONSUMERS.md).
