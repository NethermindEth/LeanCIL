# Verify many methods of a library

Read this when the user wants proofs for several methods, profiles or assembly variants checked
in one run, locally or in CI. `leancil gates` extracts and verifies a catalog; `leancil
verify-batch` verifies extractions that already exist.

## Requirements

- The proofs are in one Lake package that pins `leancil`, uses the toolchain `leancil --version`
  prints and has a resolved `lake-manifest.json`
  ([package setup](bridge-model-proof.md#package-setup)).
- Dependencies are Git packages pinned to full revisions. Local path dependencies, symlinked
  sources, custom Lake cache directories and native or precompiled dependencies are not
  supported.
- Proofs and extraction outputs are in different directories. Verification skips `.lake`,
  `.git`, `artifacts`, `generated`, `bin`, `obj` and `.work` inside the package, so keep proofs
  out of those and put outputs under `artifacts/`.
- Lake configuration and Lean elaborators are executable code. Run a batch only on a package the
  user trusts.

## Catalog with leancil gates

Write one manifest that names every method, its profiles, its proof and its theorem:

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
      "name": "wrong-operation",
      "assembly": "variants/Wrong.dll",
      "expect": "rejected"
    }]
  }]
}
```

```sh
leancil gates gates.json
```

| Manifest key | Meaning |
| --- | --- |
| `proofRoot`, `outputRoot`, `assembly`, `@profile.json` | Paths relative to the manifest |
| `gates[].name` | Letters, digits, `_`, `.` and `-`; unique ignoring case |
| `gates[].method` | A selector, as for `extract` |
| `gates[].profiles` | Built-in names or `@profile.json`, without repeats. Each profile is extracted and verified separately |
| `gates[].proof` | Path relative to `proofRoot` |
| `gates[].theorem` | Fully qualified theorem name |
| `gates[].initializedTypes`, `gates[].typeArguments` | As `--assume-initialized` and `--type-argument` of `extract` |
| `gates[].variants[]` | Another assembly the unchanged proof is applied to. `"expect": "certifies"` passes when the proof verifies; `"expect": "rejected"` passes when the proof fails at proof checking and leaves no `verified.json`. A variant cannot be named `production` |

An unknown manifest key is an error. Each result goes to
`<outputRoot>/<gate name>/<profile hash>/<variant name>`, where the gate's own assembly is the
variant `production`, and the batch manifest `gates` generates is `<outputRoot>/requests.json`.

Use a `rejected` variant to show that a proof detects a wrong implementation: build the mutated
assembly, name it as a variant, and the gate fails if the proof still verifies against it.

| Option | Meaning |
| --- | --- |
| `--method name` | Select gates whose `method` contains this substring |
| `--profile name` | Select one exact profile name |
| `--changed path` | Select gates affected by a changed `.lean`, `.cs`, assembly or project file; repeatable. Omitted gates get no verification claim |
| `--check` | Compile only; see below |
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
| `--check` | Compile only; see below |
| `--fresh`, `--rebuild-library` | Bypass reuse of earlier results; also rebuild the framework library |
| `--trace` | Trace every request's proof |
| `--parallel count` | Workspaces run at once after the first. The default is processor count / 8, at least 1 |
| `--results results.json` | Write every outcome as JSON in request order: `output`, `proof`, `theorem`, `expect`, `status`, `stage`, `error`, `axioms`, `failure` and `elapsedSeconds` |
| `--format json` | Print one JSON document with `passed`, `failed` and each request's report |

## Output

Each request prints one line when its outcome is final, in completion order:

```text
PASS verified artifacts/Add MyProof.correctness (12.345s batch-to-result latency)
PASS rejected artifacts/Mutant MyProof.correctness (proof checking)
FAIL artifacts/Other MyProof.other (stage: proof checking)
```

A `FAIL` line is followed by the same diagnostic `verify` prints, and the request's output gets
a `failed.json` ([failures.md](failures.md)). The exit code is `0` only when every request met
its expectation. A verified request writes `verified.json` into its output; when several requests
share one output, only the last writes `verification.json` and `verified.json`.

Audit each verified statement as "Reporting a result" in SKILL.md describes. A request passes
when its named theorem verifies, whatever that theorem states.

## Compile check

`leancil verify-batch requests.json --check` and `leancil gates gates.json --check` compile each
proof and its imports against its extraction and print `PASS Checked` or `FAIL` per request. A
compile check skips kernel replay and the axiom audit, removes existing `verified.json` files and
issues no certificate. Use it for fast feedback while editing, and never report its result as
verification. A request or variant that expects `rejected` is an error under `--check`.

## Profiles

List every deployment profile in `profiles`; a pass under one profile proves nothing for another.
A method whose body differs by hardware profile needs a proof that holds for each extraction.
`leancil templates output-directory extraction-directory...` generates one shared body with a
profile parameter and a binding per input extraction
([profile templates](https://github.com/NethermindEth/LeanCIL/blob/main/docs/PROOFS-BINDING.md#generated-profile-templates)).

## Further tools

- `leancil blockers assembly.dll --manifest blockers-manifest.json` reports, for a list of method
  and profile pairs, every construct that stops extraction; run it to plan which methods can be
  verified
  ([blockers](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CLI.md#report-extraction-blockers)).
- Proof files generated from C# recipes, contract export for callers in other assemblies and
  audits of a whole Lean library are described in the
  [consumer guide](https://github.com/NethermindEth/LeanCIL/blob/main/docs/CONSUMERS.md).
