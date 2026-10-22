# Command-line reference

The [README](../README.md#quick-start) walks through a first verification. This page gives the
details of each command.

## Build

A regular `dotnet build Extractor -c Release` produces `Extractor/bin/leancil.exe` on Windows (`leancil` on other platforms). The managed assembly and package are named `Nethermind.LeanCIL`.

## Discover and select methods

This lists canonical method signatures you can copy into `extract`, including overloads and non-public methods. Discovery reads metadata without executing the assembly. Listed methods are not necessarily supported: `extract` validates their signatures, CIL and reachable dependencies.

Method selectors accept C# type aliases, an optional return type, and an unqualified declaring type when the result is unique. These all select the same method:

```text
System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)
ulong Examples.Arithmetic::Add(ulong,ulong)
Examples.Arithmetic::Add(ulong,ulong)
Arithmetic::Add(ulong,ulong)
```

The parameter list remains required. Matching is case-sensitive; an explicit return type must match. Use `ulong&` for a by-reference parameter. Ambiguous selectors fail with a list of full candidate signatures, which can be copied into the command. Artifacts always record the resolved canonical signature, so equivalent selectors can check the same artifact. Selection never relaxes supported-type or instruction validation.

The extraction CLI infers the assembly identity from the DLL's metadata. Optionally add `--assembly Examples` to require a specific short name, or supply a full identity to constrain version, culture and public key token as well. A mismatch is rejected. Generated artifacts always retain the actual full identity and assembly hash, including when `--assembly` is omitted.

## Extract

Extract a method from a compiled assembly:

```sh
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::Add(ulong,ulong)" artifacts/Add
```

Expected output from the repository root:

```text
Extracted 1 reachable method into artifacts/Add/Extracted.lean
```

The generated `Extracted.lean` contains `arg 0`, `arg 1`, `add`, `ret`, the exact method signature, metadata, profile and kernel-checked fetch equations; the assembly hash lives in `identity.json` and the report. The entry is method zero; reachable managed callees are emitted in dependency order.

Extraction also emits raw metadata and a `translation_valid` certificate. Independent Lean validators recompute layouts, check all layout-dependent sites and parameter-home mappings, validate structural generic substitution and managed-call bindings, and check feature-analysis states, decided type tests and control-flow coverage. Per-site validators walk the raw code, reachability mask and emitted code in lockstep, so a long branch excluded by the profile adds linear rather than quadratic checking cost. Verification requires this certificate to have the exact validator type for the complete emitted program and kernel-replays it separately from the user proof. Raw metadata serialization and transformations outside those checks remain trusted.

Profiles default to scalar. Pass a supported profile name or `@profile.json` as the final positional argument to `leancil extract`. Both `check` and `verify` recover the profile from the manifest. Capability prerequisites are validated. Instructions unreachable under that exact fixed profile are emitted as explicit unsupported placeholders; changing profiles invalidates artifacts.

### Initialization assumptions

Methods on types with static constructors are rejected by default. If the caller
guarantees successful initialization before invocation, extraction can record
that precondition explicitly:

```sh
leancil extract assembly.dll 'Type::Method(ulong)' artifacts/Method --assume-initialized Namespace.Type
```

Repeat `--assume-initialized` for each required type, using its exact metadata
name. Assumptions apply only to named types in this assembly and do not propagate
to helper types. They do not execute or prove initialization, or admit calls to
static constructors. They do enable `ldsfld` of the type's static readonly struct
fields whose value its static constructor fixes (see
[static readonly values](OPCODES.md#static-readonly-values)); each such field is
recorded in `staticValues` and reported as a caller assumption that it keeps the
value its static constructor stored. The generated Lean source and identity
manifest retain the assumptions; `check` reuses them and rejects conflicting
explicit assumptions. Verification binds the manifest hash, prints the
initialization preconditions with the theorem and copies both lists into
`verified.json`. Re-extract older artifacts to include the new manifest fields.

## Report extraction blockers

`leancil blockers` runs admission, the validation `extract` performs, over an explicit list of
method and profile pairs, and reports everything that blocks each one instead of stopping at the
first failure. It writes no extraction artifacts and checks no proofs:

```sh
leancil blockers assembly.dll --manifest blockers-manifest.json [--output blockers.json]
```

```json
{
  "initializedTypes": ["Namespace.Type"],
  "entries": [
    { "signature": "Type::Method(ulong)", "profile": "scalar" },
    { "signature": "Type::Method(ulong)", "profile": "@profiles/x64-bmi2.json" }
  ]
}
```

`profile` is a profile name or `@file`, resolved against the manifest's directory;
`initializedTypes` applies `--assume-initialized` to every entry. The report goes to
`--output`, by default `blockers.json` next to the manifest, and a short summary goes to standard
output. Each entry is `admitted` (extraction would succeed), `blocked`, or `notChecked` with the
reason: a selector that matches no method or several, an unknown profile, or an assembly or
assumption that fails before any method is checked. Each blocker is one unsupported construct
(instruction, call, type or layout). It lists every site, with method, IL offset, instruction and
the PDB source location when one is present, and every affected entry with the call chains from
it to those sites. Only code reachable under the entry's profile is checked, so a branch excluded
by a constant `IsSupported` is never reported. A method whose metadata or control flow cannot be
analysed is reported once, without the callees behind it. Admission is not verification: an admitted entry
still needs a proof. The command exits with `0` whenever the report is written, whatever the
entries' status.

## Check

Check that the generated files still match the assembly and extraction settings:

```sh
leancil check artifacts/Add
```

Expected output on standard output:

```text
Valid: extraction artifacts match the assembly and recorded settings.
  Assembly: Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null
  DLL: Examples/Assembly/bin/Examples.dll
  Entry: System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)
  Profile: scalar (scalar, 64-bit, little-endian)
  Reachable methods: 1
  CIL: artifacts/Add/Extracted.lean
  Manifest: artifacts/Add/identity.json
  Matched: assembly identity and SHA-256, extractor SHA-256, configuration, metadata and regenerated CIL.
```

Paths under the current directory are displayed relative to it; paths outside it remain absolute.

The check reads the assembly path, method and hardware profile from the manifest, regenerates the extraction in memory, and compares it with the saved files without overwriting them. Assembly paths are stored relative to the artifact directory. If the DLL moves, use `leancil check artifacts/Add --assembly-path path/to/Examples.dll`; its identity and content must still match. Older manifests must be regenerated with `extract`.

## Verify

`verify` first checks the extraction artifacts, reuses an integrity-checked source-keyed library cache (or builds it on a cache miss), checks and kernel-replays the selected proof, and audits its transitive axioms. Use `--fresh` to rebuild the library; CI does this automatically. Only `propext`, `Quot.sound` and `Classical.choice` are permitted. It checks artifact and source identity again before writing `artifacts/Add/verified.json`. Lean and Lake must be installed; the tool includes the framework sources.

The theorem defaults to `ExampleProof.correctness`; select another with `--theorem Namespace.theoremName`. The first invocation saves the selection in `artifacts/Add/verification.json`, independently of the generated success report:

```json
{
  "schema": 1,
  "proof": "../../Examples/Proofs/Add.lean",
  "theorem": "ExampleProof.correctness"
}
```

Proof paths in settings are relative to the artifact directory; command-line paths are relative to the current directory. Settings are reusable inputs that can be versioned separately from reports. They survive failed proofs and re-extraction. Explicit `--proof` and `--theorem` arguments override the saved values. Without settings, the default proof is `Proof.lean` in the artifact directory. Older reports are used once to migrate the selection into settings.

Run verification using the saved settings:

```sh
leancil verify artifacts/Add
```

Every invocation checks the proof afresh. A failed proof removes the previous verification report. `extract` generates definitions and `check` validates extraction consistency; `verify` establishes the selected theorem about those definitions. Its guarantee is exactly the theorem's statement, including its preconditions and quantifiers.

## Diagnostics

Method and call validation failures name the rejected item and the method containing it. A rejected call reports the callee, the calling method and the IL offset of the call. For example, `typeof(ulong) == typeof(uint)` compiles to calls into the runtime library that LeanCIL does not model:

```text
Error: External managed dependency: System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)
  Caller: System.UInt64 Examples.Arithmetic::TypeCheck(System.UInt64) at IL_0005
  Callee assembly: System.Private.CoreLib (referenced as System.Runtime)
  Stage: metadata and CIL validation
  Next: Reachable calls must target methods in the extracted assembly or runtime calls modelled by LeanCIL. Remove the call from the extracted path, or see Supported subset and limits in the README for the modelled calls.
```

When proof checking fails, the report leads with `Lean errors (N):`: each
`error:` diagnostic with its `file:line:col`, the module Lake was building and
its full message block, omitting axiom reports, traces and warnings. Long
messages are truncated in this summary only; the unmodified Lake output follows
under `Details:` (and in the `LEANCIL_TRACE_DIRECTORY` transcripts when set).

## Failure reports

A failed `verify` writes `failed.json` next to where `verified.json` would go and
removes any `verified.json`; a later successful verification removes
`failed.json`. `verify-batch` writes the same report into each failing request's
output (for the last request of an output, as with `verified.json`) and as the
`failure` field of each `--results` entry (`null` when there is none).

```json
{
  "schema": 1,
  "kind": "unsolved-goal",
  "resource": null,
  "stage": "proof checking",
  "theorem": "ExampleProof.correctness",
  "module": "Proofs.Mix",
  "proof": "/work/package/Proofs/Mix.lean",
  "output": "/work/artifacts/Mix",
  "method": { "entry": "System.UInt64 Calls::Mix(System.UInt64,System.UInt64)", "assembly": "Contracts, Version=1.0.0.0, ...", "assemblySha256": "..." },
  "file": "/work/package/Proofs/Mix.lean",
  "line": 12,
  "column": 3,
  "diagnostics": [
    { "kind": "unsolved-goal", "resource": null, "module": "Proofs.Mix", "file": "/work/package/Proofs/Mix.lean", "line": 12, "column": 3, "message": "unsolved goals\n..." }
  ],
  "message": "Command failed (1): lake build ...",
  "rerun": ["leancil", "verify", "/work/artifacts/Mix", "--proof", "/work/package/Proofs/Mix.lean", "--theorem", "ExampleProof.correctness", "--proof-root", "/work/package"]
}
```

`kind` is one of:

| Kind | Meaning |
|------|---------|
| `unsupported-extraction` | `check` rejected the method in metadata and CIL validation, or Lean rejected the extraction certificate |
| `stale-input` | The assembly, extraction artifacts or proof inputs changed after extraction or during verification |
| `elaboration-error` | A Lean error other than an unsolved goal or a resource limit |
| `unsolved-goal` | A Lean `unsolved goals` error |
| `resource-limit` | Heartbeats (`(deterministic) timeout`, `(kernel) deterministic timeout`) or recursion depth; `resource` names which |
| `replay-or-audit-rejected` | Kernel replay or the theorem and axiom audit rejected the proof |
| `refutation` | The theorem verified and states `Not (contract.Holds ...)` for a `MethodContract` or `OutcomeContract` |
| `invalid-request` | The proof or theorem selection is invalid |
| `unclassified` | Anything else, such as a missing tool; read `message` |

The request's `kind`, `file`, `line` and `column` are those of the first Lean
error; `diagnostics` lists every error of the request's own modules with its
message block. Lines are 1-based and columns 0-based, as Lean prints them.
Locations in workspace or temporary copies are mapped back to the selected
proof, the artifact's `Extracted.lean` or the consumer package. `message` is the
original output, unmodified; `rerun` reruns just that request. Classification
uses only the stage, LeanCIL's own messages and Lean's error prefixes above.
An unsolved goal is never a refutation: only a verified theorem whose
elaborated statement is `Not` applied to a contract's `Holds` is, as reported by
the theorem audit. A verified refutation keeps its `verified.json`, the
certificate of the refutation, and also writes `failed.json` with kind
`refutation`, located at the theorem's name.

## Export contracts

`leancil export-contracts manifest.json [--output Lib.leancil.contracts] [--bundle directory]`
checks a library's selected contracts and writes their bound sidecar. See
[Publishing verified contracts](CONSUMERS.md#publishing-verified-contracts) for
the manifest, exact theorem guarantee, version-1 restrictions and source bundle.
All exports must pass before the sidecar is published.

## Verify with imported contracts

After import-aware extraction, `leancil verify output --proof Caller.lean` checks
the caller under the published contracts. `--proof-root` uses the same interface
audit for a consumer package. `--fresh` can use an empty `LEANCIL_CACHE_DIR`; no
library implementation proof source, artifact or full bundle is required.

The sidecar export adds `kind` (`method` or `outcome`). Each selected certification
record requires `theorem`, `statement` and `statementDigest`. The driver checks
the actual exported contract type and canonical closure. `statementDigest` is the
publisher's digest of its canonical certification type, not a hash of its pretty
printed statement. The consumer records this provenance without obtaining the
implementation proof. See [Contract interfaces](CONTRACT-INTERFACES.md).

A schema-4 `verified.json` contains `imports[]` with `acceptedVia` set to
`published-certification`, the implementation SHA-256, interface digest,
certification theorem/statement/digest, and deployment obligation. CLI output
prints the accepted certification and obligation. The caller theorem remains
conditional on those imported contracts.

Reference-only extraction is an authoring input. Verification checks its caller
proof, then exits with status 1 and an authoring-only diagnostic. It does not
write `verified.json` or publish a successful proof receipt.

Contract imports also require `--import-interface-sha256 Lib=<digest>` from an
accepted publisher channel. This independently pins the interface descriptor
and all executable Lean source bytes before compilation. See
[CONTRACT-INTERFACES.md](CONTRACT-INTERFACES.md) for the source trust boundary.

## Exception documentation lint experiment

Run `leancil lint-exceptions artifacts/Method --documentation Assembly.xml`
after extraction. The command checks the extraction again, then writes
`artifacts/Method/exception-lint.json`. It does not verify a theorem or write
`verified.json`. Drift is diagnostic and does not change the command exit code.
Malformed documentation or stale extraction fails and removes an old lint report.

The report keeps potential modeled sites and XML declarations separate. It
compares the selected entry's declarations with its profile-reachable method
closure. It includes folded throws, integer divide/overflow, signed Abs, X86
DivRem and span indexing faults. Clamp invalid bounds remain a model fault;
this experiment does not map them to a CLR exception. Memory faults, invalid
states, unsupported operations and fuel exhaustion have no CLR name here.
This is a conservative site analysis. It does not prove feasibility under a
contract, exception conditions, or complete runtime behavior.

XML must contain the selected compiler member ID and matching assembly name.
Unresolved cref, include and inheritdoc need expansion first. The supplied XML
hash identifies bytes; it does not prove that they came from the DLL build.
No documentation text becomes evidence or a contract premise.
