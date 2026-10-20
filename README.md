# LeanCIL: Formal Verification for .NET

LeanCIL is a Lean 4 formal verification framework for .NET programs. It enables machine-checked proofs of correctness and safety against compiled Common Intermediate Language (CIL), supporting applications written in C#, F#, and other .NET languages.

Verification operates on the assembly's actual compiled instructions using CIL semantics defined in Lean. The current [supported subset](#supported-subset-and-limits) covers selected instructions and runtime features; unsupported behaviour is rejected explicitly.

## Build and test

Install the toolchain selected by `lean-toolchain` (Lean **4.35.0**, through elan) and .NET SDK **10.0.402**. The extractor uses Mono.Cecil; the F# examples also use FSharp.Core. Both packages are pinned in `Directory.Packages.props`. Lean uses Std and Lean, without Mathlib.

```sh
lake build
dotnet run --file scripts/Test.cs
```

The scripts are [.NET file-based apps](https://learn.microsoft.com/en-us/dotnet/core/sdk/file-based-apps), with shared C# logic included directly. No scripting runtime is needed beyond .NET.

The test command builds independent example assemblies, runs Lean semantic tests, extracts actual CIL, proves positive examples, checks semantic counterexamples, rejects malformed/unsupported inputs, and tests artifact identity. Results go to `artifacts/test-results.json`; generated CIL, proof caches and verification reports are ignored by Git.

To run one part of the suite, use `dotnet run --file scripts/Test.cs -- --suite core` (or `cli`, `integer`, `narrow`, `primitive`). Each selection builds its prerequisites and writes `artifacts/test-results-<suite>.json`. Use separate checkouts when running suites concurrently because tests build and mutate artifacts.

## Command-line tool

Build and install the .NET tool from this checkout:

```sh
dotnet pack Extractor -c Release -o artifacts/packages
dotnet tool install --global Nethermind.LeanCIL --add-source artifacts/packages --version 0.1.0
```

Discover methods in a compiled assembly:

```sh
leancil list Examples/Assembly/bin/Examples.dll
```

This lists canonical method signatures you can copy into `extract`, including overloads and non-public methods. Discovery reads metadata without executing the assembly. Listed methods are not necessarily supported: `extract` validates their signatures, CIL and reachable dependencies.

Extract a method from a compiled assembly:

```sh
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::Add(ulong,ulong)" artifacts/Add
```

Expected output from the repository root:

```text
Extracted 1 reachable method into artifacts/Add/Extracted.lean
```

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

All commands exit with code `0` on success. Failures print a diagnostic to standard error and exit with code `1`. Failed checks and verification attempts start with `Invalid:` and produce no standard output. For example, if the generated Lean file has been edited:

```text
Invalid: Stale or mismatched verification artifact: artifacts/Add/Extracted.lean differs from regenerated CIL.
  Stage: extraction integrity
  Next: Rerun leancil extract with the intended assembly, method and profile, then rerun this command.
```

Method and call validation failures name the rejected item and the method containing it. A rejected call reports the callee, the calling method and the IL offset of the call. For example, `typeof(ulong) == typeof(uint)` compiles to calls into the runtime library that LeanCIL does not model:

```text
Error: External managed dependency: System.Type System.Type::GetTypeFromHandle(System.RuntimeTypeHandle)
  Caller: System.UInt64 Examples.Arithmetic::TypeCheck(System.UInt64) at IL_0005
  Callee assembly: System.Private.CoreLib (referenced as System.Runtime)
  Stage: metadata and CIL validation
  Next: Reachable calls must target methods in the extracted assembly or runtime calls modelled by LeanCIL. Remove the call from the extracted path, or see Supported subset and limits in the README for the modelled calls.
```

The check reads the assembly path, method and hardware profile from the manifest, regenerates the extraction in memory, and compares it with the saved files without overwriting them. Assembly paths are stored relative to the artifact directory. If the DLL moves, use `leancil check artifacts/Add --assembly-path path/to/Examples.dll`; its identity and content must still match. Older manifests must be regenerated with `extract`.

Verify a Lean proof against the extracted method:

```sh
leancil verify artifacts/Add --proof Examples/Proofs/Add.lean
```

`verify` first checks the extraction artifacts, reuses an integrity-checked source-keyed library cache (or builds it on a cache miss), checks and kernel-replays the selected proof, and audits its transitive axioms. Use `--fresh` to rebuild the library; CI does this automatically. Only `propext`, `Quot.sound` and `Classical.choice` are permitted. It checks artifact and source identity again before writing `artifacts/Add/verified.json`. Lean and Lake must be installed; the tool includes the framework sources.

Expected output:

```text
Verified: ExampleProof.correctness
  Assembly: Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null
  Entry: System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)
  Proof: Examples/Proofs/Add.lean
  Axioms: propext, Quot.sound
  Settings: artifacts/Add/verification.json
  Report: artifacts/Add/verified.json
  Statement:
    ExampleProof.correctness (x y : CIL.W64) :
      ∃ result,
        Except.map Prod.snd
              (CIL.Safety.invoke Extracted.program 4 0
                [CIL.Safety.Value.scalar (CIL.Value.i64 x), CIL.Safety.Value.scalar (CIL.Value.i64 y)] Examples.empty) =
            Except.ok [CIL.Safety.Value.scalar (CIL.Value.i64 result)] ∧
          BitVec.toNat result = (BitVec.toNat x + BitVec.toNat y) % 2 ^ 64
```

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

A regular `dotnet build Extractor -c Release` produces `Extractor/bin/leancil.exe` on Windows (`leancil` on other platforms). The managed assembly and package are named `Nethermind.LeanCIL`.

### Initialization assumptions

Methods on types with static constructors are rejected by default. If the caller
guarantees successful initialization before invocation, extraction can record
that precondition explicitly:

```sh
leancil extract assembly.dll 'Type::Method(ulong)' artifacts/Method --assume-initialized Namespace.Type
```

Repeat `--assume-initialized` for each required type, using its exact metadata
name. Assumptions apply only to named types in this assembly and do not propagate
to helper types. They do not execute or prove initialization, admit calls to
static constructors, or enable unsupported static field accesses. The generated
Lean source and identity manifest retain the assumptions; `check` reuses them and
rejects conflicting explicit assumptions. Verification binds the manifest hash
and prints the initialization preconditions with the theorem. Re-extract older
artifacts to include the new manifest field.

### Consumer proof packages

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
Successful runs locally certify extraction-independent support artifacts for reuse
across method gates. A support generation is keyed by the effective Lake
configuration files, ordered resolved import paths, dependency revisions, the
`lean`, `leanchecker` and `lake` binaries, the certified framework, the verifier,
and the environment variables Lean, Lake and elan read (`LEAN_*` except
`LEAN_NUM_THREADS`, `LAKE_*`, `ELAN_*`, `RESERVOIR_*`). Unrelated variables such
as `DOTNET_HOST_PATH` do not affect reuse. If consumer elaborators read other
variables, list them in `LEANCIL_CACHE_ENVIRONMENT` (comma-separated). Lean
sources are bound per module: each generation records, for every module, the
hashes of its candidate source files, its compiled imports and its artifacts.
A later run restores the largest import-closed set of modules whose sources are
unchanged, so editing one helper or adding unrelated proof files keeps the rest.
Modules that transitively depend on `Extracted` (but not on the extraction
certificate audit or a proof module) are also recorded, bound additionally to the
generated `Extracted.lean` text. `Extracted.lean` carries no assembly hash, so an
assembly change outside the extracted program keeps it byte-identical; each
workspace then restores those modules for its own extraction, which skips their
rebuild but never their kernel replay against the freshly built `Extracted`.
The certificate still binds the actual assembly through the extraction integrity
check and `assemblySha256` in the report. Lake still decides reuse from its own
traces; if it rebuilds any restored extraction-independent module, every module
is replayed again.
Republishing the same module set from a new session is a no-op, and concurrent
verifiers publish through an atomic rename; a corrupt entry is replaced.
An unchanged proof may reuse its authenticated successful result only for the same
extraction identity, theorem and inputs; extraction integrity is checked again.
Modified or unsigned cache files fall back to rebuilding and kernel replay.
`--fresh` disables both consumer caches. These receipts are local to the machine;
the existing certified CIL producer artifact can still supply the base library.

Kernel replay and the theorem audit run the pinned toolchain's `lean` directly
with the `LEAN_PATH` that `lake env` resolves after the build (and `LEAN_SYSROOT`
set to that toolchain), instead of starting Lake again for each step. The
resolved import paths are still compared with those resolved before the build.

When proof checking fails, the report leads with `Lean errors (N):`: each
`error:` diagnostic with its `file:line:col`, the module Lake was building and
its full message block, omitting axiom reports, traces and warnings. Long
messages are truncated in this summary only; the unmodified Lake output follows
under `Details:` (and in the `LEANCIL_TRACE_DIRECTORY` transcripts when set).

#### Binding extraction-independent bodies

Reusable execution and contract theorems are stated over a generic program and
bound to each extraction by a method-body equality. Prove those equalities with
`cil_body` (from `CIL.MethodBinding`, also imported by `CIL`) instead of `rfl`:

```lean
import CIL.MethodBinding

have found : Extracted.program[2]? = some (Full.fullBody Extracted.profile 9 5 7) := by cil_body
```

`cil_body` runs `rfl`, so the proof is the same kernel-checked `Eq.refl`. Only
when `rfl` fails does it evaluate both closed sides and report, for each
differing `Method` field, the first differing index, both elements and both
lengths, instead of only `rfl`'s type mismatch:

```text
cil_body: rfl could not prove the method-body binding
method index 1
field code: first difference at index 1 (left length 6, right length 6)
  left:  CIL.Op.brzero 10
  right: CIL.Op.brzero 4
```

The left side is the extraction's body. An index past the end of the program is
reported with the program's length. The diagnostic is computed after the
failure through compiled evaluation and is never proof evidence; it also works
for `Method = Method` goals. `Tests/MethodBinding.lean` covers both outcomes.

#### Binding bodies modulo dead code

A profile can make the extractor emit dead `.unsupported` blocks that shift
every later branch target, which breaks a `cil_body` equality even though
reachable behaviour is unchanged. `cil_embed` (from `CIL.Embedding.Tactic`)
proves the weaker `MethodEmbeds` relation instead: every live instruction of the
literal body appears in the extracted method at a mapped pc, with its code
targets mapped the same way and its fallthrough kept adjacent. Keep the proof
over the literal body and transport it with the lemmas in
`CIL.Safety.Embedding.Simulation`:

```lean
import CIL.Embedding.Tactic
import CIL.Safety.Embedding.Simulation

theorem bound : CIL.MethodEmbeds Extracted.program 2 (Full.fullBody Extracted.profile 9 5 7) := by cil_embed

-- A run proved over the literal body holds for the extraction with the same fuel.
example {fuel : Nat} {args : List CIL.Safety.Value} {m : CIL.Safety.Memory} {r : CIL.Safety.Memory × List CIL.Safety.Value}
    (h : CIL.Safety.invoke (Extracted.program.set 2 (Full.fullBody Extracted.profile 9 5 7)) fuel 2 args m = .ok r) :
    CIL.Safety.invoke Extracted.program fuel 2 args m = .ok r := bound.invoke h
```

`bound.certificate` transports an `InvocationCertificate` and
`bound.descriptors` the program's static descriptor list; `ProgramRefines.set`
composes several bound methods. The transfer is for successful checked
execution only. The pc map is computed outside the kernel and then checked by
it, so a wrong map is rejected, not trusted. A changed reachable instruction or
an inserted live one is reported by expected and actual pc:

```text
cil_embed: the expected body does not embed into the extracted method
method index 0
expected pc 1 maps to actual pc 1
  expected: CIL.Op.brzero 4
  renamed:  CIL.Op.brzero 6
  actual:   CIL.Op.brzero 4
  code target differs: expected target 4 maps to actual pc 6, but the actual instruction targets 4; actual pc 4 (CIL.Op.const32 0x00000009#32) is not the image of any live expected pc
```

The kernel check takes about 0.12 s for a 202-instruction body and 1.3 s for
1,414 instructions. See [docs/SOUNDNESS.md](docs/SOUNDNESS.md#method-body-embedding)
for the exact conditions and limits; `Tests/MethodEmbedding.lean` covers both
outcomes.

### Batch consumer verification

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
stops there, never writes a certificate, and the stale `verified.json` is
removed. As in sequential runs, only the last request for an output writes its
`verification.json` and `verified.json`. Each request prints `PASS verified`,
`PASS rejected` or `FAIL` with its stage and diagnostics as soon as its
outcome is final (an unchanged-result cache hit, or the end of its workspace),
so lines follow completion order; `--results` writes the outcomes as JSON in
request order. The exit code is 0 only when every request met its
expectation. With `LEANCIL_EXPORT_CONSUMER_SUPPORT` set, a batch writes one
manifest: the union of the extraction-independent support of every workspace
that passed replay, audits and stability checks. A module whose bytes differ
between workspaces is left out, together with its importers.

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

This mode supports Lean source packages; local path dependencies, custom Lake
cache directories, symlinked sources and native/precompiled dependencies are not
supported. Build/artifact directories (`.lake`, `.git`, `artifacts`, `generated`,
`bin`, `obj`, `.work`) and the selected extraction output directory are excluded.
Place handwritten proofs outside them.
`Extracted.lean` is reserved for the selected artifact; do not keep another copy
among consumer sources. Lake configuration and Lean elaborators are executable
code, so use this mode with packages you trust.

## Architecture

| Layer | Public modules | Purpose |
| --- | --- | --- |
| Values and instructions | `CIL.Types`, `CIL.Instructions`, `CIL.Layout` | Bit vectors, references, byte snapshots, validated aggregate layouts |
| Execution | `CIL.Semantics`, `CIL.ExecutionLemmas` | Functional byte-memory interpreter, calls, finite fuel, result uniqueness |
| Memory safety | `CIL.Safety.Memory`, `CIL.Safety.Execution` | Allocation-aware interpreter, access checks, initialization, permissions and lifetime |
| Proofs | `CIL.Safety.Certificate`, `CIL.Verification` | Invariants, invocation certificates, total-correctness specifications and finite execution conditions |
| Automation | `CIL.SymbolicExecution` | Kernel-checked instruction equations, symbolic stepping, transactional proved summaries |
| Runtime features | `CIL.Features`, `CIL.SIMD.*`, `CIL.ProfileEquivalence` | Fixed capability profiles, supported SIMD semantics, justified profile equivalence |
| Extraction | `Extractor/` | Metadata validation, managed-call reachability, CIL translation and Lean generation |
| Verification | `leancil verify` | Source-keyed library cache, explicit fresh builds, kernel replay, theorem audit and assembly/source identity binding |

**Use `CIL.Safety.invoke` for memory-safety claims.** Successful `CIL.invoke` alone does not establish allocation bounds or lifetime. The checked interpreter supports arbitrary admitted aggregate widths; the earlier interpreter retains explicitly named fixed vector-home operations and rejects the new general aggregate instructions. These are two defined models, not an unproved correspondence theorem between them.

## Worked example: addition

Prove that compiled addition returns the right result for every 64-bit input, change `+` to `-`, and see the same proof fail. This walkthrough also demonstrates a theorem that rules out successful execution of an invalid memory access.

`Examples/Assembly/Methods.cs` includes:

```csharp
public static ulong Add(ulong x, ulong y) => unchecked(x + y);
```

With the `leancil` tool installed, build the example, extract its CIL and verify the addition proof:

```sh
dotnet build Examples/Assembly -c Release
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::Add(ulong,ulong)" artifacts/Add
leancil verify artifacts/Add --proof Examples/Proofs/Add.lean
```

Verification first checks the extraction, prepares the source-keyed library cache in a private session, checks and kernel-replays the selected proof, and audits its axioms. `--fresh` bypasses the cache. It writes `artifacts/Add/verified.json` only after the proof and final identity checks succeed.

Output begins with the following summary, followed by the full theorem statement shown in the command-line section:

```text
Verified: ExampleProof.correctness
  Assembly: Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null
  Entry: System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)
  Proof: Examples/Proofs/Add.lean
  Axioms: propext, Quot.sound
  Settings: artifacts/Add/verification.json
  Report: artifacts/Add/verified.json
```

`verification.json` remembers the proof path and theorem, even if a later proof fails. To run verification again:

```sh
leancil verify artifacts/Add
```

Every `verify` run checks the proof afresh. For a new artifact directory, supply `--proof` or place your proof in `artifacts/Add/Proof.lean`. Use `--theorem` to select a theorem other than `ExampleProof.correctness`. Lean and Lake must be installed; the tool includes the framework's Lean sources.

For a quick extraction consistency check without running Lean:

```sh
leancil check artifacts/Add
```

The extraction CLI infers the assembly identity from the DLL's metadata. Optionally add `--assembly Examples` to require a specific short name, or supply a full identity to constrain version, culture and public key token as well. A mismatch is rejected. Generated artifacts always retain the actual full identity and assembly hash, including when `--assembly` is omitted.

Method selectors accept C# type aliases, an optional return type, and an unqualified declaring type when the result is unique. These all select the same method:

```text
System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)
ulong Examples.Arithmetic::Add(ulong,ulong)
Examples.Arithmetic::Add(ulong,ulong)
Arithmetic::Add(ulong,ulong)
```

The parameter list remains required. Matching is case-sensitive; an explicit return type must match. Use `ulong&` for a by-reference parameter. Ambiguous selectors fail with a list of full candidate signatures, which can be copied into the command. Artifacts always record the resolved canonical signature, so equivalent selectors can check the same artifact. Selection never relaxes supported-type or instruction validation.

The generated `Extracted.lean` contains `arg 0`, `arg 1`, `add`, `ret`, the exact method signature, metadata, profile and kernel-checked fetch equations; the assembly hash lives in `identity.json` and the report. The entry is method zero; reachable managed callees are emitted in dependency order.

Extraction also emits raw metadata and a `translation_valid` certificate. Independent Lean validators recompute layouts, check all layout-dependent sites and parameter-home mappings, validate structural generic substitution and managed-call bindings, and check feature-analysis states and control-flow coverage. Per-site validators walk the raw code, reachability mask and emitted code in lockstep, so a long branch excluded by the profile adds linear rather than quadratic checking cost. Verification requires this certificate to have the exact validator type for the complete emitted program and kernel-replays it separately from the user proof. Raw metadata serialization and transformations outside those checks remain trusted.

`Examples/Proofs/Add.lean` states the mathematical property independently: the returned word's natural value equals `(x.toNat + y.toNat) % 2^64`. Its universal proof derives execution from the generated program. Changing the implementation to subtraction causes the unchanged addition proof to fail. `WrongAdd.lean` independently proves a counterexample for every successful fuel budget.

### Try breaking the implementation

In `Examples/Assembly/Methods.cs`, change only `Add` to:

```csharp
public static ulong Add(ulong x, ulong y) => unchecked(x - y);
```

Rebuild, regenerate the extraction, and run the unchanged addition proof:

```sh
dotnet build Examples/Assembly -c Release
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::Add(ulong,ulong)" artifacts/Add
leancil verify artifacts/Add
```

Verification exits with `1`. Its diagnostic starts with:

```text
Invalid: Lean could not prove the selected theorem.
  Stage: proof checking
  Next: Read the Lean diagnostic below and check the implementation against the stated contract, including its preconditions.
```

The detailed Lean error follows. The contract still requires addition for arbitrary inputs, so the subtraction implementation cannot satisfy this proof. `verification.json` remains; `verified.json` is removed. Restore `x + y`, then repeat the three commands to recover a successful verification without repeating the proof arguments. Running `check` after rebuilding but before extraction instead reports that the assembly has changed and tells you to re-extract.

### Reject an invalid memory access

`PastEnd` advances a reference by one `ulong` and dereferences it. The example caller provides only one eight-byte allocation, so the access falls outside it:

```sh
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::PastEnd(ulong&)" artifacts/PastEnd
leancil verify artifacts/PastEnd --proof Examples/Proofs/PastEnd.lean
```

This prints `Verified: ExampleProof.correctness` and the theorem statement: for every fuel budget and result, execution with the example caller memory cannot return `Except.ok result`. Here the verified property is **rejection of the unsafe access**, not a claim that the method is safe. The proof also includes a concrete `.outsideAllocation` fault witness. Its caller memory is fixed; the theorem does not claim the access fails for every possible allocation layout.

`Tests/CliVerification.cs` automates the addition edit/rebuild/failure/recovery sequence in a disposable source copy, then checks this invalid-access theorem.

A verification report identifies the **specific named theorem and its printed type**, not all methods or all inputs automatically. `leancil check` validates extraction artifacts only; `leancil verify` runs the proof. A failed proof returns `1`, prints `Invalid:` and the diagnostic to standard error, and removes the previous verification report.

To prove another method, supply a unique method selector, write a Lean file importing `Extracted`, state a specification and prove it from `Extracted.program`. By default the driver checks `ExampleProof.correctness`; use `--theorem` for another name. `CIL.Safety.Ensures` expresses total correctness with successful finite execution. `VC` and `ensures_of_vc` expose a chosen finite execution condition. Simple concrete tests can use kernel reduction (`rfl`); symbolic checked-model proofs use ordinary Lean reasoning or `cil_checked_steps` from `CIL.Safety.SymbolicExecution`. The older `cil_steps` tactic targets the pure interpreter. Exhaustion and unsupported states are failures.

## Independent examples

- `Add`: universal modular arithmetic correctness in the specified empty initial memory.
- `CheckedArithmetic.Add64`: universal checked addition for every pair whose sum fits, over arbitrary caller memory, with exact memory preservation. The checked automation follows generated instruction lookups; the same contract is tested after inserting NOPs and rejected for subtraction.
- `Choose`: universal checked selection for both Boolean inputs and every pair of 64-bit values, preserving arbitrary caller memory exactly.
- `GenericIdentity`: universal identity through direct, repeated and nested generic calls in C#, and a compiled F# identity wrapper, preserving arbitrary caller memory exactly.
- `Loops.Countdown`: universal termination and a zero result for every `uint`, including zero and `UInt32.MaxValue`, using a decreasing natural-number measure over checked local storage.
- `Calls`: a managed-call chain with an address-taken mutable local.
- `IntegerOperations.Negate32` / `Negate64`: checked-execution proofs that negation returns the modular additive inverse for every input, including the signed minimum.
- `NarrowIntegers`: signed/unsigned casts, character values, calls and an eight-byte struct containing narrow fields. `UnsignedShort.lean` proves reduction modulo 65,536 for every 32-bit input.
- `PrimitiveOperations`: reads/writes through integer references, aliasing, switch tables and aggregate `sizeof`. `PrimitiveReadWrite.lean` proves that a store followed by a load returns every 32-bit input unchanged.
- `Alias`: two arguments naming the same caller storage.
- `Struct`: universal return of the input through a **12-byte explicit-layout struct**, initialization, two field stores and a byref helper call. For every well-formed caller memory, all earlier allocation metadata, bytes and access permissions are preserved; temporary frame allocations are expired on return. `StructCopy` separately checks by-value use of the same layout.
- `LargeStruct`: a **40-byte** explicit layout with a field at offset 32.
- `PastEnd`: a permitted end sentinel whose dereference is rejected as outside the allocation, for every fuel budget.
- `Escape`: a reference to an expired local is rejected on return, for every fuel budget.
- `WrongAdd`: a mathematical counterexample to the intended addition contract.
- A separate `Examples.Hardware` assembly, built from the file-based library `Examples/Hardware/Hardware.cs`, tests runtime capability extraction.
- A Cecil-generated independent fixture tests extraction-bound static RVA bytes.
- `StaticSpans` reads a 16-byte `ReadOnlySpan<byte>` lookup table; out-of-bounds reads, writes and tampered RVA bytes are checked.

Concrete example proofs establish their displayed inputs. Only explicitly universally quantified theorems claim arbitrary-input correctness. `CheckedAdd64`, `Choose` and `GenericIdentity` quantify caller memory and prove it unchanged. `Struct` quantifies well-formed caller memory and proves `MemoryBelow` preservation of the caller's storage. Other examples may require `Examples.empty` or `Examples.caller`; argument quantification alone does not imply arbitrary caller memory. The allocating generic instance wrapper retains a separate fixed-memory check in `GenericInstance.lean`.

## Loop verification

Reachable backward branches and switch targets are admitted when control-flow targets and stack joins validate. Feature reachability uses a fixed point: a backedge that invalidates a constant fact causes affected instructions to be revisited. Recursive managed calls remain unsupported.

Extraction does not establish termination. [The countdown proof](Examples/Proofs/Countdown.lean) uses `CIL.Safety.loop_terminates` with an invariant describing readable, writable counter storage and the measure `remaining.toNat`. The invariant location is found from the compiled branch instruction. `cil_loop_steps` checks the path between invariant locations and infers its execution cost; each iteration proves a strictly smaller measure; the zero case proves a successful return. `ensures_of_loop` lifts this to `CIL.Safety.Ensures`, so the theorem supplies successful finite execution for every input, including the maximum 32-bit unsigned value, without unrolling billions of iterations. Subtraction cannot underflow because it occurs only when the counter is positive.

The loop suite checks the unchanged universal proof after inserting NOPs and rearranging basic blocks. It also requires that proof to reject both an incorrect result and a loop whose counter never decreases.

```sh
leancil extract Examples/Assembly/bin/Examples.dll "Loops::Countdown(uint)" artifacts/Countdown
leancil verify artifacts/Countdown --proof Examples/Proofs/Countdown.lean
dotnet run --file scripts/Test.cs -- --suite loops
```

Loop invariants and decreasing measures are supplied by the proof author. The suite rejects an incorrect loop under the unchanged contract, checks malformed stack joins and changing loop facts, and proves that an admitted infinite loop exhausts every fuel budget. Fuel exhaustion is never successful verification of total correctness.

## F# examples

The [F# examples](Examples/FSharp/Examples.fs) demonstrate arithmetic, branching, real method calls, `byref` mutation and mutable structs with constructors. They use the same CIL semantics, extractor and Lean proof pipeline as the C# examples.

```fsharp
let Add (x: uint64) (y: uint64) = x + y
```

Verify the compiled F# addition with the existing language-independent [addition contract](Examples/Proofs/Add.lean):

```sh
dotnet build Examples/FSharp -c Release
leancil extract Examples/FSharp/bin/Examples.FSharp.dll "Arithmetic::Add(ulong,ulong)" artifacts/FSharpAdd
leancil verify artifacts/FSharpAdd --proof Examples/Proofs/Add.lean
```

The theorem proves `(x + y) mod 2^64` for every pair of 64-bit inputs. The suite also checks universal store/load and constructor contracts, compares compiled F# results with checked CIL execution, and rejects subtraction under the unchanged addition contract:

```sh
dotnet run --file scripts/Test.cs -- --suite fsharp
```

These examples cover F# programs that compile into the supported CIL subset. F# lists, closures, discriminated unions and arbitrary FSharp.Core calls are not generally supported; the suite includes an explicitly rejected list example.

The `GenericMethods` module also demonstrates generic identity and selection functions. LeanCIL specializes their compiled CIL for the concrete value types used by reachable calls. The F# and C# identity examples share the same [universal Lean contract](Examples/Proofs/GenericIdentity.lean):

```sh
leancil extract Examples/FSharp/bin/Examples.FSharp.dll "GenericMethods::Identity64(ulong)" artifacts/FSharpIdentity
leancil verify artifacts/FSharpIdentity --proof Examples/Proofs/GenericIdentity.lean
dotnet run --file scripts/Test.cs -- --suite generics
```

## Supported subset and limits

The [opcode support table](docs/OPCODES.md) lists every opcode currently translated by the extractor, including short forms, operand restrictions and execution limits. **Complete** means complete within the admitted value/memory model; **partial** means additional cases are excluded. Neither label claims complete CLR coverage or proves a particular method correct.

| Opcode family | Status | Main restriction |
| --- | --- | --- |
| `ldc.i4` and its short forms, `ldc.i8`, `dup`, `pop` | Complete within the admitted model | Integer constants and supported stack values |
| Argument/local loads and stores, `ldloca` | Partial | Admitted types; no address of a managed-reference local |
| `add`, `sub`, `mul`, bitwise operations, shifts, selected comparisons/conversions | Partial | Supported integer operand shapes; no floating-point or checked-overflow arithmetic |
| Supported branches | Partial | Validated cyclic control flow; integer conditions/comparisons; termination requires a separate proof |
| `call`, `ret` | Partial | Acyclic static/struct instance methods, concrete generic-method specializations and explicitly modelled runtime calls |
| Integer `ldind.*` / `stind.*`, `ldobj`, `stobj`, `cpobj`, `initobj`, fields, `ldsflda` | Partial | Checked references, validated integer/aggregate layouts and restricted static data |
| `initblk`, `cpblk`, `unaligned.` | Partial | Checked managed references, 32-bit byte counts and validated alignment prefixes; overlapping block copies rejected |
| `switch`, `sizeof` | Partial | Forward jump tables and validated integer and reference-free aggregate sizes |
| `newobj` | Partial | Validated reference-free struct constructors and the modelled byte-span constructor; no class allocation |
| Argument storage | Partial | Parameter assignment and addressing, shared aliases, narrow/native storage and frame lifetime checks |
| Native integers | Partial | `nint`/`nuint` signatures, locals, fields, memory, casts, arithmetic and `sizeof` on validated 64-bit targets |
| Checked integer conversions | Partial | Integer inputs; signed/unsigned bounds, narrow extension and native-width destinations |
| Checked integer arithmetic | Partial | Signed/unsigned 32-/64-bit add, subtract and multiply; explicit overflow faults |
| Integer division and remainder | Partial | Signed/unsigned 32-/64-bit operands; explicit zero-divisor and overflow faults |
| All other opcodes | Unsupported | Includes `callvirt`, arrays and instruction prefixes |

The initial extraction target is Release, IL-only **.NET 10**, 64-bit little-endian execution. Supported scalar operations include 32/64-bit wrapping arithmetic, bitwise operations, shifts, selected conversions/comparisons, conditional/unconditional branches, local and argument loads/stores, 64-bit indirect access, and acyclic managed calls to static methods and reference-free struct instance methods. Struct methods receive a checked managed-reference `this`; direct constructor calls on existing storage and `newobj` construction of validated structs are supported. Explicit- and sequential-layout reference-free aggregates use validated sizes and byte offsets; fields admit narrow, 32-bit, 64-bit and native integer storage, including same-assembly enums backed by the eight C# enum integer types and nested reference-free structs. Nested fields support references, snapshots and whole-value assignment, with validated packing and padding. Enum parameters, returns, locals, references and flags use the underlying integer semantics, including unnamed values. Boxing and `System.Enum` methods remain unsupported. SIMD models cover selected Vector128/256, SSE, AVX, AVX2, AVX512, BMI and ARM operations, as enumerated in `CIL/SIMD` and `Extractor/RuntimeModels.cs`.

The extractor rejects unmodelled instructions, recursive managed calls, exception handling, class instance/virtual dispatch, managed object construction, reference-bearing aggregates, general arrays, unsupported packing, floating-point arithmetic, arbitrary external calls, static constructors, and unsupported signatures. Not every combination of the model's standalone instructions is exposed by the extractor. New features require validation, semantics, proofs and regressions.

Profiles default to scalar. Pass a supported profile name or `@profile.json` as the final positional argument to `leancil extract`. Both `check` and `verify` recover the profile from the manifest. Capability prerequisites are validated. Instructions unreachable under that exact fixed profile are emitted as explicit unsupported placeholders; changing profiles invalidates artifacts.

The memory model checks allocation identity, liveness, bounds, byte permissions, initialization, alignment and GC-sensitive intervals. It supports overlap and distinct private frames. It does not prove JIT/compiler correctness, concurrency, GC implementation correctness, OS memory behaviour or arbitrary .NET runtime equivalence. See [soundness and trusted base](docs/SOUNDNESS.md) for the precise boundary.

Stores reuse existing read permissions when they already cover the written range, including coverage spread across multiple views. The `write_run_equivalent` theorem proves that replacing the previous always-prepending write preserves any subsequent checked execution: returned values, exact faults, allocation state, bytes and permissions. `Memory.Equivalent.run` and `.invoke` cover branches, calls, constructors and frame cleanup.

Run `pwsh scripts/BenchmarkViews.ps1 -Stores 128 -Repetitions 3` to compare kernel reduction against the previous write implementation. In a local Windows run with Lean 4.35.0, 128 alternating stores retained 1 view instead of 129; median elapsed time was 5.6 seconds versus 17.7 seconds. These timings include process startup and shared-machine activity; view counts are checked by kernel reduction.

### Portable bit and endian helpers

`BitOperations.RotateLeft`, `RotateRight`, `PopCount`, `LeadingZeroCount`, `TrailingZeroCount`, `Log2` and `RoundUpToPowerOf2` support `uint`, `ulong` and `nuint`. `IsPow2` also supports their signed counterparts. `BinaryPrimitives.ReverseEndianness` supports signed and unsigned 8-, 16-, 32-, 64-bit and native integers. These calls work with every hardware profile. Other overloads remain unsupported; see the [exact coverage](docs/OPCODES.md#portable-scalar-runtime-helpers).

Integer `Math.Min`, `Max`, `Clamp`, `Abs` and `Sign` are also supported, including narrow and native integers. Verification checks `Abs` overflow and invalid `Clamp` bounds explicitly.

`Unsafe.SizeOf<T>` and managed-reference `Unsafe.Add<T>` use validated managed layouts for supported primitives, enums, reference-free structs and vectors. Reference arithmetic retains allocation identity and checks lifetime and bounds; it does not grant access to memory outside the caller's permissions.

`Unsafe.SkipInit<T>` supports the same admitted storage types. It consumes a valid
managed reference and preserves memory, including byte initialization flags.
Reading an uninitialized byte after the call still fails checked execution;
subsequent stores must satisfy the normal write permissions. Extraction evidence
independently binds the runtime call to the `skipInit` instruction.

The `Examples.Bits` methods exercise these APIs, including universal proofs of the integer logarithm and of a rotation round trip. Incorrect implementations fail the same contracts. `Log2(0)` returns zero; rounding up returns zero for zero input or overflow; signed power-of-two checks reject negative values.

### Vector and hardware intrinsics

Each family has partial coverage. The [intrinsic support tables](docs/SIMD.md) give the exact accepted overloads, element types, immediate bounds and profile requirements.

| Family | Extractable operations |
| --- | --- |
| [Vector128 / Vector256](docs/SIMD.md#vector128-and-vector256) | Selected integer arithmetic, bitwise/equality operators, lane comparisons, construction, extraction, reductions, arithmetic shifts and bit reinterpretation |
| [SSE](docs/SIMD.md#sse) | `Sse2.ShiftLeftLogical128BitLane`, `Ssse3.AlignRight`; SSE4.1/4.2 getters only |
| [AVX](docs/SIMD.md#avx) | Selected `MoveMask`, `Blend`, `TestZ` overloads |
| [AVX2](docs/SIMD.md#avx2) | `Permute4x64`, `Blend`, `Add`, `CompareEqual`, `CompareGreaterThan`, widening even-lane `Multiply`, logical shifts |
| [AVX512](docs/SIMD.md#avx512) | F.VL alignment, ternary logic and unsigned comparisons; DQ mask extraction and DQ.VL low multiplication, all on 256-bit vectors |
| [BMI](docs/SIMD.md#bmi) | `Bmi1.BitFieldExtract(uint, byte, byte)`, `Bmi2.X64.MultiplyNoFlags(ulong, ulong)` |
| [ARM](docs/SIMD.md#arm) | `AdvSimd.ExtractVector128` on `ulong` lanes, `ArmBase.Arm64.MultiplyHigh(ulong, ulong)` |

An enabled CPU feature does not imply support for all of its APIs. Float/double vectors are used only for selected bit operations, not floating-point arithmetic. Vector64 and Vector512 are not supported. See the [profile table](docs/SIMD.md#feature-getters-profiles-and-execution-restrictions) for the exact flags enabled by each built-in profile.

## Using LeanCIL in another project

Pin LeanCIL as a Lake dependency and import the required `CIL.*` modules. Keep application specifications, method proofs and coverage policies in the consuming project. See [integration guidance](docs/MIGRATION.md) and [validation results](docs/VALIDATION.md).

## Verification CI

Pushes to `main` and manual runs execute every verification suite. Pull requests
select suites from changed test entry points, referenced proofs, and their
transitive source imports. Markdown and license-only changes skip the expensive
suites. Shared framework, extractor, fixture projects, build configuration,
workflow changes, and unrecognized paths conservatively run the full matrix.

The required `Build and verify` check always runs. It succeeds only when selection
succeeds and every selected suite passes, or when selection explicitly reports
that no suites are needed. Failed or cancelled selection/tests cannot pass it.
Keep this aggregate check required rather than individual matrix jobs, which may
be absent on a PR. Run `dotnet run --file scripts/TestSelectVerification.cs` to test the
selection rules and final gate locally.

## License

[MIT](LICENSE).
