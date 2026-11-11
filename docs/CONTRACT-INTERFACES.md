# Contract interface imports

Read this page to verify a caller against a contract that a separately compiled library
publishes in a sidecar file, `Lib.leancil.contracts`. It covers the `extract` options, the
sidecar schema, the form the caller theorem must have and what the result does and does not
establish. Publishing a sidecar is in
[publishing verified contracts](CONSUMERS.md#publishing-verified-contracts); generic instances
and struct references are in [typed imports](TYPED-IMPORTS.md).

`extract` can bind a plain static external `call` to a contract slot. The implementation DLL is
read as metadata: its method bodies are not copied into the caller program, and the imported
method has no body in the unlinked program.

```
leancil extract App.dll 'App::Entry(ulong)' extracted scalar \
  --import Lib.leancil.contracts \
  --import-implementation Lib=/path/to/Lib.dll \
  --import-sha256 Lib=<independently-supplied-sha256> \
  --import-interface-sha256 Lib=<independently-supplied-interface-digest>
leancil check extracted
```

| Option | Meaning |
| --- | --- |
| `--import path` | A sidecar. Optional when `Lib.leancil.contracts` lies next to the application, where it is discovered. |
| `--import-implementation Lib=path` | The implementation DLL; an explicit path overrides discovery. The default is `Lib.dll` next to the sidecar, then next to the application. |
| `--import-sha256 Lib=hex` | The independently supplied SHA-256 of the implementation DLL. This option is required. |
| `--import-interface-sha256 Lib=digest` | The independently supplied interface digest. This option is required. |

A discovered sidecar is read only when a reachable call resolves to `Lib`, so sidecars of
uncalled libraries need no pins and never enter the extraction. A hash found in the same sidecar
cannot serve as the independent `--import-sha256` input. A supplied digest establishes byte
identity; it does not establish authenticity or prove the implementation.

`--import-interface-sha256` pins the canonical interface descriptor, including every Lean source
byte, and is required before the interface is staged or compiled. Obtain it through your
accepted publisher channel. Interface sources can execute Lean metaprograms and IO with verifier
permissions, and accepting their digest accepts execution of those exact sources. A digest is
neither a sandbox nor independent publisher authentication. Rechecks enforce the recorded
independent interface pin before compilation.

`check` reopens recorded sidecars and implementations and recomputes their hashes, metadata,
generated CIL, import slots and interface sources. After the DLL changes it reports both the
expected and actual implementation SHA-256. CLI path/hash overrides can be supplied again for
an explicit recheck. `identity.json` records sidecar and implementation paths relative to the
output directory, as it does `assemblyPath`, so a moved extraction rechecks against the moved
files.

## Resolving imports from SDK assets

`resolve-imports` turns SDK output into the explicit `--import` and `--import-implementation`
arguments of `extract`. It only locates files: `extract` never reads deps.json or NuGet assets,
and the independent pins stay required.

```
leancil resolve-imports bin/App.dll --library Lib \
  --assets obj/project.assets.json --runtime-identifier linux-x64 \
  --rid-graph "$(dotnet msbuild App.csproj -getProperty:RuntimeIdentifierGraphPath)" \
  --output resolved.json
```

| Option | Meaning |
| --- | --- |
| `--library Lib` | A library to resolve; at least one, repeatable. List every required library, including transitive contract dependencies: sidecar dependencies are not followed. |
| `--deps file` | The deps file. The default is `App.deps.json` next to the application. |
| `--assets file` | The NuGet assets file, `obj/project.assets.json`. One of the deps and assets files is required. |
| `--package-root directory` | An extra package root, repeatable; the `packageFolders` of the assets file are used too. |
| `--runtime-identifier RID` | The target RID; it must not conflict with the deps file's runtime target. |
| `--rid-graph file` | The SDK's `PortableRuntimeIdentifierGraph.json`. |
| `--profile name` or `@profile.json` | The execution profile; see the architecture rule below. |
| `--output file` | Write the result as JSON there. The default is standard output. |

Only `net10.0` targets are accepted. The command does not restore, use the network, or infer a
RID from the host.

Selection follows the .NET 8+ host and NuGet. RID fallback is NuGet's breadth-first
`RuntimeGraph.ExpandRuntime` over the SDK's `PortableRuntimeIdentifierGraph.json`. For
`linux-x64` the fallback list is `linux-x64`, `linux`, `unix-x64`, `unix`, `any`, `base`; the
host's built-in list is the prefix of that list through `any`. A deps.json `runtimes` section
is never read; the host ignores it too unless `UseRidGraph` is set. A library's best-matching RID
group replaces its whole portable `runtime` group; with no match, the portable group applies. A
library with RID-specific runtime assets needs `--runtime-identifier` and `--rid-graph`.

deps.json assets are probed in the application directory as hostpolicy does: at `localPath`
(written for executables), else at a RID asset's relative path, else at the bare file name.
Package assets are probed at `<root>/<package path>/<asset path>`. Copies with different bytes
are rejected.

The RID must be x64 or arm64. A fallback that ends in another architecture is rejected.
`--profile` defaults to scalar, as `extract` does; any other profile must agree with the RID's
architecture. Compile assets never become implementations. A reference-only selection fails.

`Nethermind.LeanCIL.LeanCilContractsAttribute(string digest)` on the runtime or reference
assembly advertises the interface digest; declare it in the library source with assembly-only,
non-repeatable usage. The attribute locates a sidecar and pins nothing. The resolver looks for
`Lib.leancil.contracts` and `contracts/<digest>.leancil.contracts` in the application,
implementation and package directories. The located sidecar must name the library and, when
advertised, carry that digest. The output lists each import's library, asset path, matched RID,
implementation and sidecar, plus the arguments for `extract`.

## Sidecar schema 1

Required fields of a sidecar:

- `schema`, `semanticsVersion`, `formatVersion`: each is `1`.
- `frameworkKey`: SHA-256 of the sorted framework source manifest described below.
- `assemblyIdentity`, `mvid`, `targetFramework`, `implementationSha256`, and
  `isReferenceAssembly`: exact implementation metadata and bytes. Target framework
  is `.NETCoreApp,Version=v10.0`. Reference assemblies are authoring-only; caller proofs can be
  checked, but no successful verification report is published.
- `interfaceModules`: module names and full Lean source strings. Names are plain
  dotted identifiers. Framework, toolchain, generated, example and test module
  roots and the driver's `LeanCIL*` modules are reserved. Names are compared
  ignoring case, since case variants collide on Windows and macOS. Duplicate
  modules and conflicting definitions are rejected.
- `interfaceDigest`: the canonical descriptor digest described below.
- `exports`: exact assembly-scoped method identity, Cecil full signature,
  `parameterCount`, `hasThis`, `returnsValue`, `visibility`, `contractConstant`,
  `closureDigest`, `profiles`, and `kind` (`method` or `outcome`).
- `certifications`: records with `identity`, `profile`, `implementationSha256`,
  `interfaceDigest`, `closureDigest`, `theorem`, `statement`, `statementDigest`,
  and `staticIdentities`. Each static entry has a decimal-string `identity`,
  `assemblyIdentity`, and `fieldName`. The selected record must bind the
  selected export, profile, DLL and interface.
- `dependencies`: an empty array in version 1.
- `fullVerificationLocator`: optional provenance metadata. This importer does not
  fetch or verify the named artifact.

Unknown properties, duplicate JSON properties, missing fields and invalid digest or identifier
forms are rejected. Methods must be static, non-virtual, public or protected, non-P/Invoke and
non-generic. Instance, constructor, function pointer and virtual call sites are rejected.
Import signatures must use supported parameter and result types with matching assembly-scoped
type identities. Profiles must name an exact built-in profile; custom profiles are not admitted.

For an implementation DLL, the selected export is validated with its independently pinned
direct dependencies and its explicitly declared initialization assumptions. Its own reachable
static identity set must match the selected certification exactly. This validation checks
metadata and serialization; it does not verify the imported theorem.

An optional `initializationAssumptions` descriptor records each exported profile's sorted
assembly/type pairs and participates in the interface digest. Each local type must have a
static constructor in the selected implementation. These premises require the implementation
DLL; a reference-only import is rejected. Imported dependency premises must match those reached
by implementation validation exactly. The exporter kernel-checks and structurally audits
equality with the generated `Extracted.initializationAssumptions` list. Callers propagate this
list into their generated source, identity and report; exporting such a caller propagates it
again. The assumptions are deployment premises that initialization completed successfully. They
are not CLR initialization theorems or field-value guarantees. Recorded `staticValues`,
including unknown ones, are unexportable, and forced full verification rejects initialization
premises.

Each node's static identities are checked with those of its direct imports before output, and a
collision reports both scoped field names. Extraction does not compare every pair of graph
nodes: conditional transitive proofs retain the `StaticWorldValid` premises, and
[full verification](FULL_VERIFICATION.md) checks all descriptors of its linked program with
`linkChecked`, including those of dependencies linked into an imported library.

The framework manifest lists `CIL.lean`, all `CIL/**/*.lean`, and `lean-toolchain`
in ordinal relative-path order. Paths use `/`. Each line is `path=sha256(bytes)`.
Join lines with `\n` and no final newline, then hash the UTF-8 bytes. The CLI
uses the framework sources packaged with the executable. It does not read them from the current
working directory. The framework key identifies the framework sources. It is not a semantic
preservation theorem.

The canonical interface descriptor serializes these fields in this order:
`schema`, `semanticsVersion`, `formatVersion`, `frameworkKey`, `assemblyIdentity`,
`targetFramework`, `interfaceModules`, `exports`, `dependencies`. Use compact
`System.Text.Json` serialization with the declared record field order, camel-case
property names, and its default string escaping. Arrays retain their order.
Every interface module source and every qualified contract name is included in this digest.
The descriptor excludes MVID, implementation SHA-256, certification records and
full-verification locator, so a rebuild can retain its interface digest when its
source interface and assembly identity do not change.

`closureDigest` is recomputed from the canonical exported contract closure and
must equal the selected certification record. The closure includes definition values,
theorem/inductive types, constructor metadata and recursor computation rules.

A certification record does not supply a Lean implementation proof. Its theorem,
statement and statement digest are publisher provenance accepted by
the consumer, and are reported as such. No pinned digest covers them: the
interface digest excludes certifications. Hashing the reported statement cannot
authenticate a publisher's theorem. Reports therefore set `certificationAuthenticated` to `false`
and record the `sidecarSha256` the text came from.

## Generated proof interface and guarantees

Import slot `j` is `Extracted.program.length + j`. `Extracted.lean` contains its
full method identity, shape and closure digest. The kernel-checked
`ManagedCallsValid` certificate binds each live raw external call to that slot.
It checks call opcode, identity, type arguments, argument count, receiver and
return arity. The implementation hash is absent from `Extracted.lean`.

`ExtractedImports.lean` imports the declared interface sources and defines:

```
def Extracted.ImportsHold (linked : _root_.CIL.Program) : Prop :=
  @_root_.CIL.Safety.MethodContract.Holds _ _ _root_.Library.Contract linked <absolute-slot>
```

Several slots form a conjunction. The selected kind uses the fully qualified
framework `MethodContract.Holds` or `OutcomeContract.Holds` predicate. Both the
framework predicate and selected contract use `_root_` qualification, so an
`Extracted` namespace declaration cannot replace either one. Lean checks
that the named value has that framework contract type. The audit compares
the head constant of that type, so a contract typed through an `abbrev` of
`MethodContract` or `OutcomeContract` is rejected; declare it with the framework
structure directly. A user-defined
`Contract.Holds` predicate cannot replace this check. Each contract applies to
the linked program and its absolute slot. No body, axiom, summary or
implementation proof is generated for an import.

The caller theorem must have the conditional form:

```
CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold claim
```

This form retains both `Links` and the required imported contracts. The theorem audit
(`leancil-audit`, on replayed oleans) compares the compiled theorem type with this
application structurally, so no binder may precede it, and requires the compiled
value of `Extracted.ImportsHold` to equal the conjunction rebuilt from
`identity.json`: each slot's root contract at the canonical `Nat` numeral. An
interface `OfNat` instance, notation or elaborator therefore cannot retarget a
slot. This shape check does not establish that an arbitrary `claim` is useful.
The caller proof supplies the intended claim. A concrete linked implementation
must separately discharge the import contracts before this conditional result
can establish an unconditional application guarantee.

The verifier stages the exact interface sources, includes them in proof cache
identities, compiles them, and performs kernel replay. `leancil-audit` then
validates the interface declarations and computes each canonical closure from the
replayed oleans, without running interface code; no compiler output is read, so
an interface macro or elaborator cannot forge a closure. The compiled interface
artifacts are hashed before replay and must keep those hashes after the audit
and before each later step. Consumer workspaces also
reject source-name collisions and include their hashes in snapshot checks.
Schema-4 reports list `imports` accepted via `published-certification`, as well
as `contractImports`; CLI output states the conditional assumptions and deployment
obligations.
Hashes and certification records never discharge those assumptions.

`identity.json` schema 3 records each slot's identity, implementation path/hash,
kind, sidecar path/hash, interface digest, contract constant and closure digest.
It also hashes each generated interface source. The final extraction recheck
runs before a successful report is published. A manifest of another schema is
rejected; run `leancil extract` again.

## Transitive imports

[Transitive contract imports](CONSUMERS.md#transitive-contract-imports) states how to supply and
pin a dependency graph. The graph rejects cycles before method validation. Each library
implementation is checked against its declared direct dependencies with separate call slots,
and validation compares its actual static identity set with its certification record. A
supplied library does not authorize an undeclared dependency.
