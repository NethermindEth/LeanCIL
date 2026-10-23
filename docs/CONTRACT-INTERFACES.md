# Contract interface imports

`extract` can bind a plain static external `call` to a contract slot. The
implementation DLL is read as metadata. Its method bodies are not copied into
the caller program. The imported method has no body in the unlinked program.

```
leancil extract App.dll 'App::Entry(ulong)' extracted scalar \
  --import Lib.leancil.contracts \
  --import-implementation Lib=/path/to/Lib.dll \
  --import-sha256 Lib=<independently-supplied-sha256> \
  --import-interface-sha256 Lib=<independently-supplied-interface-digest>
leancil check extracted
```

A sidecar next to the application is discovered as `Lib.leancil.contracts`.
The implementation defaults to `Lib.dll` next to the sidecar, then next to the
application. Explicit implementation paths override discovery. A separate
`--import-sha256` is required on extraction. A hash found in the same sidecar
cannot serve as that independent input. A supplied digest establishes byte
identity; it does not establish authenticity or prove the implementation.

An independent `--import-interface-sha256` is also required before staging or
compiling the interface. It pins the canonical interface descriptor, including
every Lean source byte. Obtain it through your accepted publisher channel.
Interface sources can execute Lean metaprograms and IO with verifier permissions.
Accepting their digest accepts execution of those exact sources. A digest is
neither a sandbox nor independent publisher authentication. Rechecks enforce
the recorded independent interface pin before compilation.

`check` reopens recorded sidecars and implementations. It recomputes their hashes,
metadata, generated CIL, import slots and interface sources. It reports both the
expected and actual implementation SHA-256 after the DLL changes. CLI path/hash
overrides can be supplied again for an explicit recheck.

## Resolving imports from SDK assets

`resolve-imports` turns SDK output into the explicit `--import` and
`--import-implementation` arguments above. It only locates files. `extract`
never reads deps.json or NuGet assets, and the independent pins stay required.

```
leancil resolve-imports bin/App.dll --library Lib \
  --assets obj/project.assets.json --runtime-identifier linux-x64 \
  --rid-graph "$(dotnet msbuild App.csproj -getProperty:RuntimeIdentifierGraphPath)" \
  --output resolved.json
```

It reads `App.deps.json` next to the application, or `--deps file`, and
optionally `--assets file`. Package roots come from the assets `packageFolders`
and `--package-root directory`. Only `net10.0` targets are accepted. It does not
restore, use the network, or infer a RID from the host.

Selection follows the .NET 8+ host and NuGet. RID fallback is NuGet's
breadth-first `RuntimeGraph.ExpandRuntime` over the SDK's
`PortableRuntimeIdentifierGraph.json`; for `linux-x64` that is `linux-x64`,
`linux`, `unix-x64`, `unix`, `any`, `base`, matching the host's built-in list. A
deps.json `runtimes` section is never read; the host ignores it too unless
`UseRidGraph` is set. A library's best-matching RID group replaces its whole
portable `runtime` group. With no match, the portable group applies. A library
with RID-specific runtime assets needs `--runtime-identifier` and `--rid-graph`.
deps.json assets are probed in the application directory at their `localPath`,
or at the bare file name without one, as the host does. Package assets are probed
at `<root>/<package path>/<asset path>`. Copies with different bytes are rejected.

The RID must be x64 or arm64. A fallback that ends in another architecture is
rejected, and `--profile` must agree with the RID unless it is scalar. Compile
assets never become implementations. A reference-only selection fails.

`Nethermind.LeanCIL.LeanCilContractsAttribute(string digest)` on the runtime or
reference assembly advertises the interface digest; declare it in the library
source with assembly-only, non-repeatable usage. The resolver looks for
`Lib.leancil.contracts` and `contracts/<digest>.leancil.contracts` in the
application, implementation and package directories. The located sidecar must
name the library and, when advertised, carry that digest. The output lists each
import's library, asset path, matched RID, implementation and sidecar, plus the
arguments for `extract`. The attribute is a locator, not a pin.

## Sidecar schema 1

`Tests/ContractImports/Lib.leancil.contracts` is a hand-written template. The
`imports` test suite fills its build-specific hashes and MVID. Required fields:

- `schema`, `semanticsVersion`, `formatVersion`: each is `1`.
- `frameworkKey`: SHA-256 of the sorted framework source manifest described below.
- `assemblyIdentity`, `mvid`, `targetFramework`, `implementationSha256`, and
  `isReferenceAssembly`: exact implementation metadata and bytes. Target framework
  is `.NETCoreApp,Version=v10.0`. Reference assemblies are authoring-only; caller proofs can be checked, but no successful verification report is published.
- `interfaceModules`: module names and full Lean source strings. Names are plain
  dotted identifiers. Framework, toolchain, generated, example and test module
  roots are reserved. Duplicate modules and conflicting definitions are rejected.
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

Unknown properties, duplicate JSON properties, missing fields and invalid digest
or identifier forms are rejected. Methods must be static, non-virtual, public or
protected, non-P/Invoke, and non-generic. Instance, constructor, function pointer
and virtual call sites are rejected. Import signatures must use supported
parameter and result types with matching assembly-scoped type identities.
Profiles must name an exact built-in profile; custom profiles are not admitted.
For an implementation DLL, the selected export is validated with its independently
pinned direct dependencies and without external initialization assumptions. Its
own reachable static identity set must match the selected certification exactly.
This checks metadata and serialization; it does not verify the imported theorem.
Each node's static identities are checked with those of its direct imports before
output. A collision reports both scoped field names. `linkChecked` checks all
descriptors in the complete linked program.

The framework manifest lists `CIL.lean`, all `CIL/**/*.lean`, and `lean-toolchain`
in ordinal relative-path order. Paths use `/`. Each line is `path=sha256(bytes)`.
Join lines with `\n` and no final newline, then hash the UTF-8 bytes. The CLI
uses the framework sources packaged with the executable, not the current working
directory. This is a framework identity, not a semantic preservation theorem.

The canonical interface descriptor serializes these fields in this order:
`schema`, `semanticsVersion`, `formatVersion`, `frameworkKey`, `assemblyIdentity`,
`targetFramework`, `interfaceModules`, `exports`, `dependencies`. Use compact
`System.Text.Json` serialization with the declared record field order, camel-case
property names, and its default string escaping. Arrays retain their order.
The descriptor excludes MVID, implementation SHA-256, certification records and
full-verification locator. A rebuild can retain its interface digest when its
source interface and assembly identity do not change. Every interface module
source and every qualified contract name is included in this digest.

`closureDigest` is recomputed from the canonical exported contract closure and
must equal the selected certification record. This includes definition values,
theorem/inductive types, constructor metadata and recursor computation rules.
A certification record does not supply a Lean implementation proof. Its theorem,
statement and canonical statement digest are publisher provenance accepted by
the consumer, and are reported as such.

## Generated proof interface and guarantees

Import slot `j` is `Extracted.program.length + j`. `Extracted.lean` contains its
full method identity, shape and closure digest. The existing kernel-checked
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
that the named value has that actual framework contract type. A user-defined
`Contract.Holds` predicate cannot replace this check. Each contract applies to
the actual linked program and its absolute slot. No body, axiom, summary or
implementation proof is generated for an import.

The caller theorem must have the conditional form:

```
CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold claim
```

This retains both `Links` and the required imported contracts. The theorem audit
checks this shape in addition to the existing theorem-kind and transitive axiom
audit. This shape check does not establish that an arbitrary `claim` is useful.
The caller proof supplies the intended claim. A concrete linked implementation
must separately discharge the import contracts before this conditional result
can establish an unconditional application guarantee.

The verifier stages the exact interface sources, includes them in proof cache
identities, compiles them, and performs kernel replay. Consumer workspaces also
reject source-name collisions and include their hashes in snapshot checks.
Schema-4 reports list `imports` accepted via `published-certification`, as well
as `contractImports`; CLI output states the conditional assumptions and deployment
obligations.
Hashes and certification records never discharge those assumptions.

`identity.json` schema 3 records each slot's identity, implementation path/hash,
kind, sidecar path/hash, interface digest, contract constant and closure digest.
It also hashes each generated interface source. The final extraction recheck
runs before a successful report is published. Existing schema-2 extractions must
be regenerated to acquire these records.

Run `dotnet run --file scripts/Test.cs -- --suite imports` for the Lib/App
fixture, conditional caller proof, stale DLL/source checks and rejecting cases.

For transitive imports, each dependency node must have its own independently
pinned implementation and interface digest. The graph rejects cycles before
method validation. Each library implementation is checked against its declared
direct dependencies with separate call slots. Validation compares its actual
static identity set with its certification record. A supplied library does not
authorize an undeclared dependency. Application slots contain only calls made
by the selected application methods.
