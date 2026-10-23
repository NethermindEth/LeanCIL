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
It is read only when a reachable call resolves to `Lib`, so sidecars of uncalled
libraries need no pins and never enter the extraction. The implementation defaults to `Lib.dll` next to the sidecar, then next to the
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
overrides can be supplied again for an explicit recheck. `identity.json` records
sidecar and implementation paths relative to the output directory, as it does
`assemblyPath`, so a moved extraction rechecks against the moved files.

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

Unknown properties, duplicate JSON properties, missing fields and invalid digest
or identifier forms are rejected. Methods must be static, non-virtual, public or
protected, non-P/Invoke, and non-generic. Instance, constructor, function pointer
and virtual call sites are rejected. Import signatures must use supported
parameter and result types with matching assembly-scoped type identities.
Profiles must name an exact built-in profile; custom profiles are not admitted.
For an implementation DLL, the selected export must satisfy the closed v1
producer's admission rules without external initialization assumptions. Its
reachable static identity set must match the selected certification exactly.
This checks metadata and serialization; it does not verify the imported theorem.
Static identities from App and all selected imports are checked together before
output. A collision reports both scoped field names.

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
the consumer, and are reported as such. No pinned digest covers them: the
interface digest excludes certifications and the consumer cannot recompute
`statementDigest`. Reports therefore set `certificationAuthenticated` to `false`
and record the `sidecarSha256` the text came from.

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
that the named value has that actual framework contract type. The audit compares
the head constant of that type, so a contract typed through an `abbrev` of
`MethodContract` or `OutcomeContract` is rejected; declare it with the framework
structure directly. A user-defined
`Contract.Holds` predicate cannot replace this check. Each contract applies to
the actual linked program and its absolute slot. No body, axiom, summary or
implementation proof is generated for an import.

The caller theorem must have the conditional form:

```
CIL.Safety.HoldsGiven Extracted.program Extracted.ImportsHold claim
```

This retains both `Links` and the required imported contracts. The theorem audit
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
runs before a successful report is published. Existing schema-2 extractions must
be regenerated to acquire these records.

Run `dotnet run --file scripts/Test.cs -- --suite imports` for the Lib/App
fixture, conditional caller proof, stale DLL/source checks and rejecting cases.
