# Command-line reference

This page documents every `leancil` command: its arguments, options, output files and failure
modes. For one complete verification, read the [getting-started guide](GETTING-STARTED.md) first.

| Command | Purpose | Reference |
| --- | --- | --- |
| `leancil list assembly.dll` | Print the method signatures of an assembly | [Discover and select methods](#discover-and-select-methods) |
| `leancil extract` | Validate a method and its reachable calls and translate them to Lean | [Extract](#extract) |
| `leancil blockers` | Report everything that stops `extract` for a list of methods | [Report extraction blockers](#report-extraction-blockers) |
| `leancil check` | Compare extraction artifacts with their assembly and settings | [Check](#check) |
| `leancil new-proof` | Write a starting proof with marked holes | [Start a proof](#start-a-proof) |
| `leancil verify` | Check, kernel-replay and audit one theorem | [Verify](#verify) |
| `leancil verify-batch` | Verify many requests in one session | [Batch verification](CONSUMERS.md#batch-verification) |
| `leancil gates` | Build, extract and verify a catalog of methods, profiles, proofs and regression variants | [Run a proof catalog](CONSUMERS.md#run-a-proof-catalog) |
| `leancil workspace` | Generate a method's extraction into a Lake package for editor goals | [Editor workspace](#editor-workspace) |
| `leancil watch` | Rebuild, re-extract and verify on change | [Watch](CONSUMERS.md#watch) |
| `leancil export-contracts` | Publish verified contracts as a sidecar | [Export contracts](#export-contracts) |
| `leancil resolve-imports` | Locate contract sidecars and implementations from SDK output | [Resolving imports](CONTRACT-INTERFACES.md#resolving-imports-from-sdk-assets) |
| `leancil audit-library` | Kernel-replay and axiom-audit the theorems of a Lean library | [Library audits](CONSUMERS.md#library-audits) |
| `leancil templates` | Generate shared proof templates from extractions of several profiles, or check generated ones | [Generated profile templates](PROOFS-BINDING.md#generated-profile-templates) |
| `leancil lint-exceptions` | Compare modeled throw sites with XML documentation | [Exception documentation lint experiment](#exception-documentation-lint-experiment) |
| `leancil --version` | Print the tool, framework and toolchain versions | [Version](#version) |

`leancil --help`, `leancil -h` and `leancil` with no arguments print the usage of every command. A
failing command exits with `1` and prints on standard error a summary line starting `Invalid:` or
`Error:`, a `Stage:` line naming the failed step and a `Next:` line with the fix to try. `check`,
`verify` and `audit-library` start the summary with `Invalid:`, as does each failed request of
`verify-batch` and `gates`. Every other failure starts it with `Error:`. An unknown option is
an error, as is repeating an option that takes one value.

## Build

`dotnet build Extractor -c Release` produces `Extractor/bin/leancil.exe` on Windows (`leancil` on
other platforms). The managed assembly and package are named `Nethermind.LeanCIL`. To install the
tool globally, see [getting started](GETTING-STARTED.md).

## Version

`leancil --version` prints the tool version (the installed package version, such as
`0.1.0-dev.<stamp>` for a development pack), the LeanCIL commit and Lean toolchain of its
framework, and the `[[require]]` block that pins the matching framework in a [consumer
package](CONSUMERS.md#consumer-proof-packages). A tool built outside a git checkout reports the
revision as unknown.

## Discover and select methods

`leancil list assembly.dll` prints the canonical signature of every method, including overloads
and non-public methods, for copying into `extract`. It reads metadata without executing the
assembly. A listed method is not necessarily supported: `extract` validates its signature, CIL and
reachable dependencies.

Method selectors accept C# type aliases, an optional return type, and an unqualified declaring
type when the result is unique. The four selectors below select the same method:

```text
System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)
ulong Examples.Arithmetic::Add(ulong,ulong)
Examples.Arithmetic::Add(ulong,ulong)
Arithmetic::Add(ulong,ulong)
```

- The parameter list is required. Matching is case-sensitive, and an explicit return type must
  match.
- Use `ulong&` for a by-reference parameter.
- An `in` parameter of a virtual, abstract or interface member, including an explicit interface
  implementation, is spelled `ulong& modreq(System.Runtime.InteropServices.InAttribute)`, as
  `list` prints it. The modifier is part of the selector and the recorded signature, so it never
  matches the unmodified `ulong&` overload.
- An ambiguous selector fails with the full candidate signatures, ready to copy into the command.
- Artifacts record the resolved canonical signature, so equivalent selectors check the same
  artifact. Selection never relaxes supported-type or instruction validation.

`extract` infers the assembly identity from the DLL's metadata. Add `--assembly Examples` to
require a short name, or a full identity to constrain version, culture and public key token as
well; a mismatch is rejected. Artifacts record the full identity and assembly hash with or
without `--assembly`.

## Extract

```text
leancil extract assembly.dll '[return-type ]Type::Method(parameter-types)' output-directory
    [profile|@profile.json] [--assembly name-or-identity] [--type-argument Type]...
    [--assume-initialized Namespace.Type]... [--reference Lib.dll]...
    [--import Lib.leancil.contracts]... [--import-implementation Lib=path]...
    [--import-sha256 Lib=hex]... [--import-interface-sha256 Lib=hex]...
```

| Option | Meaning |
| --- | --- |
| `profile` or `@profile.json` | Execution profile, the fourth positional argument. The default is `scalar`; see [runtime profiles](RUNTIME-PROFILES.md#profile-selection). |
| `--assembly` | Required assembly short name or full identity; see [above](#discover-and-select-methods). |
| `--type-argument` | A closed type argument of a generic entry, repeated in order; see [referenced assemblies](#extract-from-referenced-assemblies) and [typed imports](TYPED-IMPORTS.md). |
| `--assume-initialized` | A type the caller guarantees completed initialization successfully before invocation; see [initialization assumptions](#initialization-assumptions). |
| `--reference` | A referenced assembly whose bodies are extracted too; see [referenced assemblies](#extract-from-referenced-assemblies). |
| `--import` and `--import-*` | Contract imports; see [contract interfaces](CONTRACT-INTERFACES.md). |

Build the example assembly and extract a method from it:

```sh run
dotnet build Examples/Assembly -c Release
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::Add(ulong,ulong)" artifacts/Add
```

From the repository root, `extract` prints:

```text stdout
Extracted 1 reachable method into artifacts/Add/Extracted.lean
```

The output directory holds:

| File | Content |
| --- | --- |
| `Extracted.lean` | The program: here `arg 0`, `arg 1`, `add`, `ret`, with the exact method signature, metadata, profile and kernel-checked fetch equations. The entry is method zero; reachable managed callees follow in dependency order. |
| `identity.json` | The manifest: assembly path, identity and SHA-256, entry, profile, assumptions, references, imports and extractor hash. |
| `Symbols.lean` | PDB names and source locations, written only when the assembly has a matching portable PDB. |

`Extracted.lean` also holds raw metadata and an `Extracted.translation_valid` certificate.
Verification requires this certificate to have the exact validator type for the complete emitted
program and kernel-replays it separately from the user proof.
[Extraction evidence](SOUNDNESS-EVIDENCE.md#independently-checked-extraction-evidence) lists what
its validators recompute; raw metadata serialization and transformations outside those checks are
trusted. The per-site validators walk the raw code, reachability mask and emitted code in
lockstep, so a long branch excluded by the profile adds linear checking cost.

`check` and `verify` read the profile from the manifest. Capability prerequisites of a profile
are validated. Instructions unreachable under the fixed profile are emitted as explicit
unsupported placeholders, so artifacts of one profile are invalid for another.

### Initialization assumptions

Methods on types with static constructors are rejected by default; the diagnostic names the type
and the flag to pass. If the caller guarantees successful initialization before invocation, record
that precondition:

```sh
leancil extract assembly.dll 'Type::Method(ulong)' artifacts/Method --assume-initialized Namespace.Type
```

Repeat `--assume-initialized` for each required type, using its exact metadata name. An assumption
applies only to the named type in this assembly and does not propagate to helper types. It does
not execute or prove initialization, or admit calls to static constructors.

An assumption enables `ldsfld` of the type's static readonly struct fields whose value its static
constructor fixes (see [static readonly values](OPCODES.md#static-readonly-values)). Each such
field is recorded in `staticValues` and reported as a caller assumption that it keeps the value
its static constructor stored. A field whose value extraction cannot compute is also listed in
`opaqueStaticValues` and reported as `Unknown static value`; its loads read the caller's static
binding.

The generated Lean source and identity manifest retain the assumptions; `check` reuses them and
rejects conflicting explicit assumptions. Verification binds the manifest hash, prints the
initialization preconditions with the theorem and copies both lists into `verified.json`.

### Extract from referenced assemblies

By default a call into another assembly needs a [contract import](#verify-with-imported-contracts).
To extract the callee's body instead, pin its DLL with `--reference`, repeated per assembly:

```sh
leancil extract App.dll 'App.Application::Direct(ulong)' artifacts/Direct --reference Lib.dll
```

Referenced assemblies are trusted inputs like the selected one
([soundness](SOUNDNESS-EVIDENCE.md#pinned-referenced-assemblies)). Each is recorded in
`identity.json` by relative path, full identity, MVID and SHA-256. `Extracted.lean` names it by
identity only, as an `Extraction.AssemblyPin` attributed to every body it supplies. `check`
replays the recorded references and rejects a changed hash or identity. Assemblies resolve only
against this pinned set and the runtime's platform assemblies, so an unpinned reference, a name
pinned under another version, a duplicate identity or a framework DLL passed as a reference fails.
One assembly cannot be both a typed import and a reference.

A referenced assembly's static methods are admitted as direct `call` and `ldftn` targets, and its
structs and interfaces as layouts and [constrained dispatch](OPCODES.md#constrained-struct-calls),
including static flag getters that fold a branch. A struct of the selected assembly may implement
a referenced interface or rely on its interface-level bodies, and a closed generic struct of
either assembly may receive a static slot. Its generic methods, the static methods of its generic
classes and the methods of its closed generic structs are specialized from its own metadata, so
their bodies stay attributed to its pin. A closed generic struct such as `Lib.Pair<ulong>` is laid
out from the assembly that defines it, and its type arguments may be value types of the selected
assembly or of any pinned reference, in either direction. Reference-type arguments, reference
fields and layout cycles are rejected, as are static field loads, `calli` and types with static
constructors in a referenced assembly. A closed entry type argument may name one of its structs as
`Namespace.Type, Assembly`, by simple or full assembly name:

```sh
leancil extract App.dll 'App.Application::Size(ulong)' artifacts/Size --reference Lib.dll \
  --type-argument 'Lib.Cell, Lib'
```

A static method of a generic class can be the entry. `--type-argument` lists the method's own
type arguments first, then the declaring type's, outer type parameters before inner ones as
ECMA-335 numbers them; the selector names the open definition:

```sh
leancil extract App.dll 'App.Algo`1::Run(ulong)' artifacts/Run --type-argument App.Gas
```

Instance methods of generic classes are rejected as entries and as callees.

## Report extraction blockers

`leancil blockers` runs admission, the validation `extract` performs, over an explicit list of
method and profile pairs, and reports everything that blocks each one instead of stopping at the
first failure. It checks no proofs and keeps no extraction artifacts:

```sh
leancil blockers assembly.dll --manifest blockers-manifest.json [--output blockers.json] \
  [--assembly name-or-identity] [--reference Lib.dll]... [--import Lib.leancil.contracts]... \
  [--import-implementation Lib=path]... [--import-sha256 Lib=hex]... \
  [--import-interface-sha256 Lib=hex]...
```

The manifest lists the entries and the settings shared by all of them:

```json
{
  "initializedTypes": ["Namespace.Type"],
  "references": ["Lib.dll"],
  "imports": ["Other.leancil.contracts"],
  "importSha256": { "Other": "implementation sha256" },
  "importInterfaceSha256": { "Other": "interface digest" },
  "entries": [
    { "signature": "Type::Method(ulong)", "profile": "scalar" },
    { "signature": "Type::Method(ulong)", "profile": "@profiles/x64-v3.json" },
    { "signature": "Type::Size()", "profile": "scalar", "typeArguments": ["Namespace.Pair"] }
  ]
}
```

| Manifest key | Meaning |
| --- | --- |
| `entries[].signature` | A method selector, as for `extract`. |
| `entries[].profile` | A profile name or `@file`, resolved against the manifest's directory. |
| `entries[].typeArguments` | An optional key that applies `--type-argument` to that entry. |
| `initializedTypes` | Applies `--assume-initialized` to every entry. |
| `references` | Pins referenced assemblies for every entry, as `--reference` does; paths are relative to the manifest. |
| `imports`, `importImplementations`, `importSha256`, `importInterfaceSha256` | Contract imports for every entry, as the `--import`, `--import-implementation`, `--import-sha256` and `--import-interface-sha256` options of `extract`; paths are relative to the manifest. |

A sidecar beside the assembly is discovered as `extract` discovers it. `--assembly` has its
`extract` meaning. Any other manifest key is rejected.

The report goes to `--output`, by default `blockers.json` next to the manifest, and a short
summary goes to standard output. The command exits with `0` whenever the report is written,
whatever the entries' status. Each entry has one status:

| Status | Meaning |
| --- | --- |
| `admitted` | `extract` succeeds: an entry with no blockers is extracted into a scratch directory to confirm it. |
| `blocked` | At least one blocker is listed. An entry the selector resolves but `extract` rejects by its shape, such as an `init` setter or a member of an open generic type, is `blocked`, and its definition is analysed as an entry. |
| `notChecked` | Nothing was analysed, for the reason given: a selector that matches no method or several, a malformed type argument, an unknown profile, or an assembly, import or assumption that fails before any method is checked. |

Each blocker is one unsupported construct (instruction, call, type, layout, method metadata or
static constructor). It lists every site, with method, IL offset, instruction and the PDB source
location when one is present, and every affected entry with the call chains from it to those
sites.

- A condition found by two checks, such as an entry's modifier and the type that carries it, is
  reported once, by the more specific check.
- A rejected signature, receiver, static constructor or entry shape does not stop the analysis:
  the body and callees behind it are checked and their blockers reported. Only a method without
  IL to analyse, or a body whose control flow cannot be analysed, ends its branch, and that
  blocker's message names what was not analysed behind it.
- Only code reachable under the entry's profile is checked, so a branch excluded by a constant
  `IsSupported` is never reported.
- An admitted entry is only extractable; verifying it needs a proof.

## Check

Check that the generated files still match the assembly and extraction settings:

```sh run
leancil check artifacts/Add
```

`check` prints:

```text stdout
Valid: extraction artifacts match the assembly and recorded settings.
  Assembly: Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null
  DLL: Examples/Assembly/bin/Examples.dll
  Entry: System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)
  Profile: scalar (scalar, 64-bit, little-endian)
  Reachable methods: 1
  CIL: artifacts/Add/Extracted.lean
  Manifest: artifacts/Add/identity.json
  Matched: assembly identity and SHA-256, extractor SHA-256, configuration, metadata and regenerated CIL.
  Symbols: matched the PDB
```

Paths under the current directory are displayed relative to it; paths outside it remain absolute.

`check` reads the assembly path, method and profile from the manifest, regenerates the extraction
in memory, and compares it with the saved files without overwriting them. It runs no Lean.

| Option | Meaning |
| --- | --- |
| `--assembly-path path/to/Examples.dll` | Use a DLL that moved. Assembly paths are stored relative to the artifact directory; the DLL's identity and content must match the manifest. |
| `--assembly name-or-identity` | Require that assembly name or identity, as for `extract`. |
| `--import-implementation`, `--import-sha256`, `--import-interface-sha256` | Override a recorded import's path or pin; see [contract interfaces](CONTRACT-INTERFACES.md). |

`check` replays the recorded `--reference` assemblies and rejects that option. A changed assembly
or extractor, or a saved file that differs from the regenerated one, fails at the
`extraction integrity` stage; run `leancil extract` again. A manifest whose `schema` is not `3` is
rejected the same way.

## Start a proof

Write a starting proof of an extraction's entry method:

```sh run
leancil extract Examples/Assembly/bin/Examples.dll "Loops::Countdown(uint)" artifacts/Countdown
leancil new-proof artifacts/Countdown Proofs/Countdown.lean
```

`new-proof` prints on standard output:

```text stdout
Wrote Proofs/Countdown.lean: a starting proof of System.UInt32 Examples.Loops::Countdown(System.UInt32)
  Holes: 8 obligations, 0 paths not outlined (each `sorry`; verify rejects the file until none remain)
  Next: leancil verify artifacts/Countdown --proof Proofs/Countdown.lean --goals prints the goal at each hole; fill them, then verify without --goals
```

`new-proof` reads only the extraction directory and first runs the comparison of `leancil check`,
so a stale or edited extraction is refused at the `extraction integrity` stage. It never replaces
a file: when the proof path exists, it exits with `1` and writes nothing. The same extraction
always gives the same file, byte for byte. The file imports the extraction's keyed module,
`Extracted.KEY` (see [Editor workspace](#editor-workspace)), so it opens in the editor once
`leancil workspace` selects the method, and `verify` accepts that import for this extraction only.

The file states `ExampleProof.correctness` as a `CIL.Safety.Ensures` theorem over the method's
parameters, named as in the PDB, and checks it with `#print axioms correctness`. A `bool`
parameter is a `Bool`, a narrow integer a `BitVec` of its width, and a `bool` result the `Bool`
its returned word encodes. Every place the author must decide something is a `sorry`, each with a
one-line comment saying which obligation it is. Wherever the outline splits a proof on a test,
each side that returns steps to its own return and leaves its own postcondition, commented with
the side or values it is for. In the `Holds` theorem of a callee that tests its arguments, each
returning side is stepped and leaves what `post` states of the result, and each throwing side is
closed from `pre` by `cil_loop_obligation`. The outline handles these shapes:


- `Precondition` and `Postcondition` are definitions to replace with the specification. The
  theorem assumes the precondition and promises the postcondition of the returned value. For a
  method that takes references, spans or arrays, or that calls a helper from a frame of integer
  locals, the postcondition also covers the caller's memory before and after. Each definition the
  author fills (`Precondition`, `Postcondition`, `invariant`, `measure`, a `footprint` hole and a
  helper's contract stub outside a loop) is under `set_option linter.unusedVariables false in`,
  since a specification rarely names every binder the theorem fixes. The header names each C#
  parameter bound under another name, such as `values` as `values1`.
- A method without a loop is stepped by `cil_checked_steps` when its body is arithmetic on 32- and
  64-bit arguments or a total bit count (`Log2`, `PopCount`, `LeadingZeroCount`,
  `TrailingZeroCount`), leaving only the postcondition. A signed or unsigned checked `+`, `-` or
  `*` is split with `by_cases fitsN` on whether its integer result fits. The fitting side steps
  with `checkedValues_add_unsigned_i32`, `checkedValues_add_signed_i32` or their siblings; the
  overflowing side throws and is closed from the precondition by `cil_loop_obligation`. A
  conditional branch on words the body computes from its arguments, signed or unsigned, is split
  with `by_cases branchN` on its condition; a body splits into at most eight returns. A literal in
  a split's condition is in the form default `simp` leaves it, such as `count = 0#32` or, in a
  signed comparison, `value.toInt < (-1)`, so the split's fact rewrites a simplified goal without
  restating it. A body that also takes up to three `bool` arguments and tests nothing else is
  split with `cases` on each.
- An `int[]`, `uint[]`, `long[]` or `ulong[]` parameter, alone or beside a class instance, is an
  `ArrayView` with a list of its elements. The theorem assumes the view validates, has its element
  type and holds those elements in its storage span, `SpanContents initial values.storage`. A
  method returning `values[index]` for an `int` argument `index`, read by `ldelem` or through a
  static helper whose body only returns `ref values[index]`, is split with `by_cases valuesBound`
  on whether the index is below the number of elements; a null array has none, so the bound alone
  excludes it. The in-bound side steps through `SpanContents.array_load`, and the helper's call
  through a contract proved from its body, leaving the postcondition. An index outside throws, a
  hole the precondition closes. Straight-line bodies over objects can also store the array in a
  field and read an element (see the word-array item below); unsupported combinations leave a
  `not outlined:` hole.
- A loop over an array indexes it with an `int` local tested against `values.Length`, which throws
  on a null array. `Precondition` is therefore generated as `values.reference ≠ .null ∧ sorry`
  under a comment saying why, leaving the `sorry` for what else callers guarantee. The proof
  destructures the array into `valuesBase` and `valuesLength` before the loop and closes the null
  case from `Precondition`; with the conjunct removed that case fails with
  `Precondition must exclude null`. The cutpoint takes `valuesLength`, which a valid array keeps
  below `2 ^ 31` (`SpanView.length_bounded` of its storage span). A read of `values[index]` steps
  through `array_load` of the storage span's contents and loads `valuesElements[index.toNat]`. For
  an array the loop stores into, the theorem gives authority over its storage span, `footprint` is
  that span's, and a store of `values[index]` steps through `arrayElement_of_access`. Each access
  leaves its index bound, and a store its write authority and footprint entry, to
  `cil_loop_obligation` from the author's definitions. A method storing into one of several arrays
  is refused.
- A method with a loop gets its loop state, a cutpoint derived from its control flow, and
  `invariant` and `measure` definitions to replace. A method that takes a reference also gets a
  `footprint` to replace: the caller memory the loop may write, which the loop state carries. The
  proof applies `invoke_loop_satisfies`, steps the entry to the first loop head, splits the
  iteration where the body branches, and leaves the obligations the loop tactics tag: `invariant`
  and `measure` where an iteration continues, `postcondition` where it returns, and `precondition`
  at a call. A comment at the iteration names what its holes follow from: `holds`, the invariant
  at the loop head, `assumed`, the precondition, and the fact of each test taken, such as `guard`.
- An object local of a loop, such as a list walk's `node`, is a `ManagedReference` of the loop
  state, and the cutpoint's frame names its slot from the state. A null test of it splits the
  proof with `cases node`, leaving a hole for the liveness of the instance it holds. An identity
  test against another object splits the proof with `by_cases branch1 : ...`. A load of a
  reference field into it is a `not outlined:` hole.
- A loop's test of a 1- or 2-byte struct field splits on the word its load zero-extends, such as
  `(scanStopped.setWidth 8).setWidth 32 = 0`.
- A 4- or 8-byte store in a loop through `Unsafe.Add` of a reference argument by an `int` index,
  before any other store of the iteration, is stepped from three side conditions: write authority
  over that element at the iteration's memory, the index below `2 ^ 31` and the element within
  `footprint`. `cil_loop_obligation` proves each from the invariant, precondition and footprint
  the author writes, by `omega` over their conjuncts or from a `Filled` or `Writable` fact
  covering the element. Each is a hole while any of those definitions is `sorry`, and an error at
  the write once they are written and do not imply it.
- A loop over a `Span<T>` of 32- or 64-bit integers that stores `span[0]` and continues with
  `span.Slice(1)` keeps the span as a `WritableSuffix`. Its `WritableSpan` holds the view's checks
  and `SpanWritable` authority in the caller's memory and no fact about its contents, so the
  caller need not have initialized it. The loop splits on the remaining length with `cases`. The
  store, before any other store of the iteration, steps through `frame.write_span_head`, which
  names the element's address, and `Slice(1)` through `WritableSpan.tail`. The span's bytes are
  its `footprint`, and the theorem assumes `SpanWritable` over them. A read of the written span
  is a `not outlined:` hole.
- Passing that span to a static `(Span<T> target, T value)` callee whose body only stores `value`
  into `target[0]` gives the callee a proved contract over the span's bytes. The outline lends it
  the span through `WritableSpan.lend` and names `WritableSpan.covered` and `below` for the call's
  footprint side conditions; the invariant then extends the prefix with `Filled.extend`. Such a
  callee outlined on its own is stepped through `WritableSpan.write_head`; an empty span throws
  there, a hole the precondition closes. Any other write to a span outside a loop is refused.
- The span such a loop reads or fills may be a local, `ReadOnlySpan<T> rest = values` or
  `Span<T> rest = values`, assigned once before the loop from a span argument or from the whole of
  an array argument. The local's suffix is the loop state, and the cutpoint's frame names its slot
  from the state, since the entered frame holds the null span there. A copied span argument is
  checked as when the loop slices the argument itself. An array spanned this way is not
  destructured: the loop starts from `values.span false` or `values.span true`, the span
  `step_arraySpan_whole` pushes, checked by `CheckedSpan.of_array` for a read and by
  `WritableSpan.of_array` for a fill, whose authority and `footprint` are the array's storage
  span. A null array converts to an empty span, so the precondition need not exclude it. A local
  assigned anything else, or an array also read other than through the local, is refused.
- Loops in sequence are bound in pc order (`loop`, `loop2`, ...), each with its own cutpoint,
  `invariant` and `measure` (`header2`, `invariant2`, `measure2`, ...). The path leaving one loop
  for the next loop's test enters that loop through `loop_terminates_then`, leaving its invariant
  at its first head, and that loop's iteration follows. A loop nested in another is refused.
- A call in the loop gets a `MethodContract` for the callee, with `pre` and `post` to replace, and
  a `Holds` theorem that steps the callee when it is arithmetic on its arguments. A callee of
  words that tests them and returns or throws on each side is split with `by_cases` on each test.
  A call whose callee returns a value is crossed with `cil_loop_call keeping`, so the next loop
  state names its result `output` whatever `post` states. A callee that only stores a word
  argument through a reference argument gets the contract its body meets, proved: it requires
  write authority over that word before the call and states the word's contents after it. When
  the loop passes it `Unsafe.Add` of a reference argument by an `int` index, the element is named
  with the three side conditions of a store, its authority stated at the caller's memory, and
  they close the call's precondition. A callee over objects whose body a straight-line outline
  steps (see below) gets the contract read from its body instead, proved, leaving only its
  precondition at each call.
- A struct instance method binds `this`, a reference to the caller's struct, as a `Reference`
  named for the struct, such as `counter`. A straight-line body over its scalar fields and word
  arguments is stepped. Each field it reads first gets a binder for its value on entry, such as
  `counterValue`, with `Contents` of the field's address (`counter`, or `counter.element 1 8` at
  offset 8) in the statement. Each written field gets `Writable` authority, and the result
  promises `Confined` to those fields. Fields of 1, 2, 4 and 8 bytes use their stored width,
  including signed extension on loads and truncation on stores. Repeated stores, and reads between
  stores, are stepped. The postcondition receives the final field contents. Overlapping fields are
  not outlined.
- A struct receiver loop over 64-bit fields with one conditional back edge and no local homes
  gets a `State` recording field values, contents, write authority and confinement. Its outline
  steps each path and leaves the invariant, natural-number measure and postcondition to the author.
  Scalar arguments and results must be 64-bit; void returns are also supported. Narrow fields and
  frame-owned locals in receiver loops are refused.
- A struct value argument binds a fixed-size byte vector, including padding, and is passed as an
  aggregate scalar. Straight-line outlines step parameter homes and nested aggregate locals,
  including initialization, field addresses, loads and stores. Aggregate parameter homes and
  nested aggregate locals inside loops are not outlined.
- An instance of an admitted class is a `Reference`. An instance method binds `this` under its
  class's name in lower case, such as `account`, or as `receiver` for a compiler-generated class.
  A parameter named like a hypothesis or memory the proof introduces, such as `held` or `stored1`,
  is bound as `argument` and its position instead. The statement assumes
  `LiveObject initial account`, `Readable` of each field of each object that the body or a callee
  it steps reads, and `Owned` of each they write, using the field views the extraction emits in
  `Extracted.Classes` (see [Frame class instances](PROOFS-CONTRACTS.md#frame-class-instances)). An
  object the body loads from a reference field is a further binder, such as `nodeNextTarget`, with
  the premise that the field holds it. A method that writes a field promises
  `Confined footprint initial final`, with `footprint` listing the written fields. The body is
  stepped through its field loads, its stores, locals and null tests of objects, and leaves the
  postcondition with `held1`, `held2`, ... the stored fields' `Holds` facts. A stepping call does
  not list that an argument object or array of references forms, where its fields lie or what an
  unsigned scalar field of it loads, which the tactic reads from the statement's hypotheses. A
  stepping call does list them for an object a field holds, such as `nodeNextTarget`, which the
  goal names only once the field's load has stepped. A test of words it names, such as a field
  value against an argument, splits the proof with `by_cases branch1 : ...`.
- A field holding a class outside the model, such as `string`, loads as the reference it holds,
  `Tagged.Tag.of initial item`, never read through. The statement adds `Tagged.Tag.Forms initial
  item`, that the reference forms, and the body may store it into such a field, compare it and test
  it for null, which splits the proof like a test of words. Any reference field may also be set to
  null, through `Owned.store_formed`. A `bool` result leaves
  `case result` for the `Bool` the returned word encodes and `case encoded` for the encoding.
- An array argument of class references, such as `nodes : Node[]`, binds `nodesElement`, the
  element class its allocation records, which covariance may make a class derived from the
  static one, and `nodesLength`. The statement assumes `ReferenceArray.Readable` of each element
  the body loads and `ReferenceArray.Owned` of each it stores, numbered `nodesSlot1`, ..., or
  `ReferenceArray.Live` when it only reads the length. A loaded element is the reference
  `ReferenceArray.of initial nodes index.toNat`, with the premise `ReferenceArray.Forms` that it
  forms, and a stored object adds the premise that it passes the covariance check,
  `storableIn initial nodesElement (.address node) = .ok ()`, which the caller discharges from the
  object's class. The footprint lists `ReferenceArray.entry` of each stored element. Each element
  fact is carried across the stores before it as `ReferenceArray.Holds` or `ReferenceArray.Reads`
  of what the element holds, so a load after a store reads back the stored reference, and field
  facts cross element stores, since no array has fields. An access after a store into another
  array, or into the same array at an index that is not a different literal, is a
  `not outlined:` hole, since the two elements may be one element. A reference outside the model
  used after a call that writes is also a `not outlined:` hole. A `newarr` of class references of a
  literal length, the body's first write, adds the premise
  `CIL.objectFieldSlot * 2 ≤ initial.heapBudget` for its slots and a `fresh1Element` def naming its
  element class; its elements start as owned nulls, the array is `fresh1` with `fresh1Identity`
  dating it after every caller allocation, and the footprint forgets its elements through
  `Confined.forget_fresh`. An index into it that is not a literal below its length is a
  `not outlined:` hole, as is a method with a loop.
- A word array keeps its `ArrayView` and element bindings beside a class instance argument or
  receiver, so indexed element reads and loops use the outline of a standalone word array. Storing
  the array into a class field also requires its `WholeArray` fact and its storage's origin to
  match the array reference. Field-slot writes preserve the array's element contents, so an
  element can be read after the field store. A straight-line element read after a scalar-field
  write or a supported helper call requires separation between the array storage and each written
  field; array validity alone does not establish unchanged contents. Allocation preserves existing
  contents without a separation premise for the fresh storage. Calls that change the array's
  elements need a contract describing those changes and are outside this outline pattern. An index
  expressed in the caller's initial bindings has an entry bound premise. An index depending on
  memory after a write leaves a bound obligation at the read, where the helper and field-store
  postconditions are available.
- Straight-line class methods and supported helpers can use initialized 32- and 64-bit integer
  locals. The outline carries their private storage through scalar field writes and confined
  calls, preserves saved values and expires the homes on return. A helper that writes no caller
  fields preserves caller memory; allocating its local homes does not preserve the entire memory
  state by equality. A test of named words in such a frame splits the proof as it does without
  locals, each side going on from the homes and saved values of the path so far. Frames mixing
  these integers with other local kinds, narrow or native-sized local homes, uninitialized homes,
  escaped local addresses and reference-field or reference-array effects are unsupported. Helper
  summaries allow at most one field store and no nested calls.
- An array argument of structs or vectors binds `valuesLength` and is passed as
  `.array ⟨.address values, valuesLength, element⟩`, with the premise
  `WholeArray initial element values valuesLength`. The element is the `elementType` of a field
  that holds such arrays, such as `Tiles.Pairs.elementType`, or a literal such as `.signed32`; a
  struct or vector element no field names is a reducible `valuesElement` def. A load of a field
  holding a value array, before any write, binds the array and its length, such as
  `samplesValuesArray` and `samplesValuesLength`, with premises that the field holds it and that
  it is whole. A store into such a field of an argument or loaded array steps through
  `Owned.store_whole`, and each `ldlen`, local, call argument and return of an array is stepped
  with its `WholeArray` fact. A value-array result is an `ArrayView`. A load of the field after a
  write, a store of a null array into it, and a call to a method that takes a value array or loads
  a value-array field are `not outlined:` holes, and an unstepped body over a value array leaves
  its `footprint` to the author. A struct instance method or a method with a loop that takes a
  value array, or a loop that returns one, is refused.
- A call in a body over objects to a method that loads its fields, stores at most one word field of
  an object argument and returns a value it names gets a generated `MethodContract` read from that
  body, with a `Holds` theorem proved by the same stepping and closed at its return by
  `MethodContract.Holds.returns framed post`; `cil_contract_steps` composes the call
  through it, and the callee's store counts as one of the caller's. A callee that loads an object
  from a reference field and stores nothing gets a `pre` asking that some object, such as
  `nodeNextTarget`, is held there with the facts it reads, and a `post` stating the result of
  whichever object the field holds; the caller names that object by its own fact that the field
  holds it, from a store just before the call or a target of its statement. A loop
  carries the object facts across its iterations, and a `callvirt` in it gets a contract like any
  other call. A loop's statement assumes the same per-object facts, read from its body and callees
  in order; when that reading stops, it assumes a fact of every named field of each object, `Owned`
  where the method or a callee stores the field.
- A call in a straight-line body to a static helper over words gets a contract stub, since what
  the caller should learn of the result is the author's to state: in a body over objects, a helper
  that tests its arguments or throws, and in a body over words alone, one that only computes as
  well. The helper has 32- or 64-bit integer parameters and result and no locals, and its body
  only computes, tests and throws. The stub is a `MethodContract` whose `pre` is `sorry` and whose
  `post` is `final = initial ∧ sorry`, the helper storing nothing, and a `Holds` theorem against
  the helper's method index in `Extracted.program`, split with `by_cases` on each test. When
  `cil_loop_obligation` fails on a throwing side, its error says that the path is reached unless
  one of the definitions it unfolds rules it out. At the call the caller states `permitted1`,
  the helper's `pre` of the values passed, as a hole to prove from `assumed`. `cil_contract_steps`
  composes the call through the contract `with called1 output1 call1`, naming the memory after it,
  the result and the call's `CallResult`. The proof reads what `post` states of the result as
  `post1` from `call1.post`, which the postcondition hole's comment cites. A wrong `pre` or `post`
  fails in the `Holds` theorem or at the caller; neither error is silent.
- A helper that takes an object or keeps integer locals, tests words it names from its arguments,
  fields and locals, and stores nothing gets the same kind of contract. Its `pre` states the facts
  its body needs before the `sorry`: of an object, such as
  `LiveObject memory gauge ∧ Gauge.Limit.Readable memory gauge`, or `memory.WellFormed` for a
  frame of locals. Its `post` is `final = initial ∧ sorry`, or `sorry` alone when the helper keeps
  locals, whose homes are allocated in the memory. Its `Holds` theorem closes each returning side
  with `MethodContract.Holds.returns`. At the call, `permitted1` gives those facts from the
  caller's own and leaves the rest of `pre` as the hole. The helper's `post` reads fields in the
  memory at the call, which a caller with locals names in `initial` by its field equations, such
  as `gaugeLimitEqual1`.
- A caller that keeps 32- or 64-bit integer locals composes these calls inside its frame: a
  result stored into a local is read back as the word the helper returned, and a test after it
  splits the proof. A body over words alone that keeps such locals beside a helper call, or calls
  a helper that keeps its own, is stated of any well-formed `initial` memory rather than the empty
  one, since the homes are allocated in it; its `Precondition` takes `initial` and its
  `Postcondition` both memories. A helper over words that keeps its own locals and only computes
  gets the contract read from its body, which names its result, instead of a stub.
- Any other callee leaves a `not outlined:` hole, such as a helper that calls another method or
  stores a field beside a test: the hole names the callee's method index and the `MethodContract`
  to write and prove with `Holds Extracted.program` at that index.

Where the outline cannot step a path, it leaves a hole whose comment starts with `not outlined:`,
names what it met and what that step needs, and gives the source line to continue from. The
`Holes` line counts these apart from the obligations. The unedited file elaborates with only
warnings that a declaration uses `sorry`, and `leancil verify` rejects it at the theorem audit for
`sorryAx` until every hole is filled.

`new-proof` writes this outline for the countdown:

```lean extracted
import Extracted.Loops_Countdown_1347de14
import CIL.Verification
import CIL.StructuralLabels
import CIL.Safety.LoopScaffold

/-! A starting proof of `Countdown`, generated by `leancil new-proof` from its extraction. Each
    `sorry` is a hole: `leancil verify --goals` prints the goal at each, and `leancil verify`
    rejects the file until none remains. A hole commented `not outlined:` marks a path the outline
    could not step. The tactics leave obligations tagged `invariant`, `measure`, `postcondition` and
    `precondition` (at a call), which the holes select with `case`. -/

open CIL.Safety
open CIL (W32 W64)
namespace ExampleProof

set_option linter.unusedVariables false in
/-- Replace with what callers must guarantee about the arguments, or `True`. -/
def Precondition (value : W32) : Prop := sorry

set_option linter.unusedVariables false in
/-- Replace with what `Countdown` guarantees about its result. -/
def Postcondition (value result : W32) : Prop := sorry

bind_entry entry (value : W32) := Extracted.method0
  with [.scalar (.i32 value)] from Memory.empty
  allocating Memory.empty_wellFormed
bind_loop loop := Extracted.method0

/-- The loop's locals at its head: `remaining`. -/
abbrev State (home0 : Reference) :=
  FrameState [] Memory.empty [.word32] W32
    (fun _ => [.bytes .word32 home0]) fun values => [some (.i32 values)]

-- The cutpoint is the loop's back-edge test at Loops.cs:38.
bind_cutpoint header (home0 : Reference) (state : State home0) :=
  Extracted.method0 at loop.latch matching (· matches .brnonzero _)
  with entry.frame home0, [.scalar (.i32 state.values)], state.memory

set_option linter.unusedVariables false in
/-- Replace with what holds at every loop head. -/
def invariant (value : W32) {home0 : Reference} (state : State home0) : Prop := sorry

set_option linter.unusedVariables false in
/-- Replace with a quantity each iteration decreases. -/
def measure (value : W32) {home0 : Reference} (state : State home0) : Nat := sorry

theorem correctness (value : W32) : Ensures Extracted.program 0
    (fun args initial => args = [.scalar (.i32 value)] ∧ initial = Memory.empty ∧
      Precondition value)
    (fun _ _ _ results => ∃ result : W32, results = [.scalar (.i32 result)] ∧
      Postcondition value result) := by
  rintro args initial ⟨rfl, rfl, assumed⟩
  obtain ⟨home0, entered, enter⟩ := entry.checked value
  have setup := enter.setup
  have entryFrame := enter.frame
  refine invoke_loop_satisfies Extracted.lookup0 rfl setup (header home0) (invariant value)
      (measure value) (fun start => ?_) ?_
  · have entryFrame := entryFrame []
    cil_loop_recurse start value
    case invariant => sorry -- invariant at the first loop head
  rintro ⟨remaining, current, frame⟩ holds recurse
  -- `holds` is the invariant at this loop head and `assumed` the Precondition; each side below
  -- names the test it took, such as `guard`.
  by_cases guard : remaining = 0#32
  · -- leaves the loop at Loops.cs:40
    cil_loop_finish [guard]
    case postcondition =>
      refine ⟨_, rfl, ?_⟩
      sorry -- Postcondition at the return at Loops.cs:40
  · -- another iteration
    cil_loop_recurse recurse (remaining - 1) [guard]
    case invariant => sorry -- invariant again at the loop head
    case measure => sorry -- measure decreases over this iteration

#print axioms correctness
end ExampleProof
```

It verifies once the precondition is `True`, the postcondition `result = 0`, the invariant `True`,
the measure `state.values.toNat`, and each tagged case is proved, the measure case by showing that
`remaining - 1` is smaller than a nonzero `remaining`.

A shape the outline cannot state is refused at the `proof outline` stage, exiting with `1` and
writing nothing; the message names the parameter, local, loop or test and what it lacks.

## Verify

```text
leancil verify output-directory [--proof proof.lean] [--theorem name] [--proof-root package]
    [--fresh] [--rebuild-library] [--goals] [--trace] [--format text|json]
    [--force-full-verify] [--full-artifact Lib=directory]...
```

`verify` establishes one named theorem about an extraction. In order, it:

1. checks the extraction artifacts as `check` does;
2. opens the certified framework library from its cache, or builds it on a cache miss (see
   [stage progress](#stage-progress));
3. checks the selected proof with Lean and kernel-replays it;
4. audits the theorem's transitive axioms, permitting only `propext`, `Quot.sound` and
   `Classical.choice`;
5. checks artifact and source identity again and writes `verified.json` in the output directory.

Its guarantee is exactly the theorem's statement, including its preconditions and quantifiers.
Standard output carries only the report; standard error carries stage progress and diagnostics.
Lean and Lake must be installed.

| Option | Meaning |
| --- | --- |
| `--proof` | The proof file. The default is the saved setting, else `Proof.lean` in the output directory. |
| `--theorem` | The theorem to check. The default is the saved setting, else `ExampleProof.correctness`. |
| `--proof-root` | The Lake package holding the proof's own modules; see [consumer proof packages](CONSUMERS.md#consumer-proof-packages). |
| `--fresh` | Bypass proof and support reuse; the source-bound library cache is kept. |
| `--rebuild-library` | Rebuild the library as well. CI bypasses the local library cache automatically. |
| `--goals` | Print the goal at each hole; see [goals of an unfinished proof](#goals-of-an-unfinished-proof). |
| `--trace` | Log each step the proof takes; see [trace the proof's steps](#trace-the-proofs-steps). |
| `--format json` | Print one JSON report; see [machine-readable verify output](#machine-readable-verify-output). |
| `--force-full-verify`, `--full-artifact` | Re-check imported libraries; see [verify with imported contracts](#verify-with-imported-contracts). `--full-artifact` requires `--force-full-verify`. |

The tool ships the framework's `CIL` sources only. A proof imports `Extracted` (or a method's
`Extracted.KEY`, see [Editor workspace](#editor-workspace)) and `CIL.*`;
`CIL.Safety.Memory.empty` is the caller memory with no allocations. LeanCIL's own example and
test modules are not shipped, and a proof importing one is rejected as `invalid-request`.

### Stage progress

Each Lean or Lake process `verify` and `workspace` start is a stage, and stderr reports it:

- On a terminal, a stage prints a `START` line, a `PROGRESS` line every 10 seconds, and an `END`
  line with the exit code and duration.
- When stderr is a file or a pipe, a stage shorter than 20 seconds prints nothing, so a warm run
  leaves stderr empty. A longer stage prints a `PROGRESS` line every 20 seconds and then its `END`
  line.

A `PROGRESS` line of a Lake build carries Lake's job count:

```text
PROGRESS Building fresh Lean verification library: 212 of 332 Lake jobs (240s)
END Building fresh Lean verification library (exit 0, 501.7s)
```

### Library cache

The certified library is the compiled framework. It holds every `CIL` module, and each module is
kernel-replayed. The library
certifies every proof and proof dependency for one framework version, and building it takes
several minutes. It is cached in the directory `LEANCIL_CACHE_DIR` names, by default
`<local application data>/LeanCIL/libraries`, under a key of the framework sources, toolchain
and platform. A cache miss first prints one line saying what is being built and kernel-replayed
and where later runs reuse it from.

With no whole library cached, `verify` of one proof without `--proof-root` first builds a closure
entry: the framework modules that the proof, the extraction, its symbols and the statement display
import, transitively, together with those of the audit executable.

- Every module of the entry is kernel-replayed. Its cache key and receipt name exactly that
  module list, and `verified.json` records that key as `libraryKey`, `closure` or
  `closure-cache` as `libraryBuild` and the list as `libraryModules`.
- The entry holds no other framework source, so a module outside it can be neither imported from
  it nor built into it. `verify` reads the import headers of the compiled proof and extraction
  and refuses a framework import the entry does not hold.
- After a verified result is reported, the same command builds, replays and caches the whole
  library, which stderr announces, reusing the entry's compiled modules where Lake's traces
  allow, and removes the entry once no process reads it. If that build fails, the verified
  result and its `verified.json` stand, and the command reports the failure and exits nonzero.
- A failed proof, or one with open goals under `--goals`, leaves the entry for the next run.
- One closure entry exists per library: a proof with other imports builds the whole library.
- `--proof-root`, batch, contract-import and `--force-full-verify` verification, `workspace`,
  `watch`, CI and `--rebuild-library` use the whole library only, and a package never requires a
  closure entry by path.

Verification sessions read a cache entry in place, as do packages that require it by path after
`workspace`, and Lake rebuilds a required module it finds out of date inside the entry. Each run
therefore hashes every file of the entry against the manifest its receipt binds, about half a
second for the whole library.

- An entry that does not match is named on stderr and replaced by a rebuilt library. On Windows
  the replacement fails while another process, such as an editor, holds the entry's files open.
- `verify` also compares the library's files, by name, length and write time, with those it had
  when it was opened, each time it snapshots the library's compiled modules after a build and
  once more before single-file and batch verification write their reports; a difference fails
  the run.
- A command that finds another building or opening the library waits for it and says so on
  stderr.

To use a prepared library instead of the cache, set `LEANCIL_CERTIFIED_LIBRARY` to its directory
and `LEANCIL_CERTIFIED_LIBRARY_SHA256` to the independently trusted SHA-256 of its
`cache-manifest.json`. The library must have the tool's library key and sources; a missing digest
or any mismatch fails the run. It is hashed against its manifest before a package requires it by
path, and `--rebuild-library` does not bypass it.

A release package can include a certified-library descriptor for the current runtime. On the first
cache miss, the tool downloads that exact release asset from the official LeanCIL GitHub
repository. The installed package pins its archive hash, producer manifest hash, runtime and
source/toolchain key. The download is validated and independently kernel-replayed before it
receives a local cache receipt. A missing descriptor, incompatible library or unavailable download
falls back to building the packaged sources. `--rebuild-library` bypasses this download and the
local library cache. Whoever packs a release produces the descriptor and its archive as
[release assets](performance/LibraryDistribution.md#release-assets) describes.

### Saved settings

The first invocation saves the proof and theorem selection in `verification.json` in the output
directory, apart from the success report:

```json
{
  "schema": 1,
  "proof": "../../Examples/Proofs/Add.lean",
  "theorem": "ExampleProof.correctness"
}
```

Proof paths in settings are relative to the artifact directory; command-line paths are relative to
the current directory. With `--proof-root`, the settings also record the package root as
`proofRoot`. The settings are kept after a failed proof and after re-extraction, and can be
versioned separately from reports. Explicit `--proof`, `--theorem` and `--proof-root` arguments
override the saved values.

Run verification using the saved settings:

```sh
leancil verify artifacts/Add
```

Every invocation validates the request's identity and required proof evidence. Authenticated
caches can reuse unchanged certified builds and an unchanged proof's result (see
[local support cache](CONSUMERS.md#local-support-cache)); source and hash checks, audits and
required kernel replay apply regardless. `--fresh`, `--rebuild-library`, `--force-full-verify` and
`LEANCIL_DISABLE_SUCCESS_CACHE=true` each bypass the reuse. A failed proof removes
the previous `verified.json`.

When the assembly or the extractor changed since extraction, `verify` first extracts again from
the settings `identity.json` records (assembly path, method, profile, assumptions, references and
imports) and prints `Re-extracted artifacts/Add: the assembly changed since extraction.` (on
stderr with `--format json`); a method that no longer exists then fails at extraction. An
artifact that changed while its assembly and extractor did not is rejected as tampered.
`verify-batch` does not extract again; it reports such an output as a stale input.

### Reading the report

A successful run prints, among the assumptions and paths:

```text
Verified: ExampleProof.addTwo_holds
  Assembly: Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null
  Subject: System.UInt32 Examples.Loops::AddTwo(System.UInt32) (method 1) via CIL.Safety.MethodContract.Holds
  Extraction entry: System.UInt32 Examples.Loops::TallyTwice(System.UInt32)
  ...
  Statement:
    ExampleProof.addTwo_holds : ExampleProof.addTwoContract.Holds Extracted.program ExampleProof.addTwo
  Lean messages (1):
    TallyTwice.lean:38:0: info: 'ExampleProof.addTwo_holds' depends on axioms: [propext, Quot.sound]
```

- `Subject:` names each method the statement's conclusion is about, and `Premise:` each method a
  hypothesis names. A method counts when a framework predicate with `program : CIL.Program` and
  `method : Nat` parameters (`CIL.Safety.invoke`, `MethodContract.Holds`, `LoopTerminates`, ...) is
  applied to `Extracted.program` and an index that reduces to a literal. An index the statement
  quantifies over is reported as not fixed, and predicates the proof defines are not looked into,
  so a line never names more than the statement does. `Extraction entry:` is the method the
  extraction started from; it says nothing about which method the theorem concerns.
- `Statement:` is printed in Lean notation from the audited proof module. Only the notation of
  the modules the proof imports applies, including consumer modules under `--proof-root`; the
  proof's own declarations are loaded without their extensions, so notation a proof defines cannot
  change the text. `verified.json` keeps the auditor's text in `theoremAudit`, which is printed
  instead, with `Subject: not identified`, if Lean cannot print the statement.
- `Specification:` follows the statement when it names definitions of the proof file, such as a
  `Precondition` and `Postcondition`: each is printed as `def name binders : type := body` from
  its elaborated value, in the statement's notation, before the definitions its own body names.
  `verified.json` records the same list as `specification`, each entry with its `name` and `text`,
  so changing a definition changes the report and the certificate. A definition that matches on
  its arguments or recurses is printed as Lean elaborates it, in terms of the auxiliary
  definitions it compiles to, and the field accessors of a structure the proof declares are not
  listed. Definitions of modules the proof imports are named in the statement and not printed.
- `Lean messages` lists the informational and warning messages of the proof file, such as
  `#check`, `#eval` and `#print axioms` output, at `file:line:column` in the proof. The first 60
  lines are shown; `proof-messages.txt` in the artifact directory holds the full text, and the
  report names it when lines are omitted. Messages are stored with the cached proof, so a run that
  reuses the proof shows them too. They are also printed on failure, after the diagnostic, so
  query commands work while a proof is unfinished, including under `--proof-root` when proof
  checking itself fails.

### Goals of an unfinished proof

`leancil verify ... --goals` prints the goal at each `sorry` written in the proof, the goal before
each tactic that raised an error and each goal a tactic block left unsolved, once each and in
source order. For the countdown outline of [start a proof](#start-a-proof):

```sh run fails
leancil verify artifacts/Countdown --proof Proofs/Countdown.lean --goals
```

Its diagnostic on standard error starts with:

```text stderr
Invalid: 8 goals remain in Proofs/Countdown.lean.
  Stage: open goals
  Next: Prove each goal listed below in place of its `sorry` or failing tactic, then rerun.
  Goals (8):
    Proofs/Countdown.lean:17:41: sorry
      value : W32
      ⊢ Prop
    Proofs/Countdown.lean:20:49: sorry
      value result : W32
      ⊢ Prop
```

Each entry is the place in the proof, then `sorry`, `failing tactic` or `unsolved`, then the
goal as Lean prints it there: its case tag, hypotheses and target, in the names the proof file
opens. A `sorry` written as a term, such as the body of a definition, is listed with the type it
stands for.

When any goal is open, the run exits with `1` at the `open goals` stage, with kind `unsolved-goal`
in [`failed.json`](#failure-reports), unless Lean reported an error, which fails at
`proof checking` as without the option. A verification without `--proof-root` stops right after
the proof check, skipping kernel replay and the audit, which could only refuse such a proof. Under
`--proof-root` the package's replay and audit run before the goals are read. With no goal open,
verification continues as it does without `--goals`. A `sorry` anywhere in the proof file is an
open goal, whichever theorem is selected. The proof's other messages are not listed with the
goals: the report gives their count and `proof-messages.txt`, which holds them. A failed
verification without `--goals` names the option on a `Goals:` line after `Next:`.

`--goals` checks the proof with `import CIL.Observe` added as for `--format json` and the Lean
option `cil.goals` set (see [PROOFS-STEPPING](PROOFS-STEPPING.md#observer-linter)), and
its result is cached apart from one without it. With `--format json` the goals are the report's
`goals`. [`leancil watch --goals`](CONSUMERS.md#watch) prints them after every save.

## Diagnostics

Method and call validation failures name the rejected item and the method containing it. A
rejected call reports its callee, caller, IL offset and declaring assembly scope. For example, a
reachable `Environment.ProcessorCount` call is outside the admitted runtime models. Exact closed
`typeof` comparisons are supported; a `GetTypeFromHandle` call outside those patterns is
unsupported. The diagnostic identifies metadata/CIL validation as the failing stage and links to
the supported subset.

When proof checking fails, the report leads with `Lean errors (N):`: each
`error:` diagnostic with its `file:line:col`, the module Lake was building and
its full message block, omitting axiom reports, traces and warnings. Each error
is printed once. A message longer than 40 lines or 400 columns, and every error
after the first 20, is shortened or left out of this summary and printed in full
under `Details:`; nothing else follows. When the output holds no Lean error,
such as a crashed tool, `Details:` holds the whole output instead. The
unmodified output is the `message` of [`failed.json`](#failure-reports) and,
when `LEANCIL_TRACE_DIRECTORY` is set, its transcripts.

Lean prints an internal error when its runtime or a tactic reads a part of a term or an array
that is absent, and elaboration then continues on a default value. The messages are
`PANIC at ...`, `INTERNAL PANIC: ...`, `Error: index out of bounds`,
`Stack overflow detected. Aborting.` and `LEAN ASSERTION VIOLATION`. One counts where a line of
the output of Lean, Lake or the audit executable, or a line of a message Lean logged, starts with
that exact text, which is how Lean's runtime writes it. The same words inside a sentence, a goal or a term are ordinary output,
and a failed tactic, an expected rejection and the goals of `--goals` are Lean errors with their
own kinds. Every command that runs
Lean, Lake or the audit executable fails when their output holds one, including when the
process exits with `0`, so `verify`, `verify-batch`, `gates`, `check`, `audit-library`,
`workspace` and the certified library build write no report or certificate from that run. The
report starts with `Lean or a LeanCIL tactic reported an internal error.` and leads with
`Internal errors (N):`. It lists each message once with the number of times it was printed, its
`file:line:col` when Lean logged it at a position, and the module Lake was building. The Lean
errors of the run follow. In a batch, an internal error printed while building one request's
proof module fails that request, whether or not the build as a whole succeeded, and one printed while building a module the requests share
fails each of them. The [failure report](#failure-reports) has kind `internal-error`.

Verification checks a copy of the proof, `Extracted.lean`, the PDB names and, under
`--proof-root`, the package's sources and its proof module. A location in a copy cites the file it
was copied from, at the same line and column, and Lake's module names the proof's own module, so
editors and terminals open the file the developer edits. Only a copy byte-identical to its
original when it was made is mapped; a generated module keeps the path Lean printed. Direct
verification checks the proof with `lean --json` and renders each message in Lean's
`file:line:col: severity:` form. Informational messages, which plain Lean output prints without a
position, appear there as `info:` entries, and the proof's own messages follow under
[`Lean messages`](#reading-the-report).

### Environment size on Windows

Lean on Windows builds the environment of each process it starts in a 32,767-byte buffer.
Lake starts Lean, including the editor's language server, with its own variables
(`LEAN_PATH`, `LEAN_SRC_PATH`, `PATH` and others) added to the environment it inherited,
and Lean drops every variable that no longer fits without an error, so `LEAN_PATH` can
be dropped and imports stop resolving. Each `name=value` entry counts its UTF-8 bytes plus a
terminator, and the block adds one more. Lean replaces an inherited variable only when the
name matches exactly, so Lake's `PATH` is added beside an inherited `Path` and the search
path counts twice.

Before running Lake, leancil computes what Lake will pass on: the environment it gives Lake, with
the changes elan's `lake` proxy makes, and the variables `lake env` prints (for `lake build`,
which passes Lean only `LEAN_PATH`, just that one). It fails when the result exceeds the limit,
naming the size, the limit and the largest variables. `leancil workspace` makes the same check for
`lake serve`, taking its own environment as the editor's, so the failure appears at setup. Lake
prints a variable it unsets as empty; counting it can overstate the size by a few bytes and
cannot understate it.

Lake adds a package's source directory to `LEAN_SRC_PATH` once for every `[[lean_lib]]` table in
the package's lakefile. After `leancil workspace`, a generated package and a package that pins
`leancil` resolve the framework to packages that declare only the framework and editor libraries,
which adds two directories. A LeanCIL checkout declares one library per test module, which adds
about ninety. A shorter checkout path and fewer `PATH` entries reduce the size. Setting
`LEANCIL_LEAN_ENVIRONMENT_LIMIT` to a byte count lowers the limit; on other systems, where Lean
has no such buffer, it enables the check, for example to measure headroom.

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
| `internal-error` | Lean, Lake or the audit executable printed an [internal error](#diagnostics), such as a panic in a tactic. The run is rejected whatever its exit code, and the report says nothing about whether the proof holds |
| `elaboration-error` | A Lean error other than an unsolved goal or a resource limit |
| `unsolved-goal` | A Lean `unsolved goals` error, or a `verify --goals` run that stopped at the goals it found open |
| `resource-limit` | Heartbeats (`(deterministic) timeout`, `(kernel) deterministic timeout`) or recursion depth; `resource` names which |
| `replay-or-audit-rejected` | Kernel replay or the theorem and axiom audit rejected the proof |
| `refutation` | The theorem verified and states `Not (contract.Holds ...)` for a `MethodContract` or `OutcomeContract` |
| `invalid-request` | The proof or theorem selection is invalid |
| `unclassified` | Anything else, such as a missing tool; read `message` |

The request's `kind`, `file`, `line` and `column` are those of the first diagnostic. `diagnostics`
lists each distinct internal error and then every Lean error of the request's own modules with its
message block, so an internal error gives the request its kind. Lines are 1-based and
columns 0-based, as Lean prints them. Locations in the session's copies cite their originals, as
in the text report. `message` is the original output, unmodified; `rerun` reruns just that
request. Classification uses only the stage, LeanCIL's own messages and Lean's error prefixes
above. Only a verified theorem whose elaborated statement is `Not` applied to a contract's `Holds`
is a refutation, as reported by the theorem audit; an unsolved goal is never a refutation. A
verified refutation keeps its `verified.json`, the certificate of the refutation, and also
writes `failed.json` with kind `refutation`, located at the theorem's name.

### Machine-readable verify output

`leancil verify ... --format json` prints one JSON report on stdout instead of the text report,
and nothing on stderr except [stage progress](#stage-progress); the exit code is the same as
without it. `--format text` is the default. The report has `schema` 1, `result` (`verified` or
`failed`), the `stage` that failed, the `theorem`, `method`, `proof` and `output`, and on success
the `axioms`, the `statement` and its `specification`, the definitions
[`Specification:`](#reading-the-report) prints, each with its `name` and `text`. The proof's own
Lean messages are in `messages`, and `rerun` repeats the run. With `--goals`, `goals` lists each
open goal with its `file`, `line`, `column`, `kind` (`sorry`, `failing tactic` or `unsolved`) and
`goal`; without it `goals` is `null` and `unknown.goals` says why, as it does when the run stopped
before the proof was checked. `failures` holds one record per Lean error, or per goal a tactic
stopped on, located in the developer's file as in the text report:

```json
{
  "kind": "elaboration-error",
  "source": { "file": "/work/Proofs/SpanDrain.lean", "line": 37, "column": 54 },
  "message": "cil_loop_steps: target state not matched at pc 7: ...",
  "tactic": "cil_loop_steps",
  "stopped": false,
  "method": {
    "index": 0,
    "signature": "System.Int32 Examples.Loops::Drain(System.ReadOnlySpan`1<System.Int32>)"
  },
  "cil": {
    "pc": 7, "ilOffset": 19, "instruction": "brtrue.s IL_0002", "leanInstruction": null,
    "source": { "file": "Loops.cs", "line": 30, "column": 9 }
  },
  "state": {
    "reached": {
      "stack": "[CIL.Safety.Value.scalar (CIL.Value.i32 (BitVec.ofNat 32 view.length))]"
    },
    "expected": {
      "stack": "[CIL.Safety.Value.scalar (CIL.Value.i32 (BitVec.ofNat 32 (view.length + 1)))]"
    }
  },
  "missing": { "shape": "targetState", "residual": [] },
  "suggestions": ["state a fact in the reached form, or state the target in it"],
  "obligations": [],
  "unknown": {
    "cil.leanInstruction": "the walk is at the target's pc, so it steps no instruction",
    "obligations": "the goal the tactic was handed carries no obligation tag"
  }
}
```

`kind`, `resource` and `module` are as in `failed.json`. `tactic`, `stopped`,
`method`, `cil`, `state` and `missing` come from the failure record `CIL.Observe`
logged for the error; none is read from the error's prose. `--format json` checks the
proof with `import CIL.Observe` added at the start of its first import line,
which moves no other line or column, and with the Lean option `cil.diagnostics`
set; the observer then records each error a `cil_` tactic raised, and each goal
one left that Lean reports as unsolved, with `stopped` true (see
[PROOFS-STEPPING](PROOFS-STEPPING.md#observer-linter)). An `unsolved
goals` error with several such goals gives one failure per goal. `ilOffset` and
`instruction` are read from the manifest at that method and pc. `cil.source` is
the C# file, line and column of the last visible PDB sequence point at or before
the pc, read from the extraction's `Symbols.lean` whether or not the proof
imports `ExtractedSymbols`; an extraction without a matching PDB has no
`Symbols.lean`, and `unknown` says so. `missing.shape` names the kind of fact the step
lacks, such as `unsafeAdd`, `spanValidity` or `targetState`, `calleeContract` at a
`call` or `callvirt`, or on a class instance `objectForm`, `objectSlot` or
`objectAllocation`, and `residual` the terms it must prove: the step rewritten by
the proof's step equations and the `_ = .ok _` and `_ = .error _` facts in scope.
A side condition, such as an unfolded step a tactic could not close, has a shape when it names one
of these operations. A run stopped before its first instruction because the entry could not check
an object argument lacks `objectForm`, with the `formObject` of each object argument as its
residual. `obligations` lists the obligation tags of the goal that failed, or of the goals an
`unsolved goals` error lists, such as `invariant`.
`suggestions` is advice, kept apart from these facts. Every field left `null`
for lack of data, and an empty `obligations`, has its reason under `unknown`,
keyed by the field's name; an error without a failure record, such as Lean's
own, says so there. The message is Lean's error as printed; the tactic is the
one the error names, also when it ran inside another tactic's expansion, such
as the `cil_loop_steps` that `cil_loop_continue` runs.

### Trace the proof's steps

`leancil verify ... --trace` checks the proof with `import CIL.Observe` added as
for `--format json` and `trace.CIL.step` set, so the observer logs each step the
proof takes, whichever tactic or term took it: its pc and instruction, the
source line when the proof imports `ExtractedSymbols`, the lemmas applied, the
hypotheses its proof used and what changed, then for each `cil_` tactic the
number of steps it took and the obligation tags of the goals it left (see
[PROOFS-STEPPING](PROOFS-STEPPING.md#observer-linter)). The text report
prints them in full under `Trace (N entries):`, after and apart from the proof's
`Lean messages`; the JSON report lists them in `trace`, each with its location
and text. Without `--trace`, `trace` is `null` and `unknown.trace` says why, as
it does when the run stopped before the proof was checked. A traced result is
cached apart from an untraced one.

### Batches

`leancil verify-batch requests.json --format json` prints one JSON document on
stdout instead of the per-request lines: `schema` 1, the `passed` and `failed`
counts, and `requests`, each with its `expect`, its `status` (`verified`,
`rejected` or `failed`) and the `report` that `verify --format json` prints for
it. `--trace` traces every request's proof, after its line in the text report
and in each `report` in JSON. The request manifest, the other options and what a batch shares are
in [batch verification](CONSUMERS.md#batch-verification).

## Export contracts

`leancil export-contracts manifest.json [--output Lib.leancil.contracts] [--bundle directory]`
checks a library's selected contracts and writes their bound sidecar. See
[Publishing verified contracts](CONSUMERS.md#publishing-verified-contracts) for
the manifest, exact theorem guarantee, export restrictions and source bundle.
All exports must pass before the sidecar is published.

## Verify with imported contracts

After import-aware extraction, `leancil verify output --proof Caller.lean` checks
the caller under the published contracts. `--proof-root` uses the same interface
audit for a consumer package. `--fresh` can use an empty `LEANCIL_CACHE_DIR`; no
library implementation proof source, artifact or full bundle is required.
[Contract interfaces](CONTRACT-INTERFACES.md) gives the `extract` options and required pins, the
sidecar schema and its checks, and the form the caller theorem must have.

A schema-4 `verified.json` contains `imports[]` with `acceptedVia` set to
`published-certification`, the implementation SHA-256, interface digest,
certification theorem/statement/digest, `sidecarSha256`, `certificationAuthenticated`
(always `false`: no pinned digest covers the certification text) and deployment
obligation. CLI output prints the certification as an unauthenticated sidecar
record with its sidecar SHA-256, and the obligation. The caller theorem is
conditional on those imported contracts.

`--force-full-verify` freshly checks the selected library implementations and discharges those
imports in a concrete linked CIL theorem; `--full-artifact Lib=directory`, repeatable, selects a
relocated copy of a published source bundle.
[Independent imported-library verification](FULL_VERIFICATION.md) states the checks, the supported
source format and the trust boundaries.

Reference-only extraction is an authoring input. Verification checks its caller
proof, then exits with status 1 and an authoring-only diagnostic. It does not
write `verified.json` or publish a successful proof receipt.

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
The lint is a conservative site analysis. It does not prove feasibility under a
contract, exception conditions, or complete runtime behavior.

XML must contain the selected compiler member ID and matching assembly name.
Unresolved cref, include and inheritdoc need expansion first. The supplied XML
hash identifies bytes; it does not prove that they came from the DLL build.
No documentation text becomes evidence or a contract premise.

## Editor workspace

```text
leancil workspace assembly.dll method --profile profile --proof proof.lean [--theorem name]
    [--proof-root package] [--assembly identity] [--assume-initialized Namespace.Type]...
leancil workspace --remove key-or-method [--profile profile] [--proof-root package]
leancil watch [package] [--project app.csproj]... [--configuration name] [--once] [--goals]
    [--format text|json]
```

`workspace` generates the method's extraction into the proof's Lake package as the modules
`Extracted.KEY` and `ExtractedSymbols.KEY`, so the proof file shows live goals in the editor, and
prints the import to use. KEY names the method and digests its assembly name, signature, profile
and initialization assumptions, so each method has its own module. Run it again after rebuilding
the assembly, then restart the file in the editor.

| Option | Meaning |
| --- | --- |
| `--profile` | The execution profile, as for `extract`. This option is required. |
| `--proof` | The proof file to open in the editor. This option is required. |
| `--theorem` | The theorem `watch` verifies; without it `watch` only refreshes the editor modules. |
| `--proof-root` | The Lake package. The default is the nearest package above the proof; a proof outside any package gets one beside it. |
| `--assembly`, `--assume-initialized` | As for `extract`. |
| `--remove` | Drop one recorded selection, named by KEY or by a method selector that names one recorded profile (add `--profile` when it names several), from the package given by `--proof-root`, by default the one holding the current directory. Its record, both modules and their Lake outputs are deleted; nothing is rebuilt. |

`watch` rebuilds the C# on change, refreshes the extractions whose generated modules changed and
runs `verify` for each recorded proof whose extraction or sources changed.

| Option | Meaning |
| --- | --- |
| `package` | The Lake package `workspace` used. The default is the current directory. |
| `--project` | A C# project to build and watch; repeatable. |
| `--configuration` | The build configuration. The default is `Release`. |
| `--once` | Run one cycle; exit `1` unless every proof verified or names no theorem. |
| `--goals` | Print each proof's open goals every cycle. |
| `--format json` | Print each cycle as one JSON line. |

Run `verify` on the same files for a certificate; editor checking gives none. The package layout,
the editing loop, the watch statuses and the certification step are in [proof-authoring
workspace](CONSUMERS.md#proof-authoring-workspace).
