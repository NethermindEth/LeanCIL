# Command-line reference

The [getting-started guide](GETTING-STARTED.md) walks through a first verification. This page gives the
details of each command.

## Build

A regular `dotnet build Extractor -c Release` produces `Extractor/bin/leancil.exe` on Windows (`leancil` on other platforms). The managed assembly and package are named `Nethermind.LeanCIL`.

## Version

`leancil --version` prints the tool version (the installed package version, such as `0.1.0-dev.<stamp>` for a development pack), the LeanCIL commit and Lean toolchain its framework comes from, and the `[[require]]` block a [consumer package](CONSUMERS.md#consumer-proof-packages) uses to pin the matching framework. A tool built outside a git checkout reports the revision as unknown.

## Discover and select methods

This lists canonical method signatures you can copy into `extract`, including overloads and non-public methods. Discovery reads metadata without executing the assembly. Listed methods are not necessarily supported: `extract` validates their signatures, CIL and reachable dependencies.

Method selectors accept C# type aliases, an optional return type, and an unqualified declaring type when the result is unique. These all select the same method:

```text
System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)
ulong Examples.Arithmetic::Add(ulong,ulong)
Examples.Arithmetic::Add(ulong,ulong)
Arithmetic::Add(ulong,ulong)
```

The parameter list remains required. Matching is case-sensitive; an explicit return type must match. Use `ulong&` for a by-reference parameter. An `in` parameter of a virtual, abstract or interface member, including an explicit interface implementation, is spelled `ulong& modreq(System.Runtime.InteropServices.InAttribute)`, as `discover` prints it; the modifier is part of the selector and the recorded signature, so it never matches the unmodified `ulong&` overload. Ambiguous selectors fail with a list of full candidate signatures, which can be copied into the command. Artifacts always record the resolved canonical signature, so equivalent selectors can check the same artifact. Selection never relaxes supported-type or instruction validation.

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

Extraction also emits raw metadata and a `Extracted.translation_valid` certificate. Independent Lean validators recompute layouts, check all layout-dependent sites and parameter-home mappings, validate structural generic substitution and managed-call bindings, and check feature-analysis states, decided type tests and control-flow coverage. Per-site validators walk the raw code, reachability mask and emitted code in lockstep, so a long branch excluded by the profile adds linear rather than quadratic checking cost. Verification requires this certificate to have the exact validator type for the complete emitted program and kernel-replays it separately from the user proof. Raw metadata serialization and transformations outside those checks remain trusted.

Profiles default to scalar. Pass a supported profile name or `@profile.json` as the final positional argument to `leancil extract`. Both `check` and `verify` recover the profile from the manifest. Capability prerequisites are validated. Instructions unreachable under that exact fixed profile are emitted as explicit unsupported placeholders; changing profiles invalidates artifacts.

### Initialization assumptions

Methods on types with static constructors are rejected by default; the diagnostic names the
type and the flag to pass. If the caller guarantees successful initialization before
invocation, extraction can record that precondition explicitly:

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
value its static constructor stored. A field whose value extraction cannot compute is
also listed in `opaqueStaticValues` and reported as `Unknown static value`; its loads
read the caller's static binding. The generated Lean source and identity
manifest retain the assumptions; `check` reuses them and rejects conflicting
explicit assumptions. Verification binds the manifest hash, prints the
initialization preconditions with the theorem and copies both lists into
`verified.json`. Re-extract older artifacts to include the new manifest fields.

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
replays the recorded references and rejects a changed hash or identity; it does not accept
`--reference` itself. Assemblies resolve only against this pinned set and the runtime's platform
assemblies, so an unpinned reference, a name pinned under another version, a duplicate identity
or a framework DLL passed as a reference fails. One assembly cannot be both a typed import and a
reference.

A referenced assembly's static methods are admitted as direct `call` and `ldftn` targets, and its
structs and interfaces as layouts and [constrained dispatch](OPCODES.md#constrained-struct-calls),
including static flag getters that fold a branch; a struct of the selected assembly may implement a
referenced interface or rely on its interface-level bodies, and a closed generic struct of either
assembly may receive a static slot. Its generic methods, the static methods
of its generic classes and the methods of its closed generic structs are specialized from its own
metadata, so their bodies stay attributed to its pin. A closed generic struct such as
`Lib.Pair<ulong>` is laid out from the assembly that defines it, and its type arguments may be
value types of the selected assembly or of any pinned reference, in either direction.
Reference-type arguments, reference fields and layout cycles are rejected. Static field loads,
`calli` and types with static constructors in a referenced assembly are rejected. A closed entry
type argument may name one of its structs as `Namespace.Type, Assembly`, by simple or full
assembly name:

```sh
leancil extract App.dll 'App.Application::Size(ulong)' artifacts/Size --reference Lib.dll   --type-argument 'Lib.Cell, Lib'
```

A static method of a generic class can be the entry. `--type-argument` lists the method's own
type arguments first, then the declaring type's, outer type parameters before inner ones as
ECMA-335 numbers them; the selector names the open definition:

```sh
leancil extract App.dll 'App.Algo`1::Run(ulong)' artifacts/Run --type-argument App.Gas
```

Instance methods of generic classes remain rejected as entries and as callees.

## Report extraction blockers

`leancil blockers` runs admission, the validation `extract` performs, over an explicit list of
method and profile pairs, and reports everything that blocks each one instead of stopping at the
first failure. It checks no proofs and keeps no extraction artifacts:

```sh
leancil blockers assembly.dll --manifest blockers-manifest.json [--output blockers.json]
```

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

`profile` is a profile name or `@file`, resolved against the manifest's directory;
`initializedTypes` applies `--assume-initialized` to every entry, `references` (paths relative to
the manifest) or `--reference` pins referenced assemblies for every entry, and an entry's optional
`typeArguments` applies `--type-argument` to it. Contract imports are those of `extract`: the
`--import`, `--import-implementation`, `--import-sha256` and `--import-interface-sha256` options,
or the manifest's `imports`, `importImplementations`, `importSha256` and `importInterfaceSha256`
(paths relative to the manifest), apply to every entry, and a sidecar beside the assembly is
discovered as `extract` discovers it. An entry with no blockers is then extracted into a scratch
directory, so `admitted` means exactly that `extract` succeeds. The report goes to
`--output`, by default `blockers.json` next to the manifest, and a short summary goes to standard
output. Each entry is `admitted` (extraction would succeed), `blocked`, or `notChecked` with the
reason: a selector that matches no method or several, a malformed type argument, an unknown
profile, or an assembly, import or assumption that fails before any method is checked. An entry
the selector resolves but `extract` rejects by its shape, such as an `init` setter or a member of
an open generic type, is `blocked`, and its definition is analysed as an entry. Each blocker is
one unsupported construct (instruction, call, type, layout, method metadata or static
constructor). It lists every site, with method, IL offset, instruction and the PDB source location
when one is present, and every affected entry with the call chains from it to those sites. A
condition found by two checks, such as an entry's modifier and the type that carries it, is
reported once, by the more specific check. A rejected signature, receiver, static constructor or
entry shape does not stop the analysis: the body and callees behind it are still checked and
their blockers reported. Only a method without IL to analyse, or a body whose control flow cannot
be analysed, ends its branch, and that blocker's message names what was not analysed behind it.
Only code reachable under the entry's profile is checked, so a branch excluded by a constant
`IsSupported` is never reported. Admission is not verification: an admitted entry still needs a
proof. The command exits with `0` whenever the report is written, whatever the entries' status.

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

## Start a proof

Write a starting proof of an extraction's entry method:

```sh
leancil extract Examples/Assembly/bin/Examples.dll "Loops::Countdown(uint)" artifacts/Countdown
leancil new-proof artifacts/Countdown Proofs/Countdown.lean
```

Expected output on standard output:

```text
Wrote Proofs/Countdown.lean: a starting proof of System.UInt32 Examples.Loops::Countdown(System.UInt32)
  Holes: 8 obligations, 0 paths not outlined (each `sorry`; verify rejects the file until none remain)
  Next: fill the holes, then run leancil verify artifacts/Countdown --proof Proofs/Countdown.lean
```

`new-proof` reads only the extraction directory and first runs the same comparison as
`leancil check`, so a stale or edited extraction is refused at the `extraction integrity` stage. It
never replaces a file: when the proof path exists, it exits with `1` and writes nothing. The same
extraction always gives the same file, byte for byte. It imports the extraction's keyed module,
`Extracted.KEY` (see [Editor workspace](#editor-workspace)), so the file opens in the editor once
`leancil workspace` selects the method, and `verify` accepts that import for this extraction only.

The file states `ExampleProof.correctness` as a `CIL.Safety.Ensures` theorem over the method's
parameters, named as in the PDB, and checks it with `#print axioms correctness`. A `bool` parameter
is a `Bool`, a narrow integer a `BitVec` of its width, and a `bool` result the `Bool` its returned
word encodes. Every place the author must decide something is a `sorry`, each with a one-line
comment saying which obligation it is:

- `Precondition` and `Postcondition` are definitions to replace with the specification. The
  theorem assumes the precondition and promises the postcondition of the returned value, and for
  a method that takes references or spans also of the caller's memory before and after.
- A method without a loop is stepped by `cil_checked_steps` when its body is arithmetic on 32- and
  64-bit arguments or a total bit count (`Log2`, `PopCount`, `LeadingZeroCount`,
  `TrailingZeroCount`), leaving only the postcondition. A signed or unsigned checked `+`, `-` or
  `*` is split with `by_cases fitsN` on whether its integer result fits: the side where it fits
  steps with `checkedValues_add_unsigned_i32`, `checkedValues_add_signed_i32` or their siblings,
  and the overflowing side, which throws, is closed from the precondition by
  `cil_loop_obligation`. A conditional branch on words the body computes from its arguments, signed
  or unsigned, is split with `by_cases branchN` on the condition it tests, and each side steps on
  to its own return and leaves its own postcondition, commented with the side it is on; a body
  splits into at most eight returns. When it also takes up to three `bool`
  arguments and tests nothing else, it is split with `cases` on each, and every side steps to its
  own return and leaves its own postcondition, commented with the values it is for.
- A method with a loop gets its loop state, the cutpoint at the loop's back-edge test (found by
  instruction, never by pc), and `invariant` and `measure` definitions to replace. A method that
  takes a reference also gets a `footprint` to replace: the caller memory the loop may write, which
  the loop state carries. The proof applies `invoke_loop_satisfies`, steps the entry to the first
  loop head, splits the iteration where the body branches, and leaves the obligations the loop
  tactics tag: `invariant` and `measure` where an iteration continues, `postcondition` where it
  returns, and `precondition` at a call. An object local, such as a list walk's `node`, is a
  `ManagedReference` of the loop state, and the cutpoint's frame names its slot from the state. A
  null test of it splits the proof with `cases node`, leaving a hole for the liveness of the
  instance it holds, and an identity test against another object splits it with
  `by_cases branch1 : ...`; a load of a reference field into it is a `not outlined:` hole. A test
  of a 1- or 2-byte struct field splits on the word its load zero-extends, such as
  `(scanStopped.setWidth 8).setWidth 32 = 0`. A 4- or 8-byte store through `Unsafe.Add` of a
  reference argument by an `int` index, before any other store of the iteration, is stepped from
  write authority over that element at the iteration's memory, the index below `2 ^ 31` and the
  element within `footprint`. `cil_loop_obligation` proves each from the invariant, precondition
  and footprint the author writes, by `omega` over their conjuncts or from a `Filled` or `Writable`
  fact covering the element; it is a hole while any of those is `sorry`, and an error at the write
  once they are written and do not imply it.
- A loop over a `Span<T>` of 32- or 64-bit integers that stores `span[0]` and continues with
  `span.Slice(1)` keeps the span as a `WritableSuffix`: its `WritableSpan` holds the view's checks
  and `SpanWritable` authority in the caller's memory, not its contents, so the caller need not
  have initialized it. The loop splits on the remaining length with `cases`, the store, before any
  other store of the iteration, steps through `frame.write_span_head`, which names the element's
  address, and `Slice(1)` through `WritableSpan.tail`. The span's bytes are its `footprint`, and
  the theorem assumes `SpanWritable` over them. A read of the written span is a `not outlined:`
  hole.
- Loops in sequence are bound in pc order (`loop`, `loop2`, ...), each with its own cutpoint,
  `invariant` and `measure` (`header2`, `invariant2`, `measure2`, ...). The path leaving one loop
  for the next loop's test enters that loop through `loop_terminates_then`, leaving its invariant at
  its first head, and that loop's iteration follows. A loop nested in another is refused.
- A call in the loop gets a `MethodContract` for the callee, with `pre` and `post` to replace, and a
  `Holds` theorem that steps the callee when it is arithmetic on its arguments. A callee of words
  that tests them and returns or throws on each side is split with `by_cases` on each test: each
  returning side is stepped and leaves `post`, and each throwing side is closed from `pre` by
  `cil_loop_obligation`. A call whose callee returns a value is crossed with
  `cil_loop_call keeping`, so the next loop state names its result `output` whatever `post`
  states. A callee that only stores a word argument through a reference argument gets the
  contract its body meets, proved: write authority over that word before, its contents after. When
  the loop passes it `Unsafe.Add` of a reference argument by an `int` index, the element is named
  with the same three side conditions as a store, its authority stated at the caller's memory, and
  they close the call's precondition. A callee over
  objects whose body a straight-line outline steps (see below) gets the contract read from its body
  instead, proved, leaving only its precondition at each call.
- A struct instance method binds `this`, a reference to the caller's struct, as a `Reference` named
  for the struct, such as `counter`. A straight-line body over its 64-bit fields and word
  arguments is stepped: each field it reads first gets a binder for its value on entry, such as
  `counterValue`, with `Contents` of the field's address (`counter`, or `counter.element 1 8` at
  offset 8) in the statement, and the one field it may store gets `Writable` authority there and
  `Confined` to it; a second store, or a load of another field after the store, is a
  `not outlined:` hole. The postcondition is left
  with `held1`, the stored field's `Contents` in the final memory. A struct method with a loop is
  refused.
- An instance of an admitted class is a `Reference`, and an instance method binds `this` under its
  class's name in lower case, such as `account`, or as `receiver` for a compiler-generated class.
  A parameter named like a hypothesis or memory the proof introduces, such as `held` or `stored1`,
  is bound as `argument` and its position instead. The statement assumes `LiveObject initial account`, and `Readable` of each field the body or a
  callee it steps reads of each object and `Owned` of each they write, using the field views the
  extraction emits in `Extracted.Classes` (see
  [Frame class instances](PROOFS-CONTRACTS.md#frame-class-instances)). An object the body loads from
  a reference field is a further binder, such as `nodeNextTarget`, with the premise that the field
  holds it. A method that writes a field promises `Confined footprint initial final`, with
  `footprint` listing the written fields. The body is stepped through its field loads, its stores,
  locals and null tests of objects, carrying each field's fact across the stores before it, and
  leaves the postcondition with `held1`, `held2`, ... the stored fields' `Holds` facts. A test of
  words it names, such as a field value against an argument, splits the proof with
  `by_cases branch1 : ...`, and each side steps on to its own return and leaves its own
  postcondition, commented with the side it is on.
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
  `not outlined:` hole, since the two may be one element; so is a reference outside the model used
  after a call that writes. A `newarr` of class references of a literal length, the body's first
  write, adds the premise `CIL.objectFieldSlot * 2 ≤ initial.heapBudget` for its slots and a
  `fresh1Element` def naming its element class; its elements start as owned nulls, the array is
  `fresh1` with `fresh1Identity` dating it after every caller allocation, and the footprint
  forgets its elements through `Confined.forget_fresh`. An index into it that is not a literal
  below its length is a `not outlined:` hole, as is a method with a loop.
- A call in a body over objects to a method that loads its fields, stores at most one word field of
  an object argument and returns a value it names gets a generated `MethodContract` read from that
  body, with a `Holds` theorem proved by the same stepping; `cil_contract_steps` composes the call
  through it, and the callee's store counts as one of the caller's. A callee that loads an object
  from a reference field and stores nothing gets a `pre` asking that some object, such as
  `nodeNextTarget`, is held there with the facts it reads, and a `post` stating the result of
  whichever object the field holds; the caller names that object by its own fact that the field
  holds it, from a store just before the call or a target of its statement. Any other call is a
  `not outlined:` hole naming the callee. A loop
  carries the object facts across its iterations, and a `callvirt` in it gets a contract like any
  other call. A loop's statement assumes the same per-object facts, read from its body and callees
  in order; when that reading stops, it assumes a fact of every named field of each object, `Owned`
  where the method or a callee stores the field.

Where the outline cannot step a path, it leaves a hole whose comment starts with `not outlined:`,
names what it met and what that step needs, and gives the source line to continue from. The
`Holes` line counts these apart from the obligations. The unedited file elaborates with only
warnings that a declaration uses `sorry`, and `leancil verify` rejects it at the theorem audit for
`sorryAx`; it can never verify until every hole is filled.

The countdown's outline:

```lean extracted
import Extracted.Loops_Countdown_1347de14
import CIL.Verification
import CIL.StructuralLabels
import CIL.Safety.LoopScaffold

/-! A starting proof of `Countdown`, generated by `leancil new-proof` from its extraction. Each
    `sorry` is a hole, and `leancil verify` rejects the file until none remains. A hole commented
    `not outlined:` marks a path the outline could not step. The tactics leave obligations tagged
    `invariant`, `measure`, `postcondition` and `precondition` (at a call), which the holes select
    with `case`. -/

open CIL.Safety
open CIL (W32 W64)
namespace ExampleProof

/-- Replace with what callers must guarantee about the arguments, or `True`. -/
def Precondition (value : W32) : Prop := sorry

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

/-- Replace with what holds at every loop head. -/
def invariant (value : W32) {home0 : Reference} (state : State home0) : Prop := sorry

/-- Replace with a quantity each iteration decreases. -/
def measure (value : W32) {home0 : Reference} (state : State home0) : Nat := sorry

theorem correctness (value : W32) : Ensures Extracted.program 0
    (fun args initial => args = [.scalar (.i32 value)] ∧ initial = Memory.empty ∧
      Precondition value)
    (fun _ _ _ results => ∃ result : W32, results = [.scalar (.i32 result)] ∧
      Postcondition value result) := by
  rintro args initial ⟨rfl, rfl, assumed⟩
  obtain ⟨home0, entered, setup, -, -, entryFrame⟩ := entry.checked value
  refine invoke_loop_satisfies Extracted.lookup0 rfl setup (header home0) (invariant value)
      (measure value) (fun start => ?_) ?_
  · have entryFrame := entryFrame []
    cil_loop_recurse start value
    case invariant => sorry -- invariant at the first loop head
  rintro ⟨remaining, current, frame⟩ holds recurse
  by_cases guard : remaining = 0
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

`verify` first checks the extraction artifacts, reuses an integrity-checked source-keyed library cache (or builds it on a cache miss), checks and kernel-replays the selected proof, and audits its transitive axioms. Use `--fresh` to bypass proof and support reuse while retaining the source-bound library cache. Use `--rebuild-library` to rebuild the library as well; CI bypasses the local library cache automatically. Interactive terminals receive build progress on stderr; stdout and redirected stderr retain their stable formats. Only `propext`, `Quot.sound` and `Classical.choice` are permitted. It checks artifact and source identity again before writing `artifacts/Add/verified.json`. Lean and Lake must be installed. The tool ships the framework's `CIL` sources only: proofs import `Extracted` (or a method's `Extracted.KEY`, see [Editor workspace](#editor-workspace)) and `CIL.*`, and `CIL.Safety.Memory.empty` is the caller memory with no allocations. LeanCIL's own example and test modules are not shipped; a proof importing one is rejected as `invalid-request`.

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

Every invocation checks the proof afresh. A failed proof removes the previous verification report. When the assembly or the extractor changed since extraction, `verify` first extracts again from the settings `identity.json` records (assembly path, method, profile, assumptions, references and imports) and prints `Re-extracted artifacts/Add: the assembly changed since extraction.` (on stderr with `--format json`); a method that no longer exists then fails at extraction. An artifact that changed while its assembly and extractor did not is still rejected as tampered. `verify-batch` does not extract again; it reports such an output as a stale input. `extract` generates definitions and `check` validates extraction consistency; `verify` establishes the selected theorem about those definitions. Its guarantee is exactly the theorem's statement, including its preconditions and quantifiers.

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
- `Lean messages` lists the informational and warning messages of the proof file, such as
  `#check`, `#eval` and `#print axioms` output, at `file:line:column` in the proof. The first 60
  lines are shown; `proof-messages.txt` in the artifact directory holds the full text, and the
  report names it when lines are omitted. Messages are stored with the cached proof, so a run that
  reuses the proof shows them as well. They are printed on failure too, after the diagnostic, so
  query commands work while a proof is unfinished, including under `--proof-root` when proof
  checking itself fails.

Release packages can include a certified-library descriptor for the current runtime. On the first
cache miss, the CLI downloads that exact release asset from the official LeanCIL GitHub repository.
The installed package pins its archive hash, producer manifest hash, runtime and source/toolchain
key. The download is validated and independently kernel-replayed before receiving a local cache
receipt. A missing descriptor, incompatible library or unavailable download falls back to building
the packaged sources. `--rebuild-library` bypasses this download and the local library cache;
an explicitly supplied certified library remains usable.

### Publishing certified library assets

For each supported runtime, from the exact sources that will be packaged, prepare and replay a
library, then create its archive and package descriptor. The digest comes from the preparation
command's output, independently of the directory being archived:

```sh
dotnet run --file scripts/PrepareLibrary.cs -- artifacts/release-library
dotnet run --file scripts/PackageCertifiedLibrary.cs -- artifacts/release-library PRODUCER_SHA256 vVERSION artifacts/release-assets
```

The packaging command checks the entire producer artifact, replays its modules, and validates the
bytes actually written to the archive. Collect the generated `certified-library-release.*.json`
files from supported runtimes into one directory and pass that directory when packing the CLI:

```sh
dotnet pack Extractor -c Release -p:CertifiedLibraryReleaseDirectory=/absolute/path/to/release-assets
```

Publish the generated ZIP files as assets of the named release in `NethermindEth/LeanCIL` and
distribute the CLI package through the normal trusted package channel. The descriptor is part of
that installed package, so neither a mutable release asset nor a manifest inside its ZIP can
authorize replacement bytes. These commands prepare files; they do not publish a release or upload
a package. Without descriptors, development builds retain the normal local build behavior.

## Diagnostics

Method and call validation failures name the rejected item and the method containing it.
A rejected call reports its callee, caller, IL offset and declaring assembly scope. For
example, a reachable `Environment.ProcessorCount` call is outside the admitted runtime
models. Exact closed `typeof` comparisons are supported; a `GetTypeFromHandle` call
outside those patterns remains unsupported. The diagnostic identifies metadata/CIL
validation as the failing stage and links to the supported subset.

When proof checking fails, the report leads with `Lean errors (N):`: each
`error:` diagnostic with its `file:line:col`, the module Lake was building and
its full message block, omitting axiom reports, traces and warnings. Each error
is printed once. A message longer than 40 lines or 400 columns, and every error
after the first 20, is shortened or left out of this summary and printed in full
under `Details:`; nothing else follows. When the output holds no Lean error,
such as a crashed tool, `Details:` holds the whole output instead. The
unmodified output is the `message` of [`failed.json`](#failure-reports) and,
when `LEANCIL_TRACE_DIRECTORY` is set, its transcripts.

Verification checks a copy of the proof, `Extracted.lean`, the PDB names and,
under `--proof-root`, the package's sources and its proof module. A location
in a copy cites the file it was copied from, at the same line and column, and
Lake's module names the proof's own module, so editors and terminals open the
file the developer edits. Only a copy byte-identical to its original when it
was made is mapped; a generated module keeps the path Lean printed.
Direct verification checks the proof with `lean --json` and renders each message
in Lean's `file:line:col: severity:` form; informational messages, which plain
Lean output prints without a position, appear there as `info:` entries, and the
proof's own messages follow under `Lean messages` as described above.

### Environment size on Windows

Lean on Windows builds the environment of each process it starts in a 32,767-byte buffer.
Lake starts Lean, including the editor's language server, with its own variables
(`LEAN_PATH`, `LEAN_SRC_PATH`, `PATH` and others) added to the environment it inherited,
and Lean drops every variable that no longer fits without an error, so `LEAN_PATH` can
vanish and imports stop resolving. Each `name=value` entry counts its UTF-8 bytes plus a
terminator, and the block adds one more. Lean replaces an inherited variable only when the
name matches exactly, so Lake's `PATH` is added beside an inherited `Path` and the search
path counts twice.

Before running Lake, leancil computes what Lake will pass on: the environment it gives Lake,
with the changes elan's `lake` proxy makes, and the variables `lake env` prints (for
`lake build`, which passes Lean only `LEAN_PATH`, just that one). It fails when the result
exceeds the limit, naming the size, the limit and the largest variables. `leancil workspace`
makes the same check for `lake serve`, taking its own environment as the editor's, so the
failure appears at setup rather than as unresolved imports. Lake prints a variable it unsets
as empty; counting it can overstate the size by a few bytes, never understate it.

Lake adds a package's source directory to `LEAN_SRC_PATH` once for every `[[lean_lib]]`
table in the package's lakefile, without merging repeats. The framework copy `leancil workspace` writes for
a proof outside any package declares only the framework and editor libraries, but a consumer
that pins the `leancil` repository gets its lakefile with one library per test module, so the
framework directory appears about ninety times in that consumer's `LEAN_SRC_PATH`. A shorter
checkout path and fewer `PATH` entries leave more room. Setting
`LEANCIL_LEAN_ENVIRONMENT_LIMIT` to a byte count lowers the limit; on other systems, where
Lean has no such buffer, it enables the check, for example to measure headroom.

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
Locations in the session's copies cite their originals, as in the text
report. `message` is the
original output, unmodified; `rerun` reruns just that request. Classification
uses only the stage, LeanCIL's own messages and Lean's error prefixes above.
An unsolved goal is never a refutation: only a verified theorem whose
elaborated statement is `Not` applied to a contract's `Holds` is, as reported by
the theorem audit. A verified refutation keeps its `verified.json`, the
certificate of the refutation, and also writes `failed.json` with kind
`refutation`, located at the theorem's name.

### Machine-readable verify output

`leancil verify ... --format json` prints one JSON report on stdout instead of
the text report, and nothing on stderr; the exit code is the same as without
it. `--format text` is the default. The report has `schema` 1, `result`
(`verified` or `failed`), the `stage` that failed, the `theorem`, `method`,
`proof` and `output`, and on success the `axioms` and `statement`. The proof's
own Lean messages are in `messages`, and `rerun` repeats the run. `failures`
holds one record per Lean error, or per goal a tactic stopped on, located in
the developer's file as in the text report:

```json
{
  "kind": "elaboration-error",
  "source": { "file": "/work/Proofs/Countdown.lean", "line": 40, "column": 4 },
  "message": "cil_loop_steps: target state not matched at pc 8: ...",
  "tactic": "cil_loop_steps",
  "stopped": false,
  "method": { "index": 0, "signature": "System.UInt32 Examples.Loops::Countdown(System.UInt32)" },
  "cil": {
    "pc": 8, "ilOffset": 9, "instruction": "brtrue.s IL_0004", "leanInstruction": null,
    "source": { "file": "Loops.cs", "line": 38, "column": 9 }
  },
  "state": {
    "reached": { "stack": "[CIL.Safety.Value.scalar (CIL.Value.i32 (x - 1#32))]" },
    "expected": { "stack": "[CIL.Safety.Value.scalar (CIL.Value.i32 (x - 2))]" }
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
logged for the error, never from the error's prose. `--format json` checks the
proof with `import CIL.Observe` added at the start of its first import line,
which moves no other line or column, and with the Lean option `cil.diagnostics`
set; the observer then records each error a `cil_` tactic raised, and each goal
one left that Lean reports as unsolved, with `stopped` true (see
[PROOFS-STEPPING](PROOFS-STEPPING.md#see-what-the-tactics-did)). An `unsolved
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
A side condition, such as an unfolded step a tactic could not close, has a shape
when it names one of these operations. A run stopped before its first instruction
because the entry could not check an object argument lacks `objectForm`, with the
`formObject` of each object argument as its residual. `obligations` lists the obligation tags of the goal that
failed, or of the goals an `unsolved goals` error lists, such as `invariant`.
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
[PROOFS-STEPPING](PROOFS-STEPPING.md#see-what-the-tactics-did)). The text report
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
and in each `report` in JSON.

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
its required `staticIdentities` list against the selected implementation's
reachable static fields. Each entry contains `identity`, `assemblyIdentity` and
`fieldName`. Extraction recomputes this list from the selected implementation's metadata and reachable instructions.
The driver also checks
the actual exported contract type structurally and computes its canonical closure
from replayed oleans. `statementDigest` hashes the UTF-8 `statement` returned by
that audit. The consumer records this provenance without obtaining the
implementation proof. See [Contract interfaces](CONTRACT-INTERFACES.md).

A schema-4 `verified.json` contains `imports[]` with `acceptedVia` set to
`published-certification`, the implementation SHA-256, interface digest,
certification theorem/statement/digest, `sidecarSha256`, `certificationAuthenticated`
(always `false`: no pinned digest covers the certification text) and deployment
obligation. CLI output prints the certification as an unauthenticated sidecar
record with its sidecar SHA-256, and the obligation. The caller theorem remains
conditional on those imported contracts.

`--force-full-verify` freshly checks the selected library implementations and
discharges those imports in a concrete linked CIL theorem. Repeat
`--full-artifact Lib=directory` to select relocated copies of the published
source bundles. Missing or invalid bundles fail without fallback. See
[Independent imported-library verification](FULL_VERIFICATION.md) for the
supported source format, checks and remaining trust boundaries.

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

## Editor workspace

`leancil workspace <assembly> <method> --profile <profile> --proof <file> [--theorem name]`
generates the method's extraction into the proof's Lake package as `Extracted.KEY` and
`ExtractedSymbols.KEY`, modules of the framework's `LeanCILEditor` library below `.lake`, so the
proof file itself shows live goals. It prints the import; KEY names the method and digests its
assembly name, signature, profile and initialization assumptions, so each method keeps its own
module and proofs of several methods stay open at once. After rebuilding the assembly, run it
again to refresh the extraction in place, then restart the file in the editor. A proof outside
any Lake package gets a package beside it that requires the bundled framework, so no
`lake update` or `--proof-root` is needed. Verification accepts the keyed import only for the
extraction it checks and builds it as a re-export of `Extracted`. `new-proof` writes the same
keyed import, so its outline opens in the editor as generated.

`leancil workspace --remove <key-or-method> [--profile profile] [--proof-root package]` drops one
selection from the package (by default the one holding the current directory): its record, both
modules and their Lake outputs. A method selector must name one recorded profile, so pass the
key or `--profile` when it names several. Nothing else is rebuilt.

`leancil watch [package] --project app.csproj... [--configuration name] [--once] [--format text|json]`
rebuilds the C# on change, refreshes only the extractions whose generated modules changed and
runs ordinary `verify` for each recorded proof whose extraction or sources changed. A failed
build reports every proof `stale` with the compiler errors' C# locations and deletes their
certificates; a method that no longer extracts is `missing`. See
[Proof-authoring workspace](CONSUMERS.md#proof-authoring-workspace) for the loop, the watch
statuses, pinned imports and the separate certification step. Editor checking is not a
certificate.