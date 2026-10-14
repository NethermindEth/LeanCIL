# LeanCIL: Formal Verification for .NET

LeanCIL is a Lean 4 formal verification framework for .NET programs. It enables machine-checked proofs of correctness and safety against compiled Common Intermediate Language (CIL), supporting applications written in C#, F#, and other .NET languages.

Verification operates on the assembly's actual compiled instructions using CIL semantics defined in Lean. The current [supported subset](#supported-subset-and-limits) covers selected instructions and runtime features; unsupported behaviour is rejected explicitly.

## Build and test

Install the toolchain selected by `lean-toolchain` (Lean **4.35.0**, through elan) and .NET SDK **10.0.402**. The only NuGet dependency is Mono.Cecil, pinned in `Directory.Packages.props`; Lean uses Std and Lean, without Mathlib.

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

The check reads the assembly path, method and hardware profile from the manifest, regenerates the extraction in memory, and compares it with the saved files without overwriting them. Assembly paths are stored relative to the artifact directory. If the DLL moves, use `leancil check artifacts/Add --assembly-path path/to/Examples.dll`; its identity and content must still match. Older manifests must be regenerated with `extract`.

Verify a Lean proof against the extracted method:

```sh
leancil verify artifacts/Add --proof Examples/Proofs/Add.lean
```

`verify` first checks the extraction artifacts, builds the bundled Lean sources in a fresh directory, checks the selected theorem with Lean, and audits its transitive axioms. Only `propext`, `Quot.sound` and `Classical.choice` are permitted. It checks artifact and source identity again before writing `artifacts/Add/verified.json`. Lean and Lake must be installed; the tool includes the framework sources.

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
| Verification | `leancil verify` | Fresh source builds, named theorem audit and assembly/source identity binding |

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

Verification first checks the extraction, builds the bundled Lean sources in a fresh directory, checks the selected theorem and audits its axioms. It writes `artifacts/Add/verified.json` only after the proof and final identity checks succeed.

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

The generated `Extracted.lean` contains `arg 0`, `arg 1`, `add`, `ret`, the exact method signature, assembly hash, metadata, profile and kernel-checked fetch equations. The entry is method zero; reachable managed callees are emitted in dependency order.

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

To prove another method, supply a unique method selector, write a Lean file importing `Extracted`, state a specification and prove it from `Extracted.program`. By default the driver checks `ExampleProof.correctness`; use `--theorem` for another name. `CIL.Safety.Ensures` expresses total correctness with successful finite execution. `VC` and `ensures_of_vc` expose a chosen finite execution condition. Simple concrete tests can use kernel reduction (`rfl`); symbolic proofs use ordinary Lean reasoning or `cil_steps`. Exhaustion and unsupported states are failures.

## Independent examples

- `Add`: universal modular arithmetic correctness.
- `Choose`: symbolic conditional execution.
- `Calls`: a managed-call chain with an address-taken mutable local.
- `IntegerOperations.Negate32` / `Negate64`: checked-execution proofs that negation returns the modular additive inverse for every input, including the signed minimum.
- `NarrowIntegers`: signed/unsigned casts, character values, calls and an eight-byte struct containing narrow fields. `UnsignedShort.lean` proves reduction modulo 65,536 for every 32-bit input.
- `PrimitiveOperations`: reads/writes through integer references, aliasing, switch tables and aggregate `sizeof`. `PrimitiveReadWrite.lean` proves that a store followed by a load returns every 32-bit input unchanged.
- `Alias`: two arguments naming the same caller storage.
- `Struct` and `StructCopy`: reference and by-value use of a **12-byte explicit-layout struct**, with an 8-byte field and a 4-byte field, initialization and a byref helper call.
- `LargeStruct`: a **40-byte** explicit layout with a field at offset 32.
- `PastEnd`: a permitted end sentinel whose dereference is rejected as outside the allocation, for every fuel budget.
- `Escape`: a reference to an expired local is rejected on return, for every fuel budget.
- `WrongAdd`: a mathematical counterexample to the intended addition contract.
- A separate `Examples.Hardware` assembly, built from the file-based library `Examples/Hardware/Hardware.cs`, tests runtime capability extraction.
- A Cecil-generated independent fixture tests extraction-bound static RVA bytes.

Concrete example proofs establish their displayed inputs. Only explicitly universally quantified theorems claim arbitrary-input correctness. The library additionally proves generic allocation, frame, reference, aliasing and storage properties.

## Supported subset and limits

The [opcode support table](docs/OPCODES.md) lists every opcode currently translated by the extractor, including short forms, operand restrictions and execution limits. **Complete** means complete within the admitted value/memory model; **partial** means additional cases are excluded. Neither label claims complete CLR coverage or proves a particular method correct.

| Opcode family | Status | Main restriction |
| --- | --- | --- |
| `ldc.i4` and its short forms, `ldc.i8`, `dup`, `pop` | Complete within the admitted model | Integer constants and supported stack values |
| Argument/local loads and stores, `ldloca` | Partial | Admitted types; no address of a managed-reference local |
| `add`, `sub`, `mul`, bitwise operations, shifts, selected comparisons/conversions | Partial | Supported integer operand shapes; no floating-point or checked-overflow arithmetic |
| Supported branches | Partial | Forward-only reachable control flow; integer conditions/comparisons |
| `call`, `ret` | Partial | Acyclic static managed methods and explicitly modelled runtime calls |
| Integer `ldind.*` / `stind.*`, `ldobj`, `stobj`, `initobj`, fields, `ldsflda` | Partial | Checked references, validated integer/aggregate layouts and restricted static data |
| `switch`, `sizeof` | Partial | Forward jump tables and validated integer/explicit aggregate sizes |
| `newobj` | Partial | Only an explicitly modelled byte-span constructor; no general allocation |
| Native integers | Partial | `nint`/`nuint` signatures, locals, fields, memory, casts, arithmetic and `sizeof` on validated 64-bit targets |
| Checked integer conversions | Partial | Integer inputs; signed/unsigned bounds, narrow extension and native-width destinations |
| Checked integer arithmetic | Partial | Signed/unsigned 32-/64-bit add, subtract and multiply; explicit overflow faults |
| Integer division and remainder | Partial | Signed/unsigned 32-/64-bit operands; explicit zero-divisor and overflow faults |
| All other opcodes | Unsupported | Includes `callvirt`, arrays and instruction prefixes |

The initial extraction target is Release, IL-only **.NET 10**, 64-bit little-endian execution. Supported scalar operations include 32/64-bit wrapping arithmetic, bitwise operations, shifts, selected conversions/comparisons, conditional/unconditional branches, local and argument loads/stores, 64-bit indirect access, and acyclic static managed calls. Explicit-layout reference-free aggregates use validated sizes and byte offsets; fields currently admit byte/Boolean, 32-bit integer and 64-bit integer storage. SIMD models cover selected Vector128/256, SSE, AVX, AVX2, AVX512, BMI and ARM operations, as enumerated in `CIL/SIMD` and `Extractor/RuntimeModels.cs`.

The extractor rejects unmodelled instructions, recursive/cyclic reachable control flow, exception handling, instance/virtual dispatch, value constructors for arbitrary layouts, managed object construction, reference-bearing aggregates, general arrays, implicit packing, floating-point arithmetic, arbitrary external calls, static constructors, and unsupported signatures. Not every combination of the model's standalone instructions is exposed by the extractor. New features require validation, semantics, proofs and regressions.

Profiles default to scalar. Pass a supported profile name or `@profile.json` as the final positional argument to `leancil extract`. Both `check` and `verify` recover the profile from the manifest. Capability prerequisites are validated. Instructions unreachable under that exact fixed profile are emitted as explicit unsupported placeholders; changing profiles invalidates artifacts.

The memory model checks allocation identity, liveness, bounds, byte permissions, initialization, alignment and GC-sensitive intervals. It supports overlap and distinct private frames. It does not prove JIT/compiler correctness, concurrency, GC implementation correctness, OS memory behaviour or arbitrary .NET runtime equivalence. See [soundness and trusted base](docs/SOUNDNESS.md) for the precise boundary.

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

## License

[MIT](LICENSE).
