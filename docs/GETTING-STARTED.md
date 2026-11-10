# Getting started

Install the Lean version in [lean-toolchain](../lean-toolchain) through elan and the .NET SDK
in [global.json](../global.json). The tool carries the framework sources and builds its own
library from them, so using it needs no `lake build` of this checkout; that command is for
working on the framework itself.

Build and install the .NET tool from this checkout:

```sh
dotnet pack Extractor -c Release -o artifacts/packages
dotnet tool update --global Nethermind.LeanCIL --add-source artifacts/packages --prerelease
```

Each development pack is a new prerelease version, `0.1.0-dev.` and its UTC build time, so
rerunning both commands after a change replaces the installed tool instead of reusing a cached
package of the same version. A release pack, given its certified library descriptors, keeps the
plain version.

Prove that compiled addition returns the right result for every 64-bit input, change `+` to `-`, and see the same proof fail. This walkthrough also demonstrates a theorem that rules out successful execution of an invalid memory access.

`Examples/Assembly/Methods.cs` includes:

```csharp
public static ulong Add(ulong x, ulong y) => unchecked(x + y);
```

With the `leancil` tool installed, build the example, extract its CIL and verify the addition proof:

```sh run
dotnet build Examples/Assembly -c Release
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::Add(ulong,ulong)" artifacts/Add
leancil verify artifacts/Add --proof Examples/Proofs/Add.lean
```

`verify` prints:

```text stdout
Verified: ExampleProof.correctness
  Assembly: Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null
  Subject: System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64) (method 0) via CIL.Safety.invoke
  Extraction entry: System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)
  Proof: Examples/Proofs/Add.lean
  Axioms: propext, Quot.sound
  Settings: artifacts/Add/verification.json
  Report: artifacts/Add/verified.json
  Statement:
    ExampleProof.correctness (x y : CIL.W64) :
      ∃ result,
        Except.map Prod.snd
              (CIL.Safety.invoke Extracted.program 4 0
                [CIL.Safety.Value.scalar (CIL.Value.i64 x), CIL.Safety.Value.scalar (CIL.Value.i64 y)]
                CIL.Safety.Memory.empty) =
            Except.ok [CIL.Safety.Value.scalar (CIL.Value.i64 result)] ∧
          BitVec.toNat result = (BitVec.toNat x + BitVec.toNat y) % 2 ^ 64
  Lean messages (1):
    Examples/Proofs/Add.lean:15:0: info: 'ExampleProof.correctness' depends on axioms: [propext, Quot.sound]
```

`Subject:` is the method the theorem's conclusion is about and `Extraction entry:` the method the
extraction started from; see [reading the report](CLI.md#reading-the-report).

The first `verify` or `workspace` on a machine builds the certified library: it compiles every
framework module (about 330 Lake jobs) and kernel-replays all of them, which takes several
minutes. Stderr says so when the build starts and then reports the job count as
[stage progress](CLI.md#stage-progress) describes. The
library is cached in `LEANCIL_CACHE_DIR` (default `<local application data>/LeanCIL/libraries`)
under a key of the framework sources, toolchain and platform, and both commands reuse it, so
later runs take seconds. A release package downloads the library instead of building it.

Every invocation validates the request's identity and required proof evidence. Authenticated caches can reuse unchanged certified builds; source/hash checks, audits and required kernel replay still apply. Use `--fresh` to bypass proof and support reuse while retaining the source-bound library cache; add `--rebuild-library` to rebuild the library. Release packages can download a package-pinned certified library on first use, with independent integrity checks and kernel replay. A failed proof removes the previous verification report. `extract` generates definitions and `check` validates extraction consistency; `verify` establishes the selected theorem about those definitions. Its guarantee is exactly the theorem's statement, including its preconditions and quantifiers.

See [verification reuse and replay](CONSUMERS.md) for cache and audit details.

List the methods of an assembly with `leancil list`, and check that generated files still match
the assembly and extraction settings without running Lean with `leancil check`:

```sh run
leancil list Examples/Assembly/bin/Examples.dll
leancil check artifacts/Add
```

`Examples/Proofs/Add.lean` states the mathematical property independently: the returned word's natural value equals `(x.toNat + y.toNat) % 2^64`. Its universal proof derives execution from the generated program. Changing the implementation to subtraction causes the unchanged addition proof to fail. `WrongAdd.lean` independently proves a counterexample for every successful fuel budget.

### Try breaking the implementation

In `Examples/Assembly/Methods.cs`, change only `Add` to:

```csharp edit Examples/Assembly/Methods.cs
public static ulong Add(ulong x, ulong y) => unchecked(x - y);
```

Rebuild, regenerate the extraction, and run the unchanged addition proof:

```sh run fails
dotnet build Examples/Assembly -c Release
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::Add(ulong,ulong)" artifacts/Add
leancil verify artifacts/Add
```

Verification exits with `1`. Its diagnostic starts with:

```text stderr
Invalid: Lean could not prove the selected theorem.
  Stage: proof checking
  Next: Read the Lean diagnostic below and check the implementation against the stated contract, including its preconditions.
  Goals: add --goals to print the goal at each `sorry` and failing tactic.
```

The detailed Lean error follows. `leancil verify artifacts/Add --goals` also prints the goal
before the tactic that failed; see [goals of an unfinished proof](CLI.md#goals-of-an-unfinished-proof). The contract still requires addition for arbitrary inputs, so the subtraction implementation cannot satisfy this proof. `verification.json` remains; `verified.json` is removed. Restore `x + y`, then repeat the three commands to recover a successful verification without repeating the proof arguments. Running `check` after rebuilding but before extraction instead reports that the assembly has changed and tells you to re-extract.

### Reject an invalid memory access

`PastEnd` advances a reference by one `ulong` and dereferences it. The example caller provides only one eight-byte allocation, so the access falls outside it:

```sh run
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::PastEnd(ulong&)" artifacts/PastEnd
leancil verify artifacts/PastEnd --proof Examples/Proofs/PastEnd.lean
```

This prints `Verified: ExampleProof.correctness` and the theorem statement: for every fuel budget and result, execution with the example caller memory cannot return `Except.ok result`. Here the verified property is **rejection of the unsafe access**, not a claim that the method is safe. The proof also includes a concrete `.outsideAllocation` fault witness. Its caller memory is fixed; the theorem does not claim the access fails for every possible allocation layout.

The repository's `docs` suite runs this page's commands, with the edit, in a disposable source copy and compares what they print with the output shown here. The `cli` suite automates the addition edit/rebuild/failure/recovery sequence in a disposable source copy, then checks this invalid-access theorem. Its imported-helper checks reuse an authenticated compiled base when adding previously uncompiled sources. Each helper is still compiled, kernel-replayed and audited when imported; see [validation coverage](VALIDATION.md).

A verification report identifies the **specific named theorem and its printed type**, not all methods or all inputs automatically. `leancil check` validates extraction artifacts only; `leancil verify` runs the proof. A failed proof returns `1`, prints `Invalid:` and the diagnostic to standard error, and removes the previous verification report.

To prove another method, supply a unique method selector and extract it, then run `leancil new-proof artifacts/Method Proofs/Method.lean` for a starting proof: it states the theorem, binds the entry and any loop, and leaves each decision as a commented `sorry` that `verify` refuses until filled, and `leancil verify --goals` prints the goal at each; see [start a proof](CLI.md#start-a-proof). Otherwise write a Lean file importing `Extracted`, state a specification and prove it from `Extracted.program`. By default the driver checks `ExampleProof.correctness`; use `--theorem` for another name. `CIL.Safety.Ensures` expresses total correctness with successful finite execution. `VC` and `ensures_of_vc` expose a chosen finite execution condition. Simple concrete tests can use kernel reduction (`rfl`); symbolic checked-model proofs use ordinary Lean reasoning or `cil_checked_steps` from `CIL.Safety.SymbolicExecution`. Exhaustion and unsupported states are failures.
