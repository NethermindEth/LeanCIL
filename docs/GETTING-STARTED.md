# Getting started

This walkthrough installs the `leancil` tool, verifies one method of the example assembly, shows
the same proof fail after the method is broken, and verifies that an invalid memory access cannot
succeed. The [CLI reference](CLI.md) has every command and option.

## Install

Install the Lean version in [lean-toolchain](../lean-toolchain) through elan and the .NET SDK in
[global.json](../global.json). The tool carries the framework sources and builds its own library
from them, so using it needs no `lake build` of this checkout.

Build and install the .NET tool from this checkout:

```sh
dotnet pack Extractor -c Release -o artifacts/packages
dotnet tool update --global Nethermind.LeanCIL --add-source artifacts/packages --prerelease
```

Each development pack is a new prerelease version, `0.1.0-dev.` and its UTC build time, so
rerunning both commands after a change replaces the installed tool. A release pack, given its
certified library descriptors, keeps the plain version.

## Verify a method

`Examples/Assembly/Methods.cs` includes:

```csharp
public static ulong Add(ulong x, ulong y) => unchecked(x + y);
```

Build the example, extract the method's CIL and verify the addition proof, which states that the
result equals `(x + y) mod 2^64` for every pair of 64-bit inputs:

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

The first `verify` on a machine builds and kernel-replays only the framework modules the proof
imports, reports its result, and then builds the whole certified library in the same command:
about 330 Lake jobs, which takes several minutes. Stderr reports [stage
progress](CLI.md#stage-progress). Later runs reuse the cached library and take seconds; a release
package downloads it instead of building it. See [library cache](CLI.md#library-cache) for its
location and integrity checks.

`extract` generates definitions, `check` validates extraction consistency, and `verify`
establishes the selected theorem about those definitions. Its guarantee is exactly the theorem's
statement, including its preconditions and quantifiers. `verify` reuses authenticated results of
unchanged inputs; `--fresh` bypasses that reuse and `--rebuild-library` also rebuilds the
library (see [verify](CLI.md#verify)).

List the methods of an assembly with `leancil list`. Check that generated files match the assembly
and extraction settings, without running Lean, with `leancil check`:

```sh run
leancil list Examples/Assembly/bin/Examples.dll
leancil check artifacts/Add
```

`Examples/Proofs/Add.lean` derives execution from the generated program for all inputs.
`Examples/Proofs/WrongAdd.lean` proves a counterexample to the addition contract for a subtracting
implementation, for every successful fuel budget.

## Break the implementation

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
before the tactic that failed; see
[goals of an unfinished proof](CLI.md#goals-of-an-unfinished-proof). The contract requires
addition for arbitrary inputs, so the subtraction implementation cannot satisfy this proof.

- `verification.json` is kept and `verified.json` is removed; `failed.json` holds the
  [failure report](CLI.md#failure-reports).
- To recover, restore `x + y` and repeat the three commands. The saved settings supply the proof
  and theorem.
- Running `check` after rebuilding but before extracting reports that the assembly has changed
  and tells you to extract again.

## Reject an invalid memory access

`PastEnd` advances a reference by one `ulong` and dereferences it. The example caller provides
only one eight-byte allocation, so the access falls outside it:

```sh run
leancil extract Examples/Assembly/bin/Examples.dll "Arithmetic::PastEnd(ulong&)" artifacts/PastEnd
leancil verify artifacts/PastEnd --proof Examples/Proofs/PastEnd.lean
```

This prints `Verified: ExampleProof.correctness` and the theorem statement: for every fuel budget
and result, execution with the example caller memory cannot return `Except.ok result`. The
verified property is **rejection of the unsafe access**. The theorem does not claim that the
method is safe. The proof also includes a concrete `.outsideAllocation` fault witness. Its caller
memory is fixed; the theorem does not claim the access fails for every possible allocation layout.

The commands and output on this page are run and compared by the repository's `docs` suite; see
[validation coverage](VALIDATION.md).

## Scope of a result

- A verification report identifies the **specific named theorem and its printed type**. It does
  not cover all methods or all inputs.
- Fuel exhaustion and unsupported states are failures. Neither counts as successful verification.

## Prove another method

1. Find the method's selector with `leancil list` and extract it into its own directory.
2. Run `leancil new-proof artifacts/Method Proofs/Method.lean` for a starting proof. It states the
   theorem, binds the entry and any loop, and leaves each decision as a commented `sorry`; see
   [start a proof](CLI.md#start-a-proof). Alternatively write a Lean file that imports
   `Extracted`, states a specification and proves it from `Extracted.program`.
3. Run `leancil verify artifacts/Method --proof Proofs/Method.lean --goals` to print the goal at
   each hole, fill the holes, then verify without `--goals`. `verify` checks
   `ExampleProof.correctness` unless `--theorem` names another theorem.

`CIL.Safety.Ensures` expresses total correctness with successful finite execution. `VC` and
`ensures_of_vc` expose a chosen finite execution condition. Simple concrete tests can use kernel
reduction (`rfl`); symbolic proofs use ordinary Lean reasoning or `cil_checked_steps` from
`CIL.Safety.SymbolicExecution`. [Writing proofs](PROOFS.md) describes the proof API, the
[examples](EXAMPLES.md) list complete proofs to start from, and
[consumer packages](CONSUMERS.md) covers proofs kept in your own Lake package.
