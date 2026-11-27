# Performance

<!-- audience: maintainers -->

Use these commands to measure LeanCIL's proofs, library modules and CI artifacts.

| You are changing | Measure | Page |
| --- | --- | --- |
| Tactics, lemmas or anything proofs elaborate against | Heartbeats and olean bytes per proof | [Proof cost](ProofCost.md) |
| `cil_instruction_equations`, or the code list of emitted methods | Heartbeats per instruction as methods grow | [Instruction lookups](InstructionLookups.md) |
| A slow proof inside a `CIL/` module | Elaboration time of that module | [Proof work](ProofWork.md) |
| Packing or restoring the certified library | Archive bytes, pack and restore time | [Library distribution](LibraryDistribution.md) |
| Packing or restoring the Lean toolchain in CI | Archive bytes, compression and restore time | [Toolchain distribution](ToolchainDistribution.md) |
| Fold discovery in `CIL/Extraction/Folds.lean` | Kernel time of role discovery | [Fold discovery](#fold-discovery) |
| Constructor binding in `CIL/Runtime/Net11WinX64`, or how `cil_evaluated` writes a package | Kernel time of one bound extraction and its consumer proof | [Bound constructor packages](#bound-constructor-packages) |
| A test suite or its harness | Suite seconds | [Suite times](#suite-times) |

## Reading a measurement

- Compare heartbeats, olean bytes, kernel heartbeats and proof objects on the same toolchain.
  Frontend heartbeats can vary by a few dozen between runs of the same tree.
- Wall and CPU time depend on the machine and its load. Compare two times only when both were
  taken in one session on one machine with nothing else running, and repeat each at least once.
- Stage times inside a suite overlap (a fixture time includes its Lean calls), and modules
  compile concurrently. Do not add stage or module savings to predict a job's time.

## Scaling suites

Four suites fail when cost grows faster than the size of the input. Run one with
`dotnet run --file scripts/Test.cs -- --suite <name>`.

| Suite | Fails when |
| --- | --- |
| `lookups` | Heartbeats per instruction grow more than 1.15 times from about 500 to about 2,000 instructions, kernel heartbeats per array element address grow more than 1.15 times from 128 to 512 addresses, kernel heartbeats per instruction of the scalar certificate or closed argument storage of bodies of 128 to 512 loaded, addressed or `calli` pointer locals grow more than 1.25 times, kernel heartbeats per instruction of the feature certificate of local loads, stores and addresses grow more than 1.25 times from 256 to 4,096 instructions or from 16 to 256 locals at a fixed length, the feature certificate's cost grows more than 4.5 times as much from 16 to 64 known local facts as from 4 to 16, the kernel heartbeats of one native method table step or one load of its first entry at 64 or 256 entries exceed 1.15 times those at 16 entries, the kernel heartbeats per index of a load of its last entry grow more than 1.15 times from 16 to 256 entries, the kernel heartbeats per byte of the call check's method name clause or of a metadata name's encoding grow more than 1.15 times from 20 to 80 or from 80 to 320 bytes, the kernel heartbeats per call of an embedding grow more than 1.15 times at four times the calls, or the heartbeats per call site of the managed-call check grow more than 1.35 times at four times the call sites; see [instruction lookups](InstructionLookups.md) |
| `stepping` | Checked stepping exceeds its per-instruction growth budgets; see [validation](../VALIDATION.md#proof-cost) |
| `scaling` | The certificate of a six-method call graph exceeds the default heartbeat limit, kernel heartbeats per layout of the header struct layout check over nested or over generic structs, or of a method's layout check over nested structs, grow more than 1.5 times from 64 to 512 structs, or 512 structs of either kind do not check within 8 GiB |
| `excluded` | Certificates with hundreds of excluded and live sites exceed the default heartbeat limit |

## Suite times

`scripts/verification-durations.json` includes each suite's verification and verified-output
measurement on the hosted runner. The file records the source runs and how their times are combined.
Print the resulting jobs and their estimated minutes with:

```sh
dotnet run --file scripts/EstimateVerificationSchedule.cs -- --jobs
```

A job's summary and each suite's transcript report the suite's verification time; see
[CI operation](../CI.md).

## Gate and dispatch costs

Gate validation indexes comparison targets by profile and variant and follows each comparison
edge once. For *V* variants and *R* rows, this takes expected O(V + R) work.

The extractor validates a class's base chain once and returns its ancestors nearest first.
During a read-only layout pass, it indexes inherited and declared fields once per class
reference. For *F* fields and *A* slot requests, field enumeration and lookup take expected
O(F + A) work.

The strict-binding auditor checks the parent graph in one pass when parent rows precede their
children. In other row orders it records completed chain depths. If a chain fails validation,
the auditor follows the parent links to identify the cycle or invalid row.

The first virtual dispatch query for an owner builds a membership bitmap over the validated
graph. A balanced map bounds classification at O(n log n) for *n* physical rows. Subsequent
queries reuse the owner's bitmap. The auditor reads members in physical row order and checks
the target table at each reachable call site. Exact-class queries select the owner directly.

Run the gate and dispatch fixtures with these commands.

```sh
dotnet run --file scripts/Test.cs -- --suite gates
dotnet run --file scripts/Test.cs -- --suite dispatch
```

## Fold discovery

`docs/performance/fold-roles/ThrowScaling.lean` measures the kernel evaluating `foldRoles` on
4,096 message loads with no admitted throw fold. The statement uses `decide +kernel`;
[fold discovery](../VALIDATION-EXPORTS.md#fold-discovery) bounds the scan at each message load.

Build the imported module, then time the file:

```sh
lake build CIL.Extraction.Folds
lake env lean -Dprofiler=true docs/performance/fold-roles/ThrowScaling.lean
```

To check scaling, double the size (`4096`, at each occurrence in the file) in a scratch copy
and compare. The time should about double; a fourfold increase indicates an unbounded scan per
load. There are no reference figures for this file. The `lookups` suite checks addressed locals
with a failing limit.

## Bound constructor packages

A single caller whose throw is bound to a CoreLib constructor defines `boundPackage` with
`cil_evaluated`. The kernel evaluates the binding in `boundPackage_eq` and checks the package
rows in `Extracted.translation_valid`. Consumer proofs can read the checked literal through
`boundPackage`. Reducing `managedPackage` evaluates the binding again. See [proof binding](../PROOFS-BINDING.md).

After the `evidence` suite has written `artifacts/Throws/Percent`, time the extraction and its
boundary proof:

```sh
dir=artifacts/Throws/Percent
sep=:; [ "$OS" = Windows_NT ] && sep=';'
lake env lean -Dprofiler=true -Dprofiler.threshold=100 -o $dir/Extracted.olean $dir/Extracted.lean
lake env sh -c "LEAN_PATH=\"\$LEAN_PATH$sep$dir\" lean -Dprofiler=true $dir/BoundaryProof.lean"
```

### ItemPool.Rent

`ItemPool::Rent()` binds its caller to six CoreLib rows. The kernel checks equations for the
bound caller and runtime rows. The evidence, attribution and translation proofs read the
caller's original method, body and links from that checked value.

Run the pool suite to generate the extraction, then collect the per-command profile:

```sh
dotnet run --file scripts/Test.cs -- --suite pool
lake env lean -j1 --run scripts/ProofCost.lean Extracted \
  artifacts/ItemPool/Rent/Extracted.lean artifacts/ItemPool/rent-cost.json
```
