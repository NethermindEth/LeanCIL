# Performance

<!-- audience: maintainers -->

How to measure the cost of LeanCIL's proofs, library modules and CI artifacts, with reference
figures to compare against. Read the page for the part you are changing before and after the
change.

| You are changing | Measure | Page |
| --- | --- | --- |
| Tactics, lemmas or anything proofs elaborate against | Heartbeats and olean bytes per proof | [Proof cost](ProofCost.md) |
| `cil_instruction_equations`, or the code list of emitted methods | Heartbeats per instruction as methods grow | [Instruction lookups](InstructionLookups.md) |
| A slow proof inside a `CIL/` module | Elaboration time of that module | [Proof work](ProofWork.md) |
| Packing or restoring the certified library | Archive bytes, pack and restore time | [Library distribution](LibraryDistribution.md) |
| Packing or restoring the Lean toolchain in CI | Archive bytes, compression and restore time | [Toolchain distribution](ToolchainDistribution.md) |
| Fold discovery in `CIL/Extraction/Folds.lean` | Kernel time of role discovery | [Fold discovery](#fold-discovery) |
| A test suite or its harness | Suite seconds | [Suite times](#suite-times) |

## Reading a measurement

- Heartbeats, olean bytes, kernel heartbeats and proof objects do not depend on machine load.
  Compare them between any two runs on one toolchain.
- Wall and CPU time depend on the machine and its load. Compare two times only when both were
  taken in one session on one machine with nothing else running, and repeat each at least once.
- Stage times inside a suite overlap (a fixture time includes its Lean calls), and modules
  compile concurrently. Do not add stage or module savings to predict a job's time.
- A local time does not predict a hosted runner's time. Use the suite times below for CI.

## Scaling suites

Four suites fail when cost grows faster than the size of the input. Run one with
`dotnet run --file scripts/Test.cs -- --suite <name>`.

| Suite | Fails when |
| --- | --- |
| `lookups` | Heartbeats per instruction grow more than 1.25 times from about 500 to about 2,000 instructions; see [instruction lookups](InstructionLookups.md) |
| `stepping` | Checked stepping exceeds its per-instruction growth budgets; see [validation](../VALIDATION.md#proof-cost) |
| `scaling` | The certificate of a six-method call graph exceeds the default heartbeat limit |
| `excluded` | Certificates with hundreds of excluded and live sites exceed the default heartbeat limit |

## Suite times

`scripts/verification-durations.json` holds the verification seconds of each suite on the hosted
runner, excluding job setup; its `source` field names the runs they came from. CI packs suites
into jobs from this table. Print the resulting jobs and their estimated minutes with:

```sh
dotnet run --file scripts/EstimateVerificationSchedule.cs -- --jobs
```

A job's summary and each suite's transcript report the suite's verification time; see
[CI operation](../CI.md).

## Fold discovery

Two files measure the kernel evaluating `foldRoles`, which
[fold discovery](../VALIDATION-EXPORTS.md#fold-discovery) keeps from scanning the whole body once
per local or per message load. Each proves its statement by `decide +kernel`:

| File | Workload |
| --- | --- |
| `docs/performance/fold-roles/CountScaling.lean` | 256 span locals, each stored once and loaded by address once before a receiver call; includes building the local-use index |
| `docs/performance/fold-roles/ThrowScaling.lean` | 4,096 message loads with no admitted throw fold |

Build the module they import, then time each file:

```sh
lake build CIL.Extraction.Folds
lake env lean -Dprofiler=true docs/performance/fold-roles/CountScaling.lean
lake env lean -Dprofiler=true docs/performance/fold-roles/ThrowScaling.lean
```

To check scaling, double the size (`256` or `4096`, at each occurrence in the file) in a scratch
copy and compare: the time should about double. A fourfold increase means a scan per local or per
load has returned. There are no reference figures for these files.
