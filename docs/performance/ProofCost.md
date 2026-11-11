# Proof cost measurements

<!-- audience: maintainers -->

How far proof-cost figures move between runs of one tree, how clearly a real cost increase
shows, and how long measuring takes. Read it when a `Proof cost` comparison reports a change and
you need to decide whether it is noise. [CI operation](../CI.md#proof-cost) defines the measures
and thresholds; [validation](../VALIDATION.md#proof-cost) gives the commands that compare a head
with its base.

## Measuring the noise of a tree

Measure one tree twice and compare the two reports with a 0% threshold, so every difference is
listed:

```sh
dotnet run --file scripts/ProofCost.cs -- measure --tree . --libraries --output artifacts/cost/first.json
dotnet run --file scripts/ProofCost.cs -- measure --tree . --libraries --output artifacts/cost/second.json
dotnet run --file scripts/ProofCost.cs -- compare --base artifacts/cost/first.json \
  --head artifacts/cost/second.json --threshold-percent 0
```

`--jobs <count>` sets how many modules are measured at once; `--module <name>` measures one
module and the checkout modules it imports instead of every test library. A manual run of the
verification workflow on a commit main has published reports the same comparison for the hosted
runner.

## Reference figures

Windows, AMD Ryzen 9 9950X, Lean 4.35.0, `--libraries --jobs 16`, with other builds sharing the
machine. The workload is the 92 test libraries of `lakefile.toml`: 4,859 rows and 2,411,059,442
heartbeats. Row and heartbeat totals grow as tests are added.

| Between two runs of one tree | Figure |
| --- | ---: |
| Rows whose heartbeats differ | 90 to 92 of 4,859 |
| Largest heartbeat difference of a row | 36 |
| Largest relative difference of a row | 0.0083% |
| Olean bytes, kernel heartbeats or proof objects that differ | 0 |

| Cost of measuring | Seconds |
| --- | ---: |
| 92 test libraries, wall time | 180 to 200 |
| 92 test libraries, summed over modules | 309 |
| Kernel rechecks within that sum | 55 |
| 54 modules of 19 output directories of `loops` and `structoutlines`, wall time | 146 |
| The same 54 modules, summed over modules | 58 |

One source elaborated from two different absolute paths gives identical heartbeats, kernel
heartbeats, proof objects and olean bytes, so a base checkout in another directory is comparable.

## Reading a difference

- A row that moves by a few dozen heartbeats is noise. The 50,000-heartbeat floor of the
  comparison is three orders of magnitude above the largest difference between reruns.
- Any olean byte, kernel heartbeat or proof object that differs comes from a change to the
  sources or the toolchain, never from a rerun.
- A change to code that a module imports moves that module's rows slightly: 205 heartbeats in a
  module total of 23,453,868 in one measured case.
- A real cost shows on its own row. A scratch copy of `Tests/CodeAt.lean` whose
  `run_sum_segment` proof runs `cil_checked_steps` twice measures 2,350,930 heartbeats for that
  theorem against 1,259,640. The comparison fails on that theorem and on its module total and
  on no other row; the other 29 rows of the module move by at most 0.2%.
- Elapsed times depend on load and never decide a comparison.

## Measuring one module of another package

The frontend runs without the C# driver, from any Lake package that depends on LeanCIL. From the
package directory:

```sh
lake env lean --run .lake/packages/leancil/scripts/ProofCost.lean <module> <source.lean> <report.json> <output.olean>
```

`<module>` is the module name of `<source.lean>`, `<report.json>` receives one row per command
and one for the module, and the optional `<output.olean>` receives the compiled module. The
package's dependencies must be built first. To compare two versions of a source, measure both
against the same compiled dependencies. The frontend does not certify a proof; an error in any
command makes the module unmeasured.
