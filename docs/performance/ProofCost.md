# Proof cost measurements

<!-- audience: maintainers -->

Use two measurements of the same tree to distinguish variation between runs from a change in
proof cost. The reports include the cost of each command and the total for its module.
[CI operation](../CI.md#proof-cost) defines the measures and thresholds;
[validation](../VALIDATION.md#proof-cost) gives the commands that compare a head with its base.

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

## Reading a difference

- Frontend heartbeats can vary by a few dozen on the same tree. CI flags an increase only
  when it exceeds both 5% and 50,000 heartbeats.
- Kernel heartbeats, proof-object counts and olean bytes are reproducible for identical sources,
  compiled imports and toolchain. Check the imports when a proof's cost changes with no edit
  to its source.
- Find the named declaration in the report to see how much it contributes to the module total.
  CI compares module totals when the base and head contain the same rows.
- Use the measurement step in the verification job log for elapsed time and the number of
  modules and commands measured. Module measurements overlap when multiple workers run.
  Elapsed time depends on runner load and does not decide the comparison.

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
