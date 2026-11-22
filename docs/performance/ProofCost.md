# Proof cost measurements

<!-- audience: maintainers -->

This page reports how far proof-cost figures move between runs of one tree, how clearly a real
cost increase shows, and how long measuring takes. Read it when a `Proof cost` comparison
reports a change and you need to decide whether it is noise.
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

## Reference figures

The figures were measured on Windows, on an AMD Ryzen 9 9950X with Lean 4.35.0 and
`--libraries --jobs 16`, with other builds sharing the machine. The workload is the 92 test
libraries of `lakefile.toml`: 4,859 rows and 2,411,059,442 heartbeats. Row and heartbeat totals
grow as tests are added.

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

## Reusing a wide vector equality contract

On Lean 4.35.0 the scalar-profile extractions of `EqualBytes256` and `EqualSigned512` each
load two arguments, call vector equality and return a Boolean. For each method the consumer
proves that zero compared with a vector containing only its highest bit returns false and
preserves arbitrary caller memory. Both proofs allow any sufficient fuel. The direct proof
supplies 16 and reduces the invocation. The other proof obtains the fuel, return value and
memory equality from the universal contract.

| Vector width | Proof | Frontend heartbeats | Kernel heartbeats | Proof objects | Elapsed ms |
| ---: | --- | ---: | ---: | ---: | ---: |
| 256 | Universal contract | 4,611,894 | 768,547 | 312 | 441 |
| 256 | Direct consumer | 2,744,041 | 767,330 | 129 | 276 |
| 256 | Consumer using contract | 73,207 | 6,015 | 535 | 11 |
| 512 | Universal contract | 5,608,075 | 978,331 | 312 | 536 |
| 512 | Direct consumer | 3,346,702 | 977,114 | 129 | 389 |
| 512 | Consumer using contract | 73,249 | 6,015 | 535 | 10 |

The universal contract incurs its kernel cost once per extracted method. At either width,
checking it once and using it twice costs fewer kernel heartbeats than reducing two such
invocations. The proof that uses the contract has more proof objects. The command-level
measurements use the proof-cost frontend described below. Elapsed times are from one run.

## Reusing a compiled field-read contract

The scalar-profile methods `Gates.Reader.Read` and `ReadPacked` read four bytes by reference.
The first reads an explicit-layout field at offset 8. The second reads a sequential field at
offset 2 with one-byte packing. Each contract accepts arbitrary initialized contents of a
24-byte caller allocation, grants read access only and requires the entire memory to remain
equal after the call. Deep verification checks both layouts against the pinned assembly.

The consumer sets the field's most significant byte to 128 and all other bytes to zero. It
proves that some fuel returns `0x80000000` with identical caller memory. The direct proof
supplies eight fuel and reduces the invocation. The proof using the contract obtains the fuel,
return and memory equality from the universal theorem. All measurements use Lean 4.35.0.

| Layout | Proof | Frontend heartbeats | Kernel heartbeats | Proof objects | Elapsed ms |
| --- | --- | ---: | ---: | ---: | ---: |
| Explicit | Universal contract | 3,737,167 | 1,246,785 | 49 | 337 |
| Explicit | Direct consumer | 3,501,647 | 1,249,312 | 91 | 293 |
| Explicit | Consumer using contract | 56,417 | 7,700 | 371 | 6 |
| Sequential | Universal contract | 3,700,831 | 1,232,107 | 49 | 318 |
| Sequential | Direct consumer | 3,465,669 | 1,234,634 | 91 | 297 |
| Sequential | Consumer using contract | 56,401 | 7,695 | 371 | 7 |

The universal theorem uses a shared contract-introduction lemma costing another 2,893 kernel
heartbeats for each layout. With that cost included, checking the contract once and applying
it twice uses fewer kernel heartbeats than reducing two reads for either layout. The table
gives command-level measurements after extraction. Image hashing and layout replay run separately.

A second fixture, `LayoutProbe.Reader`, compares the historical `CIL.Op` interpreter at
`27953edb` with canonical execution at `4d72d8c3`. The .NET 10 and .NET 11 builds produce
identical eight-byte method bodies for each reader, including the field token and tiny header.
Both interpreters use the same positive contract proof and consumer sources.

| Layout | Proof | CIL.Op kernel heartbeats | Canonical kernel heartbeats | Proof objects in both |
| --- | --- | ---: | ---: | ---: |
| Explicit | Universal contract | 62,159 | 1,276,911 | 49 |
| Explicit | Direct consumer | 64,722 | 1,279,438 | 91 |
| Explicit | Consumer using contract | 7,700 | 7,700 | 371 |
| Sequential | Universal contract | 62,159 | 1,261,729 | 49 |
| Sequential | Direct consumer | 64,722 | 1,264,256 | 91 |
| Sequential | Consumer using contract | 7,695 | 7,695 | 371 |

Direct reduction costs 19.8 times as many kernel heartbeats for the explicit field and 19.5
times as many for the sequential field. The universal proof incurs a comparable increase once
per layout. Applying it to the same caller memory costs exactly the same in both models.
The direct consumers took 24 and 25 ms to elaborate with `CIL.Op` and 291 and 279 ms with
canonical execution in single runs. The explicit contract application took 6 ms with each.

## Reusing the compiled Countdown loop contract

`Examples.Loops.Countdown(uint)` returns zero for every UInt32 input from empty entry memory.
Its proof uses the remaining unsigned count as a strictly decreasing measure. The consumer
proves normal return for inputs 4 and 16, either by reducing the compiled method or by
instantiating that universal theorem. The same consumer source runs against both models.
[Loop proof](../../Examples/Proofs/Countdown.lean) · [Consumer](../../Tests/LoopVariants/CountdownReuse.lean.in)

The baseline uses the `Op` interpreter from commit `27953edb` with its .NET 10 Release assembly. The
canonical extractor uses .NET 11. The two DLLs have identical 25-byte Countdown method bodies,
including all 13 instruction bytes, and identical local signature blobs. Each extractor selected
its own DLL. Lean 4.35.0 and the same proof-cost frontend measured both runs. Times below are
single-run elaboration times in milliseconds.

| Proof | Baseline kernel heartbeats | Canonical kernel heartbeats | Baseline proof objects | Canonical proof objects | Baseline ms | Canonical ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Universal loop theorem | 265,854 | 206,646 | 8,066 | 8,693 | 773 | 900 |
| Shared consumer lemma | 3,773 | 3,773 | 352 | 352 | 7 | 6 |
| Direct reduction, input 4 | 485,216 | 643,032 | 94 | 94 | 154 | 200 |
| Contract application, input 4 | 145 | 145 | 18 | 18 | 1 | 2 |
| Direct reduction, input 16 | 1,530,394 | 1,783,100 | 94 | 94 | 467 | 519 |
| Contract application, input 16 | 145 | 145 | 18 | 18 | 1 | 1 |

Direct canonical reduction costs 33% more kernel heartbeats at input 4 and 17% more at input
16. Each contract application costs 145 in either model. Including the entry and loop-header
facts, the universal proof module takes 344,696 kernel heartbeats on the baseline and 270,141
with canonical CIL. Its compiled size is 408,960 and 433,776 bytes respectively. The consumer
module is 25,808 bytes in both. Standalone kernel replay checked each extraction, proof and
consumer together.

To reproduce the comparison, extract `Examples.Loops::Countdown(uint)` under the scalar
profile in each checkout, use its loop proof as `Proof.lean` and the consumer above as
`Consumer.lean`. Use the frontend below to measure `Proof` and `Consumer` with that checkout's
compiled library and extraction on the Lean search path.

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
