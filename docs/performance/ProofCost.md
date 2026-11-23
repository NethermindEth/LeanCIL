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

For a matched comparison, .NET 10 and .NET 11 compiled the two equality methods alone in
a Release assembly. Each method has the same nine bytes in both builds, including its tiny
header, call token and return. Neither method has locals. The baseline uses the CIL.Op
interpreter at `27953edb`. Both models check identical contract and high-bit consumer sources
at each width. The resolved-call proof uses the runtime-model theorem generated for instruction
2, the equality call between the two argument loads and the Boolean return.

| Width | Proof | Baseline kernel heartbeats | Canonical kernel heartbeats |
| ---: | --- | ---: | ---: |
| 256 | Universal contract by reduction | 69,974 | 768,551 |
| 512 | Universal contract by reduction | 70,058 | 978,335 |
| 256 | Direct high-bit consumer | 68,879 | 767,246 |
| 512 | Direct high-bit consumer | 68,963 | 977,030 |
| 256 and 512 | Consumer using the contract | 6,013 | 6,013 |

Using the checked call resolution costs 186,226 kernel heartbeats for the 256-bit universal
proof and 186,310 for the 512-bit proof. Both proof terms have 773 objects, compared with
312 for direct reduction. The canonical elaboration times in this run were 118 and 129 ms
with the call theorem, compared with 350 and 414 ms by reduction. The production equality
fixtures use the call theorem and check a compiled second-load substitution at each width.

## Reusing an AVX2 AND-NOT contract

The x64-v3 extraction of `Examples.DivisionIntrinsics.AndNot` broadcasts two 64-bit words,
applies AVX2 AND-NOT and returns lane three. The contract covers every pair of words and
preserves the caller's memory. The .NET 10 assembly at `27953edb` and the .NET 11 assembly
at `97b318f7` have the same MethodDef token, complete tiny method body (24 IL bytes) and
empty local signature. Lean 4.35.0 checked both extractions.

| Interpreter | Proof | Frontend heartbeats | Kernel heartbeats | Proof objects | Elapsed ms |
| --- | --- | ---: | ---: | ---: | ---: |
| Base | Universal contract | 67,714 | 4,355 | 273 | 7 |
| Canonical at 97b318f7 | Universal contract | 1,674,992 | 477,046 | 361 | 145 |
| Canonical with literal broadcast signature | Universal contract | 494,340 | 130,729 | 361 | 42 |
| Canonical with checked primitive signature | Universal contract | 101,316 | 6,280 | 401 | 8 |
| Base | Direct witness | 719,384 | 141,620 | 97 | 62 |
| Canonical | Direct witness | 4,727,138 | 1,216,915 | 97 | 437 |
| Base | Consumer using contract | 59,649 | 6,157 | 511 | 6 |
| Canonical | Consumer using contract | 59,636 | 6,157 | 511 | 8 |

The witness uses inputs one and two and returns two in unchanged memory. Direct reduction
uses 16 fuel. The other consumer instantiates the all-input contract at the same words and
memory. Both modules passed standalone kernel replay. On the canonical model, proving that
the extracted body has the broadcast helper's method shape took 366,114 kernel heartbeats
in isolation. Comparing just the broadcast member with the name formatted from its width
cost 363,912 kernel heartbeats. Using its literal metadata name took 2,119. The optimized
contract uses the same 361 proof objects and retains the 6,157-heartbeat consumer. Stepping
the four resolved call sites separately took 194,168 kernel heartbeats, 9,079 proof objects
and 648 ms of elaboration.

Reducing the return-width premise for the extracted UInt64 costs 122,105 kernel heartbeats.
The two argument-width premises cost 123,348 and 123,713 when checked separately. These
counts overlap in the full proof. Both AVX2 AND and AND-NOT use one checked fact about the
static method signature. The result and both arguments have the same primitive narrowing for
any layout table. With the original AND-NOT instructions, the full proof takes 6,280 kernel
heartbeats, and its consumer still takes 6,157. Lean replayed the measured module against the
395-module certified library. The independent AVX2 AND contract drops from 130,609 to 6,074
kernel heartbeats with the same signature fact. Its proof grows from 352 to 391 proof objects.


## Reusing an in-place vector swap contract

On Lean 4.35.0, the `arm64-advsimd` extraction of `DivisionIntrinsics.SwapHalves` exchanges
two 16-byte halves of one writable buffer. The contract covers every initial byte pattern.
The following runs use the base at
[27953edb](https://github.com/NethermindEth/LeanCIL/commit/27953edb) and the canonical interpreter.
The two Release assemblies target .NET 10 and .NET 11 respectively. All 19 instruction offsets,
opcodes, resolved operands and local signature bytes agree. The six generic calls have different
MethodSpec row numbers in the two assemblies.

Only input byte 16 is set for the consumer proofs. Both require output byte zero to equal one
for some sufficient fuel. The direct proof reduces the invocation. The other applies the
universal contract. Append the [consumer proofs](../../Tests/HalfSwapCost.lean.in) to the original
half-swap proof from [the intrinsics fixture](../../Tests/ExactIntrinsics.cs) and measure that
module with the proof-cost driver. Both modules passed standalone kernel replay. The legacy
frame includes an empty argument-home list in the intermediate state.

| Interpreter | Proof | Frontend heartbeats | Kernel heartbeats | Proof objects | Elapsed ms |
| --- | --- | ---: | ---: | ---: | ---: |
| Base | Direct consumer | 1,982,309 | 550,666 | 98 | 143 |
| Canonical | Direct consumer | 5,621,328 | 1,684,575 | 98 | 432 |
| Base | Consumer using contract | 87,678 | 4,929 | 387 | 7 |
| Canonical | Consumer using contract | 87,670 | 4,929 | 387 | 10 |

Proving the four execution regions once costs 761,169 kernel heartbeats on the base and
3,545,916 on canonical. The same composition with the footprint and byte-order proofs costs
4,614 on each interpreter. The direct consumer costs 3.06 times as much on canonical.
Applying the universal contract costs the same on both.

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

A second fixture, `LayoutProbe.Reader`, compares the interpreter at
[27953edb](https://github.com/NethermindEth/LeanCIL/commit/27953edb)
with canonical execution at `4d72d8c3`. The .NET 10 and .NET 11 builds produce
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
The direct consumers took 24 and 25 ms to elaborate on the historical revision and 291 and 279 ms with
canonical execution in single runs. The explicit contract application took 6 ms with each.

The explicit `LayoutProbe.Reader` resolves its field to offset 8 and width 4 in 1,218,000
kernel heartbeats. Checking the owner against the indexed raw layout accounts for 1,106,363
of those heartbeats when measured separately. Extraction already proves the field shape once.

The `Gates.Reader` proofs can apply that shape theorem at the field load and compose the
argument load, field load and return. The following costs exclude the extraction and measure
the reusable execution lemma plus the final contract statement. Both negative cases use the
same contract as their original and return zero on the byte pattern that requires 128.

| Layout and outcome | Execution lemma, kernel heartbeats | Final theorem, kernel heartbeats | Combined elaboration, ms |
| --- | ---: | ---: | ---: |
| Explicit, verified contract | 168,181 | 297 | 72 |
| Sequential, verified contract | 177,298 | 299 | 82 |
| Explicit, refuted contract | 168,177 | 3,670 | 77 |
| Sequential, refuted contract | 177,262 | 3,675 | 76 |

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

## Decoding an ordinary string load

Both certified libraries checked the same reflexivity proof that opcode 114 decodes to
`ldstr` of its operand. Each operand was a named ASCII string literal. The counts cover kernel
checking of that decoding equation. Checking the physical UTF-16 bytes in the assembly's
`#US` heap is separate work.

| Literal length | With the character filter | Without the filter |
| ---: | ---: | ---: |
| 8 | 31,296 | 13,463 |
| 32 | 74,841 | 13,352 |
| 128 | 249,465 | 13,352 |
| 512 | 947,963 | 13,352 |
| 2,048 | 3,741,953 | 13,352 |

The counts are raw kernel heartbeats. The decoder accepts every Lean string, so the same
reflexivity proof also checks for a symbolic operand of arbitrary length.

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
