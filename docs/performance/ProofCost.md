# Proof cost measurements

<!-- audience: maintainers -->

Measured on Windows, AMD Ryzen 9 9950X, Lean 4.35.0, with `scripts/ProofCost.cs` at 16 concurrent
modules while other builds shared the machine. Heartbeats, olean bytes, kernel heartbeats and
proof objects do not depend on that load; elapsed times do. [CI operation](../CI.md#proof-cost)
defines the measures and the thresholds these figures support.

## Noise of an unchanged tree

The 92 test libraries of `lakefile.toml` at main `469ea341` give 4,859 rows and 2,411,059,442
heartbeats. Two pairs of runs of that tree were compared with a 0% threshold:

| Pair | Rows whose heartbeats differ | Largest difference | Largest relative difference |
| --- | ---: | ---: | ---: |
| First | 90 | 36 | 0.0083% |
| Second | 92 | 19 | 0.0065% |

No olean byte, kernel heartbeat or proof object differed in either pair, and both comparisons
passed: the 50,000-heartbeat floor is three orders of magnitude above the largest difference.

One module's source elaborated from two different absolute paths gave identical heartbeats,
kernel heartbeats, proof objects and olean bytes. The hosted runner's noise is
reported by a manual run of the workflow, which measures its own tree twice.

## A merged change against its base

Main `469ea341` against its first parent `cec6df9b`, test libraries only: 4,859 rows at the head
and 4,852 at the base, and the comparison passes. The change added three theorems and a
definition to `Tests/LocalSnapshots.lean`, the largest at 806,062 heartbeats, so that module
went from 3,129,715 to 4,109,734 heartbeats and from 253,184 to 332,584 olean bytes. Its totals
are reported and do not fail, since the module gained rows. The largest change of any other row
is 205 heartbeats in 23,453,868, the total of a module that imports the changed library code.

## Sensitivity

A scratch copy of `Tests/CodeAt.lean` whose `run_sum_segment` proof runs `cil_checked_steps`
twice measured 2,350,930 heartbeats for that theorem against 1,259,640, and 4,559,316 for its
module against 3,467,823. The comparison failed on both rows and on nothing else; the other 29
rows of the module moved by at most 0.2%. Comparing the unchanged module with itself passed.

## Cost of measuring

One tree's 92 test libraries take about 180 to 200 seconds of wall time, and 309 seconds summed
over the modules, of which the kernel rechecks are 55 seconds. The 54 modules of 19 verified
output directories of the `loops` and `structoutlines` suites take 146 seconds of wall time and
58 seconds summed. A CI run measures only its own tree, in the jobs that verified it, so proof
cost adds these measurements to those jobs and one job that compares.

## Consumer reuse pilot, 10 November 2026

The int256 source comparison is `ee28ccb08ed9d57f473d4b6ff25911435dc5b752` to
`cad9918cca0d1e7848c7f56a6c62a218f84c3b87`; the narrowing tests end at
`a0ef8b6c01e563361b718e5247fcf0af90c837bc`. All proof-cost pairs use LeanCIL
`9a084079686ba4c5cb012a6c8f219ddc818cd70d`. Frozen sources before and after each
pilot were elaborated against compatible consumer dependencies on that same framework.
The cost totals aggregate these incremental pairs; they are not two complete consumer builds.

The measured modules reuse existing checked-call, calling-view, snapshot and weakest-precondition
APIs. Consumer arithmetic and public contracts remain intact. This historical pilot adds no
shared LeanCIL source; the larger PR adds shared features separately.

| Module | Elaboration heartbeats, before → after | Kernel recheck heartbeats, before → after | `.olean` bytes, before → after |
| --- | ---: | ---: | ---: |
| `UInt256.Safety.ReportingForwarder` | 4,705,314 → 3,419,846 | 416,210 → 137,133 | 640,696 → 218,848 |
| `UInt256.Safety.Calling` | 1,272,390 → 1,243,963 | 100,830 → 96,739 | 258,104 → 249,968 |
| `UInt256.Safety.OutputAccess` | 1,735,688 → 1,693,527 | 321,928 → 319,860 | 180,944 → 176,392 |
| `UInt256.Safety.CallerSetup` | 672,364 → 450,144 | 25,563 → 14,478 | 84,440 → 53,968 |
| `UInt256.Safety.PrivateCalls` | 733,072 → 677,600 | 25,191 → 22,428 | 79,744 → 78,296 |
| `UInt256.Methods.Compare.NativeEntrySafety` | 1,369,209 → 811,450 | 90,562 → 40,116 | 217,264 → 92,744 |
| `UInt256.Safety.ReadOnlyForwarder` | 1,716,885 → 1,559,112 | 81,339 → 70,745 | 217,232 → 198,024 |
| `UInt256.Methods.Multiply.Calls` | 1,030,431 → 963,339 | 38,350 → 34,756 | 164,272 → 148,608 |
| `UInt256.Safety.LocalCallSafety` | 1,542,551 → 1,505,633 | 135,659 → 133,747 | 329,072 → 317,504 |
| `UInt256.Methods.Add.PortableSmall` | 87,488,078 → 86,823,145 | 4,708,223 → 4,650,591 | 2,846,840 → 2,756,520 |
| `UInt256.Methods.Subtract.SmallHelper` | 46,115,620 → 45,988,473 | 2,298,462 → 2,261,938 | 1,304,480 → 1,246,056 |
| **Total** | **148,381,602 → 145,136,232 (−2.19%)** | **8,242,317 → 7,782,531 (−5.58%)** | **6,323,088 → 5,536,928 (−12.44%)** |

| Source scope | Net lines |
| --- | ---: |
| Maintained consumer proofs, compatibility edits and documentation | −51 |
| Dedicated incorrect-narrowing tests and coverage | +16 |
| Overall consumer delta | −35 |
| Generated production source | 0 |
| Shared upstream source added by these consumer pilots | 0 |

The Add/Subtract subset changes 11 declarations: statement lines fall from 191 to 166 and
body lines from 327 to 323. All 196 outer theorem parameters remain. There are 54 fewer
explicit existential binder-name occurrences and 18 new fuel-lambda binder occurrences;
the postcondition already has a name, so this subset adds no postcondition-lambda binders.
This removes 36 source binder occurrences, not logical quantifiers: unfolding `WP` recovers
definitionally equal propositions.

The measurement command, run from the consumer verification directory for each frozen source, is:

```text
lake env lean --run .lake/packages/leancil/scripts/ProofCost.lean <module> <source.lean> <report.json> <output.olean>
```

The raw paired module reports and saved source snapshots are retained under
`verification/artifacts/reuse-pilot/`. The summary inputs are `measurements.json` (reporting),
`shared-measurements.json` (six calling modules), `multiply-measurements.json` (two multiplication
modules) and `statements-measurements.json` (two arithmetic modules).
`consumer-pilot-measurements.json` combines their values. Source counts come from the commit
diffs and `statements-source-measurements.json`; `statements-outer-binders.log` records the
compiled outer parameter counts. These are local measurement artifacts, not published certificates.

These results do not establish a certificate wall-time speedup. Individual actual consumer
certificates and mutation rejection tests were checked separately. The complete final consumer
matrix and a merged LeanCIL dependency pin remain separate acceptance requirements.

### Checked local-call steps

A second local-call comparison uses consumer `3a2d31d8e981acebaf25e6b183f28b75dada6172`
and `8dd16e2ebca83172f3b1151d78c12459913a45c7`, both against framework
`c707f283804247932dc1907603701164019f3b06`. In module
`UInt256.Safety.LocalCallSafety`, the proof of `UInt256Model.Safety.run_local_word_call` uses
checked stepping for the local-address and call-step equations. Its statement and axiom set
are unchanged.
The source delta is ten fewer maintained lines, with no generated or upstream source added
by this consumer change. At this pin, the local-address step still explicitly supplies
`localAddress` alongside its slot and formation facts.

| Measure for `UInt256.Safety.LocalCallSafety` | Before | After |
| --- | ---: | ---: |
| Elaboration heartbeats | 1,506,101 | 1,304,089 |
| Kernel recheck heartbeats | 133,747 | 106,693 |
| `.olean` bytes | 317,616 | 224,816 |

Both sources were measured against a freshly rebuilt dependency closure with the command
above. The six affected Multiply method/profile certificates pass at these exact consumer
and framework pins, with verified receipts and only allowed axioms. Other production gates
were not rerun for this support edit. There is no paired certificate-time measurement.
Raw measurements and receipt summaries are retained in the consumer's
`verification/artifacts/local-step-reuse/measurement-summary.json` and
`certificates-summary.json`. This comparison uses a different framework pin from the earlier
table and is not added to its heartbeat or compiled-size totals.
