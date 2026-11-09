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
58 seconds summed. A CI job measures two trees, and a proof suite's job also verifies the suite
on both, so the job costs about twice the suite's own time plus these measurements.
