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

### Aggregate-return composition

Consumer `bac692a3bbbf25b0f8434204cb0cf3337ed06d6a` and
`f54f9591f0a3ace415aef70391113dab152c5900` were measured against the same compiled
framework closure at `645e21feec8a024fb8bcc3ac2e6cd97dd114a7ff`. The binary and unary
proofs in `UInt256.Safety.AggregateReturn` reuse `WP.enter`, `WP.of_prefix`, `WP.call`,
`WP.step` and `WP.returned`, together with existing argument-validation and invocation
certificate lemmas. They retain the helper's actual readback and outside-output cell
preservation guarantees; neither proof assumes `Confined`.

All 17 declaration statements are unchanged. Maintained source falls by five lines
(45 added, 50 removed), with no generated or upstream source added by this consumer edit.

| Measure for `UInt256.Safety.AggregateReturn` | Before | After |
| --- | ---: | ---: |
| Elaboration heartbeats | 6,086,577 | 5,954,780 |
| Kernel recheck heartbeats | 325,505 | 219,364 |
| Proof objects | 15,296 | 9,803 |
| `.olean` bytes | 569,736 | 376,312 |

The focused 163-job build passes with the same allowed axiom set. These measurements use
an explicit Lake package override to the compiled framework closure. The portable manifest
still names `c707f283` at these consumer commits, so these results are compilation and
proof-cost evidence, not final-pin certificates. Certificate wall time was not measured.
Raw paired reports and the command are retained under the consumer's
`verification/artifacts/aggregate-reuse/`, including `measurement-summary.json`.

## Relational WP and calling evidence, 10 November 2026

The comparison from `e6e792cc293f9c1ca9f69bc83b52689d642bfa36` to
`c89730f6daf54e31bfad25f20378e2185116e0f8` measures seven modules, with 466 baseline
rows and 484 head rows. All existing thresholds pass without waivers; no module is unmeasured.
The saved baseline measurements were reused. Elapsed times are not compared because other
builds shared the machine. All 544 library build jobs pass at the head with clean axiom checks.

| Module | Elaboration heartbeats, before → after | `.olean` bytes, before → after |
| --- | ---: | ---: |
| `Tests.Automation` | 79,813,703 → 79,813,837 | 2,019,840 → 2,019,840 |
| `Tests.CodeAt` | 10,211,461 → 10,211,434 | 349,904 → 349,904 |
| `Tests.FeatureExecution` | 2,591,708 → 2,591,681 | 108,576 → 108,576 |
| `Tests.MethodContract` | 46,316,761 → 46,832,385 | 1,227,208 → 1,232,720 |
| `Tests.StoreFacts` | 58,495,201 → 58,557,218 | 880,064 → 880,064 |
| `Tests.SimdCarryCalls` | 85,486,112 → 85,876,735 | 2,027,712 → 2,039,960 |
| `Tests.CallingFields` | 24,482,605 → 45,119,475 | 517,960 → 776,816 |

`CallingFields` adds 18 measured declarations/commands, including consecutive writes, supplied
write priority and wrapper forms. Its module totals therefore describe more proofs. The existing
`writes_after_reads` theorem, whose body now derives the store automatically, changes from
10,518,951 to 10,939,446 heartbeats (+4.0%). Its arbitrary-overlap contract is unchanged.

The SIMD fixture shares each proof between Add (`subtract = false`) and Subtract
(`subtract = true`). `caller_holds` retains five statement lines and five outer binders;
`stored_holds` retains three statement lines and one outer binder. Both counts are unchanged.
The statements keep the same preconditions, read-before-write ordering, arbitrary overlap and
confinement guarantees. This interface migration claims no statement-size reduction for them.

| Shared Add/Subtract proof | Elaboration heartbeats, before → after | Kernel heartbeats, before → after |
| --- | ---: | ---: |
| `caller_holds` | 4,029,114 → 4,163,083 | 147,475 → 148,744 |
| `stored_holds` | 4,969,202 → 5,055,840 | 124,586 → 126,212 |

The compiled-size measurement is the complete SIMD module in the preceding table; it is not
attributed separately to Add and Subtract. Negative helper, lane, overlap and alias controls
remain in that module. These may-alias fixtures require checked snapshots and write authority,
without imposing separation between inputs and outputs.

### Upstream source accounting

The upstream diff from merge base `13740081296a751b03344238ae0123fd8dfcbd0b` to
`c89730f6daf54e31bfad25f20378e2185116e0f8` covers 144 files. Counts are physical lines,
including declarations and comments, from `git diff --numstat`. This report itself is later
than that snapshot. Maintained examples are grouped with tests.

| Upstream category | Added | Removed | Net |
| --- | ---: | ---: | ---: |
| CIL production | 2,247 | 521 | +1,726 |
| C# production | 193 | 37 | +156 |
| Tests and proof examples | 3,143 | 158 | +2,985 |
| Documentation | 487 | 51 | +436 |
| Tooling, CI and build configuration | 500 | 43 | +457 |
| Generated/golden data | 68 | 12 | +56 |
| **Total** | **6,638** | **822** | **+5,816** |

The data category contains CLI JSON goldens, the self-admission baseline and scheduling
durations. No generated Lean or C# binding source changes. These upstream additions are
separate from the consumer pilots above; they do not establish a system-wide source reduction.
Raw reports are retained in `artifacts/int256/final-store-cost.json`,
`final-store-cost-comparison.json` and `final-source-accounting.json`.

### Positive proof composition

Commit `2acbb52e` replaces chosen success budgets in seven self-contained test modules with
existing structural rules and checked stepping. The comparison uses the same compiled
framework at `98afdd3f` for both sides: 515 baseline rows and 516 migrated rows, with no
unmeasured entries or threshold waivers. All seven modules pass. The additional row prints
the axiom set of the shared static-read body proof.

| Module | Elaboration heartbeats, before → after | `.olean` bytes, before → after |
| --- | ---: | ---: |
| `Tests.ConstructContract` | 29,031,710 → 29,409,095 | 1,131,640 → 1,123,872 |
| `Tests.ContractConsequence` | 36,228,019 → 36,546,871 | 1,899,776 → 1,896,224 |
| `Tests.Linking` | 15,532,447 → 15,584,488 | 444,656 → 439,728 |
| `Tests.ModularStatics` | 8,769,010 → 8,718,827 | 337,488 → 332,848 |
| `Tests.OutcomeContract` | 20,425,022 → 20,478,107 | 535,176 → 527,656 |
| `Tests.OutcomeEmbedding` | 15,283,267 → 15,337,856 | 419,384 → 417,640 |

`Tests.Imports.Calls.add_linked` reuses an explicit method lookup while stepping. Its
elaboration heartbeats fall from 3,239,882 to 3,131,981 and kernel heartbeats from 93,847
to 93,268. The seven-file migration adds 50 lines and removes 52; the public contracts
and deliberate fault/budget tests are unchanged.

The separate example migration at `761ca255` removes 18 chosen success budgets and six
manual success-budget forwarding adapters. It adds 96 lines and removes 47 across 18
examples and `Tests.LocalCalls`, so it is not a source-size reduction. Each changed example
passes a focused check against its extracted method. The LocalCalls comparison passes
124 measured rows; its mixed-frame proof changes from 12,298 to 10,968 kernel heartbeats
and from 1,279 to 881 proof objects. These are focused checks, not a replacement for CI.

The imported-caller migration at `4d63b371` uses existing `WP.enter`, `WP.step`, `WP.call`
and `WP.returned` rules in eight normal-return callers. The two-call proof obtains frame
well-formedness from the existing invocation preservation theorem. All eight statements
and their outer binders are unchanged. Together with two inferred success budgets in
`InvocationCertificates`, the nine-file edit adds 92 lines and removes 136. No library
implementation changes are part of this comparison.

All nine focused checks pass. The comparison measures 109 head rows against 108 baseline
rows at the same `98afdd3f` compiled framework; all thresholds pass without waivers.
Caller elaboration heartbeats fall by 4.7–10.4%. The two-call module's compiled size falls
17.7%; the other caller modules grow by 2.4–4.6%. The two echo proofs' elaboration
heartbeats rise 2.2%, while their kernel heartbeats rise 15.1% and 16.8%; removing their
explicit budgets therefore does not improve every cost measure. Raw reports are retained
in `artifacts/wp-callers-cost/` in the measurement checkout.

### Consumer mixed snapshots and wrappers

The following paired consumer measurements use the same compiled framework at
`98afdd3fc4845101a45aa1d80739db240f181210`. They measure separate source edits and module
sets; their totals are not summed. Each measured source passes focused elaboration with
the allowed axiom set. These results do not certify the integrated consumer revision or
establish a certificate wall-time improvement.

| Consumer edit | Maintained source delta | Elaboration heartbeats | Kernel heartbeats | `.olean` bytes |
| --- | ---: | ---: | ---: | ---: |
| Mixed Multiply snapshots, `d3546a5` | −19 | 22,893,241 → 22,307,079 | 2,030,151 → 1,991,674 | 1,464,064 → 1,333,872 |
| Add/Subtract two-home snapshots, `abff3fbf` | −11 | 143,994,446 → 143,766,178 | 14,908,188 → 14,810,876 | 11,962,200 → 11,679,704 |
| Six wrapper modules, `797bbaa` | −17 | 14,775,691 → 14,797,046 | 683,518 → 656,750 | 1,271,272 → 1,197,744 |

The mixed Multiply comparison starts at consumer `25756eb`. It replaces internal word
and vector state bookkeeping with existing `LocalSnapshots`; all four theorem headers
and `FullTopContract` are unchanged. Vector slots become known after their actual stores.
No live vector crosses the later helper call in this extracted path, so this case does
not demonstrate preservation of live vector contents across that call.

The Add/Subtract comparison starts at `a49814e`, which already includes the one-line net
compatibility prerequisite. Its net reduction includes the new 109-line consumer
`RippleState` module. The comparison measures eight baseline modules and nine head modules,
including the complete new shared cost.
The helper's actual two-output footprint remains explicit; output readback follows the
write, and unrelated snapshots require the existing footprint evidence. Four internal
storage-prefix statements change; the exported arithmetic and caller contracts do not.
This isolated measurement uses an explicit Lake package override to the framework above.

| Add/Subtract internal theorem | Statement lines | Outer named binders | Body lines |
| --- | ---: | ---: | ---: |
| `UInt256Proof.Add.Safety.vector128_sse_store_prefix` | 17 → 16 | 19 → 17 | 12 → 5 |
| `UInt256Proof.Subtract.Profile.subtract_repair_store_prefix` | 17 → 16 | 19 → 17 | 12 → 5 |

Each statement retains six existential names in its execution and continuation propositions.
The two quantified indices in the former slot/readback premises disappear, so the total
named binder count changes from 27 to 23. These are internal storage-prefix reductions;
they do not establish smaller full arithmetic specifications. The shared module's source
and checking cost are included in the preceding totals.

The wrapper comparison starts at `a1ba5c6`. Scalar, SSE and vector equality prefixes,
read-only and reporting forwarders, and the binary adapter reuse the existing consumer
helpers and WP rules. All 15 declaration headers are unchanged. The reporting helper's
exact tail budget remains part of its existing signature. Invocation certificates and
caller-cell preservation remain explicit; neither is promoted to `Confined`.

The mixed Multiply and wrapper measurements use a normal portable Lake git dependency.
All three consumer edits add zero upstream and generated-source lines. Their source
reductions are separate from the upstream additions reported above. Raw reports are
retained under consumer `verification/artifacts/mixed-snapshots/` and
`verification/artifacts/two-home-reuse/`, including the measurement summaries and paired
module reports.
