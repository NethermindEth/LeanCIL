# Contract export and consumer validation

## Export suite selection

`dotnet run --file Tests/ContractExport.cs` runs every export cohort once. `dotnet run --file
scripts/Test.cs -- --suite all` runs the same export leaves once with the other suites. Each export
leaf has a fresh SDK and proof workspace. Full verification keeps fresh extraction, source audit,
independent kernel replay, and all report and artifact checks.

Run one leaf with `dotnet run --file scripts/Test.cs -- --suite NAME`:

| Name | Cases |
| --- | --- |
| `exports` | Production, wrapper-True rejection, generic/virtual/static-value restrictions and caller reuse |
| `exportsprotected` | SDK-built protected static export, separately compiled derived caller and rehashed visibility mismatch rejection |
| `exportsaudit` | Proof-source and compiled-wrapper callback mutations |
| `exportsresolution` | Same loaded files and changed loaded module |
| `exportsfullconsumer` | Explicit and repeated consumer full verification; stale-report removal; caller and library proof-build stages required separately for each invocation |
| `exportsfullordinary` | Ordinary caller full verification, requiring its direct proof check and the imported proof build |
| `exportsfullpair` | Two imported slots from one bundle, requiring both imported proof builds and the caller check |
| `exportsfullchecks` | Bundle, DLL, closure, statement digest and caller-premise rejection |
| `exportsfulltheorems` | Wrong producer theorem statement and definition |
| `exportsfullcomposition` | Transferred macro cannot replace the composition theorem with True |
| `exportsmutationordinary` | Executed ordinary caller artifact mutation |
| `exportsmutationconsumer` | Executed consumer caller artifact mutation |
| `exportsmutationsource` | Executed consumer caller source mutation |
| `exportsmutationshadow` | Executed original-root module shadow |
| `exportsstatics` | Standalone modular static exports with their own SDK setup and existing assertions |
| `exportsfullstatics` | The same fixture with `--full-composition`: forced full verification of app and library tables with one local index and one table shared by two imported slots, run after a repeated ordinary verification restored a receipt; a republished bundle with forged static records fails in preflight and a re-certified changed table fails the independent library proof; a Top → App → library chain independently composes the table reader with its static-world premise |
| `exportstransitive` | App → A → B and a four-node diamond where A and C share B; full mode rechecks each selected export despite warm receipts, rejects changed deployment pins and cycles before building, rejects forged dependency composition, and detects B changing staged A before A builds |
| `exportstransitiveoutcomes` | App → C → A → B independently preserves normal returns and the named exceptional outcome through three forwarders |
| `exportsdiscovery` | Real producer SDK/publication bootstrap, then the unchanged six-argument discovery fixture |
| `exportstyped` | Standalone closed-generic and imported-layout fixture with its own SDK setup and existing assertions |
| `exportsderived` | Standalone derived public contracts: `Holds.weaken` exports, sidecar-only callers, refuted weakenings |
| `exportsinitialized` | A static-readonly struct library exports a named initialization premise; its caller retains the scoped premise, malformed descriptors reject, and full verification remains unavailable |
| `exportsprofiles` | One family theorem across three profiles, independent full composition, outcome families and scoped initialization premises; disagreeing flags, unequal programs, malformed selections, forged audit declarations and compiled-reference mutation reject |

The base coverage ledger has 49 cases: 22 core, 3 protected, 2 callback, 2 resolution and 20 full
cases. Each leaf rejects an omitted, repeated or unexpected completion. The artifact-mode rejection
follows real consumer positives so it still checks removal of an actual successful report. The
default eight-argument `Tests/FullImportVerification.cs` invocation runs resolution and all full
cohorts once. Its optional `--cohort NAME` selects one full cohort. Unknown, missing or duplicate
selections fail before fixture setup. The full plan contains only its ten explicit base cohorts.
Later standalone statics, fullstatics, transitive, transitiveoutcomes, discovery, typed, derived,
initialized and profiles suites cannot enter that plan. The registry has 23 leaves.
`exportsstatics`, `exportsfullstatics`, `exportstransitive`, `exportstransitiveoutcomes`,
`exportstyped`, `exportsderived`, `exportsinitialized` and `exportsprofiles` run directly, with no
core export bootstrap or nested post-call. Their fixture assertions are separate from the 49 base
case IDs. A standalone fixture cannot use an empty base completion ledger to claim coverage.
`exportsdiscovery` records one separate `discovery.fixture` completion after the actual child
succeeds. It does not count individual child behaviors in the 49 base cases. It builds the producer
library and creates real proof packages and publication. The child builds, extracts and verifies its
own caller. It needs no baseline caller artifact or verified report. The discovery leaf runs no core
caller verification, restrictions, callbacks or full cases. The typed leaf explicitly owns its
fixture and five input proof/interface modules. Shared model and proof dependencies retain their
existing owners. The derived leaf likewise owns its fixture and the five `Derived*` interface,
producer and caller modules in `Tests/ContractImports`. It proves exact internal method and outcome
contracts on the actual extraction and exports public ones derived only through `Holds.weaken`.
Callers verify from the sidecar alone, on normal and named-exception paths. Stronger posts, weaker
preconditions, smaller footprints and renamed exceptions are refuted on the same extraction; at the
exporter, one renamed exception fails only its refinement proof.

New cohort durations are unmeasured. The existing CI caps remain 90 minutes for imports, 120 for
each exports leaf, and 30 for other suites. The matrix still uses at most eight runners. Run the
resource-bounded routing tests with `dotnet run --file scripts/TestSelectVerification.cs`; they need
no Lean build or fixture SDK project. Full integration results come from the CI leaf jobs.

`Tests/PointerOperations.cs` compares seven compiled pointer methods with .NET: int32/native byte
subtraction, pointer differences and four unsigned orderings. It independently forges subtraction as
addition and requires the Lean scalar certificate to reject it. The Lean fixtures cover negative
offsets and differences, end positions, readonly preservation, every unsigned branch, and null,
cross-allocation, invalid-position and signed-comparison rejection.

Managed-call proof construction is covered by `Tests/ExtractionGenerics.lean` and the 15 generated
generic-method samples in `Tests/GenericEvidence.cs`. Direct tactic rejection checks cover changed
signedness, assembly scope, generic arguments and argument count. The fixed three-method int256
scalar Equality extraction retains every public certificate proposition and all program/metadata
definitions. Replaying every generated theorem reduces kernel work from 36,782,462 to 32,494,315 raw
heartbeats (11.7%); the structural proofs introduce additional auxiliary theorems, increasing the
replay count from 169 to 181. These are kernel work measurements, not full consumer build or
end-to-end verification timings.

Shared runtime-scope encoding keeps the same 181 Equality theorems and reduces their replay from
32,494,315 to 26,201,571 raw heartbeats (19.4%). Including all 43 generated data definitions and the
changed scope definition plus its equality theorem gives 32,502,723 versus 28,123,894 raw heartbeats
(13.5%). The latter includes the one-time scope construction and equivalence cost. Actual extractor
output matches the measured source. Generic evidence mutations also reject altered runtime versions
and public-key tokens; no scope comparison is relaxed.

`Tests/GenericEvidence.cs` also checks exact external-call identity sharing, repeated emission,
pruned-only identities and Unicode/escaped characters. Changed bytes, versions and tokens fail the
generated equality proof. Replacing a raw target with another correctly encoded identity, or
changing its emitted intrinsic, still fails the unchanged division certificate. Existing
specialization and raw/translated metadata rejection cases remain enabled.

External-call byte sharing was measured against the parent extractor on fixed compiled inputs. The
following counts replay every generated definition, theorem and auxiliary proof, including all new
byte constants, UTF-8 proofs and exact equality proofs:

| Fixed input | Before raw heartbeats | After raw heartbeats |
| --- | ---: | ---: |
| int256 scalar Equality, three methods | 26,209,754 | 21,765,190 |
| `DivisionIntrinsics.UnsafeEquals`, x64-v3 | 28,184,308 | 22,519,141 |
| `VectorFields.Reinterpret`, x64-v3 | 15,047,351 | 14,850,377 |
| `Arithmetic.Add`, scalar, no calls | 1,397,796 | 1,397,796 |
| Feature getter only, scalar | 12,688,673 | 8,715,896 |
| `UnsafeLow` through one managed caller, scalar | 25,337,727 | 20,917,175 |
| Eight different division intrinsic helpers, x64-v4 | 379,503,016 | 257,862,158 |

The last input calls `And`, `Or`, `Xor`, `AndNot`, `ShiftLeft`, `ShiftRight`, `Less` and `Greater`
once each and sums the results. Its nine-method extraction has thirteen unique external identities,
including eight operator identities used only once. Counts include the new declarations (582 before,
647 after); sharing does not require repeated source call sites. Source checking and independent
kernel replay both pass. These are deterministic kernel-work measurements, not isolated wall times
or end-to-end consumer verification improvements.

The core `Tests/AllocationImports.cs` fixture checks that the CIL umbrella omits allocation
refinement, builds both explicit allocation acceptance modules, and jointly replays every additional
imported module. The current closure contains 49 production and two test modules; all remain
mandatory checks while ordinary consumers avoid loading their 197 MiB of oleans. The compiled
namespace audit checks their theorem axiom closures even on warm builds and binds the audited paths
and module bytes to those replayed. An isolated theorem depending on `sorryAx` passes kernel replay
but must fail that audit; build output is also checked.

Extraction bookkeeping indexes declaration names, imported assembly identities, imported call slots,
batch proof modules and aggregate layout names. Component imports retain declaration order; raw
layout positions and emitted layout constant positions have separate indexes.
`Tests/ConsumerSupportCandidates.cs` checks dependency ordering and conservative references in
literal text, while `Tests/InstructionIndexes.cs` checks nested layout ordering and absent types.
The transitive import regression also checks identical imports before rejecting ambiguous versions.

On the Apple M4 with .NET 10.0.401, splitting synthetic one-dependency method chains took these
median times over seven warmed runs, including index construction and component hashing:

| Methods | Declaration scans | Indexed dependencies |
| --- | ---: | ---: |
| 128 | 1.23 ms | 0.46 ms |
| 512 | 13.79 ms | 1.94 ms |
| 2,048 | 113.59 ms | 6.46 ms |

Each input contains two declarations per method and refers to the previous method's value. Both
implementations produced identical component sources and aggregate imports. A separate 24-request
extraction matrix (eight entries across scalar, x64-v3 and arm64-advsimd profiles) retained all 48
generated Lean file hashes. These measure component splitting and output stability, not end-to-end
proof or CI speedups.

The certificate successor index consumes the source list once to build its balanced tree, replacing
repeated length/take/drop traversals. `Tests.FlowIndex` covers empty and singleton inputs, odd/even
partitions, missing certificate states, out-of-bounds lookups and untouched suffixes.
`FlowIndex.build_spec` proves prefix consumption and exact list lookup equivalence.

`Tests/FlowIndexScaling.lean` retains the list-based builder as a benchmark reference. It constructs
indexes and checks every target in reverse order, including the first out-of-bounds position, using
`decide +kernel`. On Apple M4 with Lean 4.35.0, leanprof measured these theorem-checking heartbeat
counts (kHB); they include elaboration and kernel checking, not whole-suite timings:

| Entries | Repeated list splitting | Consuming builder |
| --- | ---: | ---: |
| 128 | 1,019.05 | 654.46 |
| 512 | 4,749.06 | 2,907.29 |
| 2,048 | 21,825.45 | 12,951.03 |

These fixed workloads reduce checking work by 36–41%. Tree construction is linear in list cells;
arbitrary target lookup remains logarithmic. The existing feature and scalar validators continue to
use the same proved optional-lookup interface.

The shared state-pairing proof also uses explicit list-shape cases instead of broad simplifier
search. Its statement is unchanged, and its checked axiom set is reduced to `propext`.

Region closure builds an ordered map of each method's minimum starting pc, visits program methods
sequentially, and checks each included body once. It skips absent region entries and preserves
region membership for absent callees: execution validity is a separate obligation. The equivalence
theorem covers the list-based specification exactly, including duplicate starts and out-of-range
pcs. `Tests.RegionRun` exercises those cases; `Tests/RegionScaling.lean` is a standalone
before/after workload for `leanprof elab --heartbeats`.

On Apple M4 with Lean 4.35, kernel-decision declaration work for a single full-method region:

| Nops before return | Former checker (kHB) | Indexed checker (kHB) |
| --- | ---: | ---: |
| 128 | 2,674.46 | 214.01 |
| 512 | 38,908.36 | 742.40 |
| 2,048 | 608,701.24 | 2,855.94 |

Measurements include index construction. They show the removal of quadratic instruction lookup; they
do not estimate total CI savings. The separate `all3_zip_states` proof cleanup reduces declaration
work from 97,195.29 to 589.64 kHB on the same machine, without changing its statement. Its axiom set
shrinks to `propext`. Constrained validation uses balanced instruction/reachability indexes and a
set of all decoded branch destinations, including unreachable instructions and switch arms. The
following constrained lowering pass also indexes predecessor instructions;
`lowerConstrainedRaw_eq_original` proves identical output for arbitrary raw bodies, including
malformed prefixes. Managed-call validation indexes both extracted methods and imported slots once
per method check. The equivalence theorems `ConstrainedCallsValid_iff_original` and
`ManagedCallsValid_iff_original` preserve the original list-based rules, including absent entries,
import offsets and malformed lengths. `cil_managed_calls` still uses structural metadata equalities
before its kernel-decision fallback.

`lake env lean Tests/CallIndexScaling.lean` compares indexed and list-based checks and independently
replays every theorem, including the auxiliary proof declarations created by `decide +kernel`. On
Windows with Lean 4.35, the dominant auxiliary declarations used these raw kernel heartbeats:

| Workload | Size | List lookup | Indexed lookup |
| --- | ---: | ---: | ---: |
| Constrained validation, reachable nops | 128 instructions | 4,984,847 | 2,045,014 |
| Constrained validation, reachable nops | 512 instructions | 76,557,716 | 9,566,111 |
| Managed calls, each target used once | 128 methods/calls | 2,767,034 | 1,368,097 |
| Managed calls, each target used once | 512 methods/calls | 39,348,863 | 6,135,858 |

The indexed measurements include index construction and length checks; the list baselines measure
only the per-site checks. These isolate lookup costs rather than estimate total CI wall time. The
constrained traversal is O(N log N), plus branch-target set construction and metadata checks; it no
longer performs O(N²) optional list lookups. Imported signature comparisons retain their existing
checks and costs. The registered constrained/import evidence suites also test unreachable
switch-prefix bypass, duplicate switch targets, short reachability and both import-table bounds.
Home discovery and static/opaque-local validation use balanced indexes instead of repeated
linked-list scans. Home discovery collects live stores and addresses once, then retains argument
order while filtering the argument range. Static sites keep the first descriptor at a duplicate pc.
Opaque-local discovery still considers addresses in the complete raw body, including dead
instructions. Equivalence theorems cover arbitrary input lists, including malformed indexes,
duplicate sites and truncated masks; no new assumptions are required.

`Tests.ExtractionHomeIndexes` exercises those boundary cases. The indexed implementations use
`Std.TreeSet`/`Std.TreeMap` for keyed membership and `FlowIndex` for positional lookup. This adds
standard-library tree dependencies to the validators. The public validity propositions retain their
obligations, with explicit equivalence theorems for the indexed checks.

An Apple M4 run of `leanprof elab --heartbeats` measured the following total declaration work for
paired `decide +kernel` proofs (kHB, thousands of raw heartbeats). More than 99% of total profiled
work was in the kernel. Each pair includes constructing its index. The home fixture has one store
per argument; the static fixture has one descriptor per load; the opaque fixture has equally many
vector locals and out-of-range address references, leaving all locals eligible.

| Check | Entries | List scans | Indexed |
| --- | ---: | ---: | ---: |
| Parameter home discovery | 128 | 3,568.83 | 4,674.26 |
| Parameter home discovery | 512 | 53,145.52 | 24,966.14 |
| Static-load shape validation | 128 | 5,402.08 | 5,152.10 |
| Static-load shape validation | 512 | 81,005.04 | 26,628.89 |
| Opaque-local discovery | 128 | 9,601.26 | 7,323.65 |
| Opaque-local discovery | 512 | 124,343.11 | 31,897.40 |

The tree overhead increases work for the smaller home fixture; at 512 entries, measured work falls
by 53%, 67% and 74%, respectively. These isolate the changed checks and do not estimate end-to-end
CI time. Parameter slot lookup and the rest of contract verification are unchanged.

Call and home/static/opaque measurements above were collected for each isolated change before
stacking the linear FlowIndex builder. Combined-stack counts may differ. Managed-call numbers
measure direct kernel decision, not the preserved structural "cil_managed_calls" shortcut.

Region suffix membership makes fallthrough closure automatic: `lower ≤ pc` implies `lower ≤ pc + 1`.
The checker therefore looks up only explicit branch targets and callees. Its equivalence theorem
still covers every instruction, including a final fallthrough beyond the body; instruction
availability remains a separate execution obligation.

On Apple M4 / Lean 4.35, paired `decide +kernel` checks of 32, 128 and 512 methods, each containing
16 nops and a return and listed from pc zero, took 1,120.60→1,008.90, 5,832.86→5,391.51 and
29,638.99→27,878.92 kHB respectively. These include region-index construction and show 6–10% less
kernel work, not total verification wall-time savings. Aggregate metadata validation counts module
type names once per layout traversal and field names once per visited type. Duplicate
instance/static field names and duplicate full type names still reject; the counts are rebuilt on
each public layout request so later metadata mutations remain visible. `Tests.InstructionIndexes`
includes those rejection and mutation cases.

An isolated Windows .NET 10 scaling fixture used sequential structs with UInt64 fields, warmed three
times, then took the median of seven batches of ten complete layout computations. Index construction
is included: 256 fields improved 1.293→0.158 ms, 1,024 fields 3.753→0.479 ms, and 4,096 fields
49.715→1.829 ms. The duplicate-field check is linear instead of quadratic. These are
layout-validation measurements, not end-to-end extraction or CI estimates. The ordinary struct
extraction retained its generated Lean bytes, and mixed batch-extraction regressions pass. Template
emission groups methods by identity once, indexes template positions and each variant's method
positions, and indexes template callee parameters. Sorted template/callee order and profile input
order remain unchanged; duplicate identities are still rejected before emission. An absent callee in
an excluded profile retains the existing zero placeholder. `Tests/TemplateIndexes.cs` checks
reordered methods, conditional absent callees, deterministic output and duplicate rejection without
compiling Lean.

A Windows .NET 10 Release benchmark emitted two profiles with reverse method ordering and one call
per method. Median times over five measured runs after two warmups, including index construction,
generated text and output writes, were 2.90→1.87 ms at 128 methods, 20.56→6.37 ms at 512, and
127.10→24.18 ms at 2,048. Combined output hashes matched at every size. These are isolated
template-emission measurements, not end-to-end verification estimates. Argument instruction
validation shares indexes for argument types and appended home slots. The home-slot map preserves
the first occurrence even for duplicate home lists; missing argument indexes, hidden home accesses
and unsupported replacements remain rejected. Expected home kinds also use the argument-type index.
Exact lookup/check equivalence theorems preserve the existing semantic consequence statements. Tests
in `Tests.ExtractionHomeIndexes` cover these boundaries.

`Tests/ArgumentSlotScaling.lean` isolates the per-instruction checks with one store per argument. On
Apple M4 / Lean 4.35, `leanprof elab --heartbeats` reported:

| Arguments/stores | List lookup (kHB) | Indexed lookup (kHB) |
| --- | ---: | ---: |
| 128 | 8,953.23 | 4,647.67 |
| 512 | 136,907.69 | 24,508.59 |

The indexed measurements include constructing both indexes with the current linear FlowIndex
builder. They reduce measured work by 48–82%; they do not estimate total CI wall time.

Loaded contract libraries index exports by exact identity and certifications by exact (identity,
profile). The production reader still rejects duplicates before constructing either index.
`Tests/ImportIndexes.cs` checks case-sensitive lookup, multiple profiles and the reader's exact
duplicate diagnostics using an otherwise accepted interface.

A Windows .NET 10 Release synthetic lookup benchmark, with one lookup per export and two
certifications per export, measured median batches of 128/512/2,048 exports at 0.369/1.814/22.929 ms
with list searches versus 0.031/0.121/0.590 ms with dictionaries. Dictionary construction is
included. This measures the lookup algorithm, not DLL validation, proof checking or end-to-end
import time.

Blocker collection retains ordered lists for sites, entries and call chains while using indexes for
deduplication. Sites use record value equality; entries use exact (signature, profile) keys; chains
use full ordinal element equality, including element boundaries and order. Findings and reaches have
reference identity, so assigning a finding's output ID cannot change its hash. `Tests/Blockers.cs`
checks distinct arrays with equal contents, distinct chain splits, profile case and first-seen
output ordering. The full fixture report matches the single-request CLI except for its extractor
hash.

A Windows .NET 10 Release collection benchmark inserted each unique site and two-element chain twice
into one finding. After a one-second warmup per implementation/size, median times over five measured
batches at 128/512/2,048 unique sites and chains were 0.093/2.761/35.876 ms for list deduplication
versus 0.021/0.130/0.540 ms for indexed accumulation. Collection construction is included; indexed
measurements invoke the actual accumulator through reflection. These are collection costs, not
admission or complete report-generation timings. Constrained instruction validation consumes the
raw, reachability and emitted lists together, retaining the previous instruction and reading the
next one from the tail. Lowering likewise retains the raw predecessor before rewriting it. This
removes per-position tree lookup and construction for sequential instruction evidence while
preserving malformed-neighbor and length rejection. Method-target lookup, branch membership and
dispatch metadata resolution keep their existing checks. Opaque-local enumeration reads each type
directly from `zipIdx`; address-set membership remains indexed. The earlier equivalence theorems
retain their statements.

`Tests/StreamingValidationScaling.lean` compares these traversals to the preceding indexed
implementations, using the current linear FlowIndex builder. An Apple M4 / Lean 4.35 run of
`leanprof elab --heartbeats` measured total theorem-declaration work:

| Check | Entries | Indexed positions (kHB) | Streaming positions (kHB) |
| --- | ---: | ---: | ---: |
| Constrained reachable nops | 128 | 1,256.40 | 330.73 |
| Constrained reachable nops | 512 | 5,596.06 | 1,257.34 |
| Eligible opaque locals, no addresses | 128 | 2,248.81 | 1,781.24 |
| Eligible opaque locals, no addresses | 512 | 4,807.78 | 2,599.93 |

These include index construction and isolate positional work. They do not measure dispatch metadata
resolution, full-method proof time or total CI savings. Existing constrained/opaque regressions
pass, with additional trailing-prefix and extra-emitted-instruction rejection cases.

Read-only translation validation and Lean emission each own a `LayoutContext`, scoped to one module
and architecture. It reuses fully validated root layouts and field/position snapshots through layout
declarations, instruction translation and raw evidence emission. Every new root still runs the
original recursive validator with a fresh active set and recursive cache: warming a child cannot
bypass the 128-level nesting check. Contexts never cross metadata rewrites or extraction requests,
and context-taking helpers reject module/architecture mismatches.

`Tests.InstructionIndexes` checks nested-root reuse, field identity/order, fresh-call mutation
visibility, distinct x64/arm64 vector layouts and nesting rejection after warming a child. A
34-request matrix covering scalar, x64-v3, x64-v4 and arm64-advsimd, including nested vector layouts
and tuple division, retained all 68 generated Lean file hashes.

A Windows .NET 10 fixture compiled a method reading every UInt64 field of a wide struct and measured
complete `LeanEmitter.Emit` calls, including constructing the context. After three warmups, median
times over seven runs were 7.762→1.133 ms at 64 fields, 72.221→4.212 ms at 256 fields, and
531.870→21.939 ms at 1,024 fields. All three emitted source hashes matched. The baseline already
includes linear metadata-name counting. This isolates emission work; it does not include loading
assemblies, the initial admission walk, proof checking or CI.

C# argument translation builds argument-to-home-position indexes once per method in validation,
emission and exception lint. The original ordered home array still drives evidence emission.
Duplicate inputs retain their first position, missing homes remain absent, and raw locals are still
added to the home position when emitting local-slot instructions.

`Tests.InstructionIndexes` exercises loads, stores, addresses, duplicate homes and missing-store
rejection. Eight argument-processing methods across scalar, x64-v3 and arm64-advsimd produced 48
byte-identical Lean files before/after. A Windows .NET 10 lookup fixture, including index
construction, performs eight passes over reverse-ordered homes plus a missing argument. After
one-second warmups, median seven samples of 25 runs measured 128/512/2,048 homes at
0.0090/0.0306/0.4200 ms before and 0.0021/0.0088/0.0649 ms after. These isolate lookup costs, not
full extraction or CI wall time. Parameter home discovery enumerates the collected ordered set and
filters its members by the argument bound. It no longer allocates every argument index and performs
a tree lookup for each. The proved list equality retains ascending order, duplicate elimination,
out-of-range filtering and truncated reachability semantics. `Tests/HomeEnumerationScaling.lean`
compares both algorithms.

Apple M4 / Lean 4.35 paired `decide +kernel` declaration work, including set construction (kHB):

| Arguments | Homes | Range membership | Set enumeration |
| --- | ---: | ---: | ---: |
| 128 | 128 | 4,674.52 | 4,331.61 |
| 512 | 512 | 24,966.38 | 23,066.91 |
| 512 | 8 | 2,152.66 | 360.60 |
| 2,048 | 8 | 8,246.02 | 1,011.87 |

The dense cases improve 7–8%; sparse cases improve 83–88%. Computing the argument bound still
traverses the argument list. These are focused kernel-work measurements, not total CI savings.

Interface-module merging uses an ordinal-ignore-case spelling index to detect collisions while
retaining ordinal sorted output. Exact duplicate names with identical source remain accepted;
changed source or different casing remains rejected, including Unicode ordinal case pairs.
`Tests.ImportIndexes` exercises this merge rule independently of interface admission.

A Windows .NET 10 collection benchmark with reverse-ordered unique module names, including both
indexes and sorted output construction, measured 128/512/2,048 modules at 0.092/1.304/20.984 ms
before and 0.011/0.060/0.458 ms after (one-second warmups, median seven samples). This isolates
module merging, not full import verification. Collision detection becomes expected linear work;
sorted output construction still takes O(M log M).

Static initializer bindings reuse the emitter's existing method-identity index instead of searching
the method array at each static load. Null initializers still use zero and missing initializers
still produce the existing `-1` sentinel. Three compiled Word256 static-load entries retain all six
generated Lean hashes; an unsupported initializer retains its exact rejection diagnostic. This
removes O(static sites × methods) search work without another index. Static initializer validation
shares a read-only `StaticValues.Context` within one metadata validation walk. Constructor indexes
retain store positions, the first control transfer and an ordered branch-reentry envelope; module
indexes retain the first stores outside a field's constructor. Constructor closure address checks
and initializer static-access checks are also shared. Specialization creates detached clones, so the
compiled module remains unchanged. A later validation receives a fresh context; there is no
module-wide persistent index cache. The existing field/architecture value cache remains unchanged.

`Tests.StaticValueIndexes.cs` checks scalar copies, duplicate stores, prefix control flow,
branch/switch and foreign targets, first outside writer, closure address-taking, fresh contexts and
resolution-error ordering. Index construction records resolution failures so a later failure cannot
replace the original earlier writer diagnostic. Twenty-four extraction requests (eight scalar loads
across three profiles) retain all 48 generated Lean file hashes.

Windows .NET 10 medians over seven runs after three warmups measured resolution of every field in a
fresh synthetic module, including context/index construction, literal evaluation and value checks
but excluding fixture construction. The module has one constructor assigning all fields and one
reader accessing them all:

| Readonly fields | Repeated scans | Shared indexes |
| --- | ---: | ---: |
| 128 | 5.638 ms | 0.350 ms |
| 512 | 28.794 ms | 1.470 ms |
| 2,048 | 172.527 ms | 6.254 ms |

These isolate static-field resolution and do not estimate full extraction or CI savings. Layout
computation accumulates field placements in reverse and restores declaration order once, removing
quadratic `fields ++ [field]` work. `computeLayout_eq_append` proves equality to the complete
list-based computation for arbitrary layouts, architectures and nested-layout tables.
`Tests.LayoutAccumulation` covers order, explicit overlaps, empty layouts, missing children,
packing/offset failures and vector architecture restrictions.

Apple M4 / Lean 4.35 paired `decide +kernel` checks in the standalone
`Tests/LayoutAccumulationScaling.lean` fixture measured 2,556.71→546.05 kHB for 128 fields and
34,404.26→2,080.50 kHB for 512 fields (79–94% less kernel work). These include constructing and
comparing the entire computed layout, not total CI time. Local step lemmas keep the new full
algorithm-equivalence proof inexpensive: its declaration takes 1,282.34 kHB rather than the
177,255.76 kHB of the initial broad proof attempt. Constrained-call validation and lowering build
ordered dispatch candidate indexes once per invocation, then reuse them across call sites. Type
identity, method token/name and explicit interface override lookup no longer rescan the full catalog
for every call. Candidate buckets retain duplicates, exact type checks and explicit override
precedence. Repeated override tokens within one method still contribute only one candidate.
Arbitrary-input equivalence theorems cover indexed resolution, complete instruction validation and
lowering, including malformed and ambiguous metadata. The list-based `resolveConstrained` remains
the specification used by those theorems; production validation and lowering use
`DispatchIndex.resolve`.

`Tests/DispatchScaling.lean` is a standalone kernel-work comparison with one valid call per concrete
type and a shared interface. Both sides construct the raw catalog; the indexed side also constructs
all indexes. Apple M4 / Lean 4.35 `leanprof elab --heartbeats` declaration work:

| Concrete types and calls | List search (kHB) | Indexed dispatch (kHB) |
| --- | ---: | ---: |
| 16 | 3,825.30 | 4,691.19 |
| 32 | 11,182.25 | 9,893.97 |
| 64 | 36,403.13 | 21,464.39 |

Index construction costs 23% more in the small fixture, breaks even before 32 calls and reduces work
by 41% at 64 calls. These are type-heavy dispatch measurements, not total proof or CI time.
Validation and lowering each construct their own index; they do not share it across invocations. The
helper APIs `constrainedSiteWindow`, `constrainedSites`, `lowerConstrainedInstruction`,
`lowerConstrainedCode` and their streaming equivalence theorems accept a resolver function. Public
`ConstrainedCallsValid` and `lowerConstrainedRaw` argument types are unchanged.

Public layout projection validation constructs balanced indexes for artifact selection and nested
public-index expansion. Ordered sets replace the three quadratic list-uniqueness checks.
`LayoutProjectionValid_iff_list` proves exact equivalence to all list-based conditions for arbitrary
inputs, including malformed indices and catalogs. `Tests.LayoutProjectionIndexes` checks reordering,
empty catalogs, duplicate identities/indices, case-sensitive identity, missing indices and nested
expansion; the existing imported-layout certificate tests also pass.

The proposition's unfolded conjunction exposes `projectionDistinct ... = true` instead of
`List.Nodup`, and `projectionMetadataMatches` instead of the list-based metadata equality. Consumers
that destructure these clauses can recover the list-based statements through
`LayoutProjectionValid_iff_list`; the validator's accepted inputs and computed-layout checks are
unchanged. No stepping equations or execution tactics change.

Apple M4 / Lean 4.35 `leanprof` measurements of the standalone `Tests/LayoutProjectionScaling.lean`
paired `decide +kernel` fixture include complete validators, both computed-layout checks, and
construction of all indexes/sets. At 128 distinct empty layouts, the workload fell from 42,941.43 to
29,594.10 kHB (31% less). At 32 layouts it increased from 3,288.47 to 3,667.68 kHB (12% more): index
construction has a small-catalog cost. These are synthetic validator measurements, not total CI
timings. The eliminated work is quadratic identity/index comparison and repeated linear metadata
lookup; computed-layout validation and structural equality remain, so this is not a claim that the
entire validator is linear.

Imported-interface auditing selects declarations from the imported module catalogs rather than
materializing and filtering every declaration in the Lean environment. Current-file declarations
still use the environment scan. Private and auxiliary declarations are included and their actual
module ownership is checked. Dependency traversal visits shared expression nodes only once;
canonical contract serialization is unchanged. `Tests.ContractClosure` compares selected membership
with the list-based scan, including current, imported, missing and duplicate modules. The imports
suite compiles that test against its already certified library instead of rebuilding the library's
dependencies in the repository checkout.

A preliminary Windows paired native audit of `ImportFixture.addOne` measured median 3.50 seconds
before and 1.22 seconds after (three runs each), with byte-identical audit output. These focused
timings are not complete-suite or CI measurements.
### Consumer certificate and theorem audit imports

Fresh consumer verification audits the extraction certificate and requested proof in one native
import environment. Both artifacts must match their kernel-replayed module paths, and their
individual theorem types, premises and allowed axioms are still checked. This removes a repeated
closure import; it does not reuse a previous proof result or skip fresh verification.

The four positive verification requests in `Tests/ConsumerCertificateReuse.cs` used eight native
audits before this change and four afterward. Local Windows traces measured 11.03 seconds versus
5.95 seconds in those audits. Other concurrent builds affected whole-fixture timings, so this is not
an end-to-end CI estimate. Corrupted receipts, changed extraction and generated-source modification
controls still reject as before.
### Allocation reference-step proof search

`fixed_fallback` normalizes mapped stack constructors definitionally and rewrites the target profile
once. It avoids repeatedly asking the simplifier to discharge the large dispatcher's negative match
conditions. Reference operations use a proved finite classification before stack case analysis; this
changes proof construction, not execution or the simulation statement.

On Apple M4 with Lean 4.35 and `leanprof --heartbeats`, elaborating `Memory.Renamed.stepReference`
fell from 416,618.32 to 204,647.51 kHB (51% less). Its kernel check fell from 16,039.56 to 11,202.47
kHB (30% less). The generated Windows olean shrunk from 32,111,728 to 26,561,792 bytes. All four
fixed-step family consumers and the full 423-job library build passed without `sorryAx`. The
profiling fixtures included the candidate macros inline; the figures above select the theorem's own
elaboration and kernel entries. The same native auditor parses contract source import headers with
Lean's parser. This replaces compiling a temporary Lean parser program for each verification.
Parsing still rejects malformed headers, retains comments and module-system import syntax, and never
elaborates source commands. The imports fixture checks those properties explicitly. A focused native
parse takes roughly 0.06 seconds locally; the original CI run spent 22.1 seconds across 25
interpreted parser calls.
### Core example batches

Core's ten immutable example proofs share one generated verification batch. Each keeps its own
extraction, theorem audit, exact translation certificate and output identity check. The source,
environment, receipt and assembly mutation scenarios remain separate. The focused `dotnet run --file
Tests/CoreExamples.cs` fixture uses the same implementation; `--separate` reproduces the separate
verification loop, and `--check-existing <directory>` checks all reports and rejects changed proof
identity or batch source. With success caching disabled and the same prepared library, the ten
examples took 116.95 seconds separately and 28.65 seconds batched on Windows. They contain nine
distinct proof texts and ten distinct extracted programs. Native audits fell from ten to one, replay
processes from eleven to two, and Lake invocations from five to one; both runs built exactly one
support module. This is a focused measurement, not a claim that the complete Core job has reached
four minutes.

The generic-method, F# and universal-contract fixtures also batch their immutable positive proofs.
The generic instance and other fixed-memory contracts retain their exact statements; batching does
not turn them into arbitrary-memory specifications. Mutated assemblies and expected failures retain
their isolated checks. These changes remove eleven separate positive verification sessions across
the three fixtures.

Standalone proofs and generated batches combine their final replay and theorem audit when eligible.
Dependency certification, artifact identity checks and failure diagnostics remain; audits needing
source-location metadata still import the checked artifacts. Paired Windows runs of the ten-example
batch with the same certified library took 29.98 seconds with separate replay/audit and 28.10
seconds combined. An earlier combined run took 40.17 seconds with slower compilation and setup too;
these short fixture timings remain sensitive to host load.

Compatible consumer requests can share that final replay and audit too. Each selected theorem and
its reachable replay-target declarations must belong to the request's own import closure. Duplicate
declarations and skipped consumer support conservatively retain separate checking. The fallback
replays each request's import-closed target set independently, preventing a forged proof from
borrowing an undeclared sibling dependency before an isolated axiom audit. `Tests/JointReplay.cs`
covers target and external owners, duplicate bodies and hidden dependencies. The existing consumer
batch checks also reject a theorem available only in another request.

`Tests/ConsumerCombinedAudit.cs` is a focused manual benchmark and adversarial fixture. Its
`--without-hidden` comparison keeps eight successful requests and two expected failures fixed. On
Windows, that workload took 30.87 seconds with separate audits and 19.48 seconds with shared
replay/audit, using the same certified library. Its default additionally checks an undeclared
reference to an unapproved sibling axiom; both shared and isolated fallback paths must reject it.
These measurements exclude fixture setup and do not establish a complete-suite CI timing.

### Native joint kernel replay

Direct and consumer contract interfaces are replayed and validated in the same native environment
when their complete declaration ownership is unambiguous. The replayed ownership map enumerates
private, auxiliary and unused declarations; interface checks do not select only the exported
contract's dependencies. Imported interfaces outside the replay target set, duplicate ownership and
conflicting code-generator ownership entries retain the metadata import fallback. Source-location
audits and replay profiling retain their existing paths. `Tests/JointReplay.cs` compares ordinary
and replayed interface verdicts, including module-system private declarations, unused forbidden
axioms, misleading namespaces and equation auxiliaries. Use `dotnet run --file Tests/JointReplay.cs
-- --audit-only` for the native audit regressions without repeating the independent bootstrap and
native replay regressions.

The authenticated `leancil-audit --replay INPUT` command accepts a JSON array of module names. It
uses the same `CIL/Replay.lean` algorithm as fresh-library bootstrap certification: import
non-target dependencies without extensions, reject conflicting declarations and replay target
constants in the kernel. Identical on-demand theorem duplicates retain the toolchain rule. The
native executable is checked before and after replay. Before it is authenticated, bootstrap uses the
source captured when the verifier starts and rejects changes before executing it.

`Tests/JointReplay.cs` exercises both modes against import-closed targets, repeated equation lemmas,
conflicting declarations, targets hidden behind untargeted imports and forged theorems. Rejected
joint sets still fall back to per-module replay with individual failure attribution. After auditor
authentication, `--replay-separately` performs this fallback natively. Each module gets its own
imported environment and the pinned toolchain's sequential kernel replay; no successful sibling can
supply an undeclared dependency. Bootstrap and profiling retain the toolchain frontend runner. The
regression checks forged bodies, hidden declarations, malformed and missing target files, and
missing imported modules in both paths. Three alternating Windows measurements of a fixed mixed
valid/forged/undeclared/missing target set took 3.36/3.04/3.03s through the frontend and
2.17/2.14/2.04s natively: about 0.9–1.2s less per fallback. This measures fallback startup and
replay, not a full consumer-suite speedup; required independent kernel checks still run. For a
single consumer request, a fused audit that reports a kernel declaration rejection goes directly to
isolated replay instead of retrying the identical joint target set. Unrecognized diagnostics and
metadata/eligibility failures keep the ordinary joint retry; a changed diagnostic can therefore only
lose this optimization. Multi-request closures still receive their own replay attempts. The existing
unused-forged-helper regression checks the two required stages without adding another verification
request. Three full negative consumer requests on Windows took 9.68/9.87/9.82s before removing the
duplicate trial and 8.40/8.27/8.36s afterward. Their joint attempts fell from six to three in total;
all three isolated checks and the same forged-body rejection remained. Positive and refutation
consumer cases retain their normal audits and failure classification. The joint replay fixture
asserts the rejected joint stage and subsequent isolated attribution in one invocation for
conflicting names, untargeted imports and forged definitions. Both bootstrap and native modes remain
covered. This removes six duplicate checker processes; the six retained joint stages took 9.06s
together on Windows, indicating the avoided work without treating that estimate as a whole-fixture
timing comparison. Within a fixed batch workspace, an isolated helper rejection also rejects later
requests that import that helper. The verifier retains that failure instead of replaying another
already-invalid request closure. Successful requests still receive their own checks, and no
successful joint module result is reused across scopes. The existing eleven-request mixed batch
checks every status, certificate and hidden-sibling rejection and requires one isolated rejection of
its shared forged helper. Initial Windows measurements were 52.79s before and 43.36s after reuse;
elapsed time includes runner variance. Joint attempts fell from ten to nine and isolated checks from
three to two, with three consumer builds unchanged. After an eligible fused batch rejects a kernel
declaration, each remaining request can fuse its own replay with its theorem audit. Only that exact
request's checked result is retained; partial success never skips a sibling's replay. Ineligible
scopes retain ordinary fallback. A second paired measurement, including both changes, took 49.06s
before and 40.04s afterward (18.4%), with all eleven original outcomes and certificates unchanged.
Fresh compilation, isolated rejection attribution and the hidden-sibling controls remain mandatory.
The test also rejects a changed bootstrap source snapshot. In one Windows trace, the two positive
target sets took 2.03/2.19 seconds through the Lean frontend and 0.37/0.37 seconds through the
native auditor. Single-file verification shares replay imports for its multi-module interface and
proof target sets. Fresh checking and failure isolation are unchanged.

The native auditor also accepts `replayTargets` in an audit request. It retains the kernel's checked
environment for structural theorem and constant checks, avoiding a second dependency import. Any
duplicate declaration, interface/closure/namespace request, or contract refutation requiring source
locations retains the ordinary audit import. This does not change the standalone replay duplicate
rule: equal theorem types can have different proof bodies, so a merged replay environment must not
choose which body's axioms a subsequent audit sees. `JointReplay` checks both duplicate orders, a
forged body, source-location fallback and toolchain shadowing in both paths. A fixed
`Tests.MethodContract` artifact took 2.59–2.63 seconds for separate native replay and audit versus
1.36–1.38 seconds combined, with identical statement and axiom output. These are focused Windows
timings. Single-request consumer groups use this path, except export callbacks, full-import audits
and profiled replay. Existing byte snapshots, module-path checks and post-audit integrity checks
still bind the result. A rejected joint set retains per-module failure attribution. The verifier
records `auditFused` so measured runs distinguish shared environments from metadata or
duplicate-declaration fallbacks.

### Evidence-suite reuse

The evidence runner compiles its test modules once against the authenticated CIL library, without
asking Lake to rebuild that library from copied build traces. Test dependencies are ordered before
their importers, with at most two independent compilations running together. Child fixtures validate
the parent's source/output hashes before reusing a completed test; standalone fixture invocations
retain their original build path. Reproduce this preparation with `dotnet run --file
Tests/ExtractionEvidence.cs -- --prepare-only`.

Generated rejection batches retain each mutation's original expected diagnostic markers. A Lean
command saves and restores the complete command state around each case, including its declarations,
attributes, scopes and options. Messages are collected with Lean's `guard_msgs` helper, then
associated with the original case's line range. A rejected neighbor, missing marker, successful
mutation or leaked failed simp theorem cannot satisfy another case's check;
`Tests/RejectedEvidenceTests.cs` exercises these failures. No rejection result is published until
every case passes. Existing audited positive batches still replay with `leanchecker`; direct
semantic fixtures retain their original frontend kernel checks while sharing imports.

The four capability profiles share one generated verification batch. Every profile keeps its own
extraction identity, execution theorem, certificate audit and final regeneration check. A regression
rejects reuse of the scalar report under the x64-v3 profile. The runtime-scope constants in the
scalar, type-test, throw, span and imported-layout fixtures use the existing byte representation,
whose equality to the full assembly-name literal is already proved by `runtimeScope_eq`; their
regression statements are unchanged.

Focused Windows measurements on this change reduced the scalar regression file from about 26 seconds
to 14.4 seconds and the type-test file from 12.2 seconds to 9.0 seconds by reusing that
representation. The mixed-profile feature fixture's traced work took 37.5 seconds locally. These are
local observations, not a claim that the evidence CI job is below four minutes; its completed Ubuntu
run remains the end-to-end acceptance measurement.

Constrained-call rejection fixtures retain the emitted definitions and the exact constrained
validator obligations, while their full positive certificates still check every validator. Positive
controls compile that same reduced fixture before changing its call target, so a missing
prerequisite cannot masquerade as rejection. Static-span proofs share one batch across original and
mutated assemblies, and UTF-8 identity mutations use isolated rejection scopes. Generated
verification batches use the authenticated native kernel replay command when it succeeds, retaining
the toolchain checker as the failure fallback for the same module set.

Translation-audit fixtures compile all six certificate variants against one checked prefix before
testing wrapper rejection, then replay those declarations and audit their exact native statements.
Missing certificates, unrelated statements, definitions and altered import tables must fail both
their wrapper checks and direct certificate audits; the definitionally equal wrapped statement still
passes elaboration but fails the exact emitted-statement check.

Generic substitution, managed-call and method-shape mutations select their corresponding emitted
validator; type-test mutations select feature-flow validation. Unchanged controls compile first,
with repeated generic controls deduplicated. Byte-backed identity definitions retain their UTF-8
witnesses. Evidence-list omission and reordering still check the complete certificate because they
test agreement between records, not an independent validator.

Feature-flow validation indexes addressed local slots and classifies exact local types once, then
shares that index across state-shape checks, local transfers and emitted local operations.
`FeatureLocalIndex.eligible_eq` proves equality with the original raw instruction/type scan for
every index and fact, including malformed metadata and missing locals. Existing feature-flow
equivalence and reachability proofs retain their statements. The focused feature regression also
checks boolean bounds, both address-taking opcodes, wrong assembly scopes and malformed address
operands.

`Tests/FeatureLocalScaling.lean` isolates known facts at every instruction/local pair. A local
kernel measurement reduced 128×128 checks from 1.52 to 0.844 seconds, 256×256 from 6.58 to 3.99
seconds, and 512×512 from 29.3 to 16.4 seconds. Both measured sequences grow approximately
quadratically; these data do not demonstrate a different asymptotic kernel cost. The eliminated work
is repeated raw-body address scanning, local-list lookup and type classification. The existing
feature regression module changed from 4.290 to 4.056 seconds, a smaller benefit because ordinary
certificates often contain unknown facts, which already exit early. For full 128-instruction feature
certificates, empty-local kernel checks measured 116 versus 117 ms and 128 unknown locals measured
161 versus 152 ms; this sample showed no material regression on the early-exit paths.

Full-verification term transfer encodes each structurally distinct expression node once and writes a
compact data table instead of elaborating a recursively expanded constructor term. Structural
equality includes binder spelling and annotations; names retain numeric and string components, and
universe expressions retain their full structure. Metadata is stripped as before. The decoder
rejects missing, cyclic and forward references, unknown binder annotations and malformed table data.
Free variables and expression/universe metavariables remain unsupported.

Decoding constructs expressions only. Each transferred declaration still passes `Lean.addDecl` with
kernel checking explicitly enabled, followed by the existing independent replay and exact
composition audit. The generated source imports the decoder from the certified
`CIL.Interface.FullTransfer` module. `Tests.FullTransfer` checks exact reconstructed types and
values across binders, universes, projections, local lets, string literals and proofs, plus
malformed table rejection. The full transitive suite retains its forged dependency, staged mutation,
changed implementation, cyclic dependency and missing-bundle regressions.

Contract publication audits interface declarations and their requested closures in one imported
environment. The fresh consumer theorem audit also requests each export's closure and certified
statement, including independently rebuilt full-verification exports. Export callbacks consume that
authenticated response after the existing artifact and source guards; they do not import the
environment again. The closure digest, contract kind, theorem axioms and statement checks remain
separate obligations. `exportsaudit` exercises source and compiled-artifact mutation after those
callbacks and requires the original integrity failures.

Exports whose artifacts lie outside the proof root share one consumer input snapshot and the
existing extraction-group verification machinery. Each request retains its own exact export audit
and checked result. Artifacts inside the proof root retain individual snapshots so their output
exclusion does not hide another request's source. `exportsfullpair` checks two exported methods and
their independently replayed caller composition; its focused Windows run passed in 179.7 seconds.
That is a validation timing, not a before/after performance measurement. Consumer workspaces restore
authenticated, source-bound support before compiling published interfaces. Identical interfaces can
therefore reuse their compiled artifacts across extraction groups, while each workspace still
kernel-replays them and checks their canonical contract closures against its own imports. Existing
before/after artifact checks remain in place. `Tests/ContractImports.cs --interface-reuse-only`
checks two fresh profile groups with one interface compilation and independent replays. A focused
Windows comparison reduced interface build stages from 5.28 to 2.95 seconds and the two-request
verification from 50.54 to 47.67 seconds. These are fixture timings, not complete-suite or CI
measurements.

Consumer verification audits `Extracted.translation_valid` directly after kernel replay instead of
compiling a second theorem that merely restates it. The native auditor still requires a theorem
declaration, the exact `TranslationValid` application over the emitted tables and program, and the
approved axiom set. Consumer reports therefore name `Extracted.translation_valid` in
`extractionAudit`; the single-file verifier still names `ExtractionAudit.valid`. Workspaces
containing expected proof rejections retain the wrapper, since those requests can finish before the
final native audit. Compiled extraction and component artifacts are hashed before consumer proof
checking and checked again afterward. Authenticated native replay also handles single-module target
sets; profiling retains the toolchain frontend, and rejected native replays retain the existing
per-module fallback. The same two-profile fresh workload took 43.56 seconds with these changes,
versus 47.67 seconds with interface restoration alone; certificate compilation fell from 8.71 to
5.64 seconds and replay from 8.73 to 6.83 seconds. Full-suite timing remains a separate check.

The component-reuse and support-union fixtures skip their framework-only warmup verification when
`LEANCIL_CERTIFIED_LIBRARY` is supplied. Their actual batches still authenticate that library and
verify every original request with success caching disabled. Without a supplied library, the
original warmup remains. This removes two redundant complete consumer sessions from prepared CI runs
without removing any component, replay or source-identity assertions.

Fold discovery counts decoded local references once with a balanced tree instead of filtering the
entire instruction body per local. `foldRoles_eq_filter` proves exact equality to the filter-based
specification, including malformed operands and out-of-range local indexes. Methods without locals
skip count construction. The separate positional lookup of local types remains linear; this change
does not make all of fold discovery linear.

Exception folds inspect at most three message loads, since admitted constructors accept at most two.
`throwFold_eq_takeWhile` proves equality to the unrestricted prefix scan. Long rejected prefixes
still permit an admitted fold starting later. Span and throw evidence tests cover extra uses,
malformed local operands, oversized prefixes and valid suffix folds.

On Apple M4, kernel-checked discovery for 256 span locals/768 instructions fell from 7.87s to 2.40s
(user CPU 7.45s to 2.05s), including index construction and checking every output role. A
4,096-instruction message-only body fell from 6.47s to 2.06s (user CPU 6.15s to 1.76s). Smaller
counts showed 0.94s to 0.76s at 64 locals and 2.29s to 1.17s at 128 locals. Existing
TypeTestEvidence and SpanEvidence were effectively unchanged: 5.22s to 5.15s and 0.77s to 0.77s.
Those fixtures contain few locals and short message prefixes, so these are scaling improvements
rather than a demonstrated large CI saving.

The standalone kernel benchmarks are `docs/performance/fold-roles/CountScaling.lean` and
`ThrowScaling.lean`. After building each revision's library, run `lake env lean
docs/performance/fold-roles/CountScaling.lean` (and the throw file) under an external timer. They
construct their inputs inside the checked proposition and verify complete role lists with `decide
+kernel`; neither benchmark is part of the default library build.

With the indexed validators and combined replay/audit built into a newly certified library, the
Windows two-profile interface-reuse workload passed in 39.14 seconds, compared with 43.56 seconds
before these changes. Both consumer groups used the fused audit; the interface still compiled once
and was independently replayed in each group. The entire fixture, including setup, took 56.86
seconds. These timings do not establish a whole-suite CI gain. The certificate-reuse fixture passed
all six checks: its four positive sessions used the fused audit, and generated-source tampering and
compiled-extraction substitution were rejected.

### Transitive composition replay

The transitive import suite runs its staged-bundle mutation probe in a separate process of its
already compiled executable. This preserves process isolation and all mutation checks without
compiling the shared verifier a second time. The helper remains a tracked suite input through its
include directive. Full composition also shares its final replay and exact audit; the transitive
fixture checks that this path uses the native auditor in one invocation.

On a Windows App → A → B fixture, final composition replay plus its exact audit fell from 7.83s to
1.67s when combined. The complete forced-full invocation took 96.16s before and 87.46s afterward;
this is a local sample, not a whole-suite CI measurement. Catalog scans covered 2,546 toolchain
modules in 23–54ms, so mutable module-resolution rescans remain intact.

### Fixed profile references

The profile-family fixture disables persistent receipts for its initial three-profile export. It
requires one fixed-reference build and three independent profile extraction replays. Source-bound
authenticated references already shared compilation; the verifier avoids Lake invocations when their
restored module parts and traces still match exactly. A Windows sample removed two no-op builds of
0.20s each; the retained build stayed at 2.96s (2.97s before). Total export time was 56.38s before
and 55.20s afterward, but this small sample establishes the removed process work rather than a
stable whole-suite speedup.

`Unsafe.AreSame<T>`, `IsAddressLessThan<T>`, `IsAddressGreaterThan<T>`, `ByteOffset<T>`,
`AddByteOffset<T>` and `SubtractByteOffset<T>` (signed and unsigned native offsets) reuse checked
allocation-relative reference operations. Generic storage types must already have a supported
managed layout. Exact runtime identity, closed signatures, offset signedness and byte scaling are
checked by Lean translation evidence.

Byte differences and ordering require live references in the same allocation. Equality supports
nulls and distinct allocation interiors; cross-allocation end-pointer equality remains unsupported.
Byte offsets preserve bounds and grant no read/write authority. `ByteOffset` accepts readonly views;
addition retains the existing writable-reference input restriction, and subtraction preserves a
readonly input. Element `Subtract<T>` covers signed 32-bit and signed/unsigned native offsets,
including aggregate and vector scaling. Tests compare native wraparound with the runtime and reject
forged strides and signedness in Lean evidence. These operations do not model arbitrary numeric
addresses or establish runtime placement of separate allocations.
