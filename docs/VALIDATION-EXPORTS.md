# Contract export and consumer validation

<!-- audience: maintainers -->

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
| `exportsdiscovery` | Real producer SDK/publication bootstrap, then the six-argument discovery fixture |
| `exportstyped` | Standalone closed-generic, imported-layout and imported-local fixture with its own SDK setup and existing assertions |
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

CI timeouts are 90 minutes for imports, 120 for
each exports leaf, and 30 for other suites. The matrix uses at most eight runners. Run the
resource-bounded routing tests with `dotnet run --file scripts/TestSelectVerification.cs`; they need
no Lean build or fixture SDK project. Full integration results come from the CI leaf jobs.

## Extraction and metadata checks

`Tests/PointerOperations.cs` compares seven compiled pointer methods with .NET: int32/native byte
subtraction, pointer differences and four unsigned orderings. It independently forges subtraction as
addition and requires the Lean scalar certificate to reject it. The Lean fixtures cover negative
offsets and differences, end positions, readonly preservation, every unsigned branch, and null,
cross-allocation, invalid-position and signed-comparison rejection.

Managed-call proof construction is covered by `Tests/ExtractionGenerics.lean` and the 15 generated
generic-method samples in `Tests/GenericEvidence.cs`. Direct tactic rejection checks cover changed
signedness, assembly scope, generic arguments and argument count.

`Tests/GenericEvidence.cs` also checks exact external-call identity sharing, repeated emission,
pruned-only identities and Unicode/escaped characters. Changed bytes, versions and tokens fail the
generated equality proof. Replacing a raw target with another correctly encoded identity, or
changing its emitted intrinsic, still fails the unchanged division certificate. Existing
specialization and raw/translated metadata rejection cases remain enabled.

The core `Tests/AllocationImports.cs` fixture checks that the CIL umbrella omits allocation
refinement, builds both explicit allocation acceptance modules, and jointly replays every additional
imported module. These modules require checking even though ordinary consumers do not import them. The compiled
namespace audit checks their theorem axiom closures even on warm builds and binds the audited paths
and module bytes to those replayed. An isolated theorem depending on `sorryAx` passes kernel replay
but must fail that audit; build output is also checked.

Extraction bookkeeping indexes declaration names, imported assembly identities, imported call slots,
batch proof modules and aggregate layout names. Component imports retain declaration order; raw
layout positions and emitted layout constant positions have separate indexes.
`Tests/ConsumerSupportCandidates.cs` checks dependency ordering and conservative references in
literal text, while `Tests/InstructionIndexes.cs` checks nested layout ordering and absent types.
The transitive import regression also checks identical imports before rejecting ambiguous versions.

The certificate successor index consumes the source list once to build its balanced tree, replacing
repeated length/take/drop traversals. `Tests.FlowIndex` covers empty and singleton inputs, odd/even
partitions, missing certificate states, out-of-bounds lookups and untouched suffixes.
`FlowIndex.build_spec` proves prefix consumption and exact list lookup equivalence.

Tree construction is linear in list cells; arbitrary target lookup is logarithmic.
Feature and scalar validators use the proved optional-lookup interface.

The shared state-pairing proof uses explicit list-shape cases and depends only on `propext`.

Region closure builds an ordered map of each method's minimum starting pc, visits program methods
sequentially, and checks each included body once. It skips absent region entries and preserves
region membership for absent callees: execution validity is a separate obligation. The equivalence
theorem covers the list-based specification exactly, including duplicate starts and out-of-range
pcs. `Tests.RegionRun` exercises those cases; `Tests/RegionScaling.lean` is a standalone
before/after workload for `leanprof elab --heartbeats`.

Constrained validation uses balanced instruction/reachability indexes and a
set of all decoded branch destinations, including unreachable instructions and switch arms. The
following constrained lowering pass also indexes predecessor instructions;
`lowerConstrainedRaw_eq_original` proves identical output for arbitrary raw bodies, including
malformed prefixes. Managed-call validation indexes both extracted methods and imported slots once
per method check. The equivalence theorems `ConstrainedCallsValid_iff_original` and
`ManagedCallsValid_iff_original` preserve the original list-based rules, including absent entries,
import offsets and malformed lengths. `cil_managed_calls` still uses structural metadata equalities
before its kernel-decision fallback.

The registered constrained/import evidence suites also test unreachable
switch-prefix bypass, duplicate switch targets, short reachability and both import-table bounds.
Home discovery and static/opaque-local validation use balanced indexes instead of repeated
linked-list scans. Home discovery collects live stores and addresses once, then retains argument
order while filtering the argument range. Static sites keep the first descriptor at a duplicate pc.
Opaque-local discovery still considers addresses in the complete raw body, including dead
instructions. Equivalence theorems cover arbitrary input lists, including malformed indexes,
duplicate sites and truncated masks; no new assumptions are required.

`Tests.ExtractionHomeIndexes` exercises those boundary cases. The indexed implementations use
`Std.TreeSet`/`Std.TreeMap` for keyed membership and `FlowIndex` for positional lookup, with
explicit equivalence theorems for the indexed checks.

Region suffix membership makes fallthrough closure automatic: `lower ≤ pc` implies `lower ≤ pc + 1`.
The checker therefore looks up only explicit branch targets and callees. Its equivalence theorem
still covers every instruction, including a final fallthrough beyond the body; instruction
availability remains a separate execution obligation.

Aggregate metadata validation counts module
type names once per layout traversal and field names once per visited type. Duplicate
instance/static field names and duplicate full type names still reject; the counts are rebuilt on
each public layout request so later metadata mutations remain visible. `Tests.InstructionIndexes`
includes those rejection and mutation cases.

Template
emission groups methods by identity once, indexes template positions and each variant's method
positions, and indexes template callee parameters. Output uses sorted template/callee order and
profile input order; duplicate identities are rejected before emission. An absent callee in
an excluded profile retains the existing zero placeholder. `Tests/TemplateIndexes.cs` checks
reordered methods, conditional absent callees, deterministic output and duplicate rejection without
compiling Lean.

Argument instruction
validation shares indexes for argument types and appended home slots. The home-slot map preserves
the first occurrence even for duplicate home lists; missing argument indexes, hidden home accesses
and unsupported replacements remain rejected. Expected home kinds also use the argument-type index.
Exact lookup/check equivalence theorems preserve the existing semantic consequence statements. Tests
in `Tests.ExtractionHomeIndexes` cover these boundaries.

Loaded contract libraries index exports by exact identity and certifications by exact (identity,
profile). The production reader still rejects duplicates before constructing either index.
`Tests/ImportIndexes.cs` checks case-sensitive lookup, multiple profiles and the reader's exact
duplicate diagnostics using an otherwise accepted interface.

Blocker collection retains ordered lists for sites, entries and call chains while using indexes for
deduplication. Sites use record value equality; entries use exact (signature, profile) keys; chains
use full ordinal element equality, including element boundaries and order. Findings and reaches have
reference identity, so assigning a finding's output ID cannot change its hash. `Tests/Blockers.cs`
checks distinct arrays with equal contents, distinct chain splits, profile case and first-seen
output ordering. The full fixture report matches the single-request CLI except for its extractor
hash.

Constrained instruction validation consumes the
raw, reachability and emitted lists together, retaining the previous instruction and reading the
next one from the tail. Lowering likewise retains the raw predecessor before rewriting it. This
removes per-position tree lookup and construction for sequential instruction evidence while
preserving malformed-neighbor and length rejection. Method-target lookup, branch membership and
dispatch metadata resolution keep their existing checks. Opaque-local enumeration reads each type
directly from `zipIdx`; address-set membership is indexed.

Constrained and opaque-local regressions include trailing-prefix and
extra-emitted-instruction rejection cases.

## Layout and dispatch indexes

Read-only translation validation and Lean emission each own a `LayoutContext`, scoped to one module
and architecture. It reuses fully validated root layouts and field/position snapshots through layout
declarations, instruction translation and raw evidence emission. Every new root still runs the
original recursive validator with a fresh active set and recursive cache: warming a child cannot
bypass the 128-level nesting check. Contexts never cross metadata rewrites or extraction requests,
and context-taking helpers reject module/architecture mismatches.

`Tests.InstructionIndexes` checks nested-root reuse, field identity/order, fresh-call mutation
visibility, distinct x64/arm64 vector layouts and nesting rejection after warming a child.

C# argument translation builds argument-to-home-position indexes once per method in validation,
emission and exception lint. The original ordered home array still drives evidence emission.
Duplicate inputs retain their first position, missing homes remain absent, and raw locals are still
added to the home position when emitting local-slot instructions.

`Tests.InstructionIndexes` exercises loads, stores, addresses, duplicate homes and missing-store
rejection.
Parameter home discovery enumerates the collected ordered set and
filters its members by the argument bound. The proved list equality retains ascending order, duplicate elimination,
out-of-range filtering and truncated reachability semantics. `Tests/HomeEnumerationScaling.lean`
compares both algorithms.

Interface-module merging uses an ordinal-ignore-case spelling index to detect collisions while
retaining ordinal sorted output. Exact duplicate names with identical source remain accepted;
changed source or different casing remains rejected, including Unicode ordinal case pairs.
`Tests.ImportIndexes` exercises this merge rule independently of interface admission.

Static initializer bindings reuse the emitter's existing method-identity index instead of searching
the method array at each static load. Null initializers still use zero and missing initializers
still produce the `-1` sentinel. Static initializer validation
shares a read-only `StaticValues.Context` within one metadata validation walk. Constructor indexes
retain store positions, the first control transfer and an ordered branch-reentry envelope; module
indexes retain the first stores outside a field's constructor. Constructor closure address checks
and initializer static-access checks are also shared. Specialization creates detached clones, so the
compiled module remains unchanged. A later validation receives a fresh context; there is no
module-wide persistent index cache.

`Tests.StaticValueIndexes.cs` checks scalar copies, duplicate stores, prefix control flow,
branch/switch and foreign targets, first outside writer, closure address-taking, fresh contexts and
resolution-error ordering, and that computable scalars never resolve as unknown while random seeds
do. Index construction records resolution failures so a later failure cannot
replace the original earlier writer diagnostic.

Layout
computation accumulates field placements in reverse and restores declaration order once, removing
quadratic `fields ++ [field]` work. `computeLayout_eq_append` proves equality to the complete
list-based computation for arbitrary layouts, architectures and nested-layout tables.
`Tests.LayoutAccumulation` covers order, explicit overlaps, empty layouts, missing children,
packing/offset failures and vector architecture restrictions.

Constrained-call validation and lowering build
ordered dispatch candidate indexes once per invocation, then reuse them across call sites. The indexes support type identity, method token/name and explicit interface override lookup. Candidate buckets retain duplicates, exact type checks and explicit override
precedence. Repeated override tokens within one method still contribute only one candidate.
Arbitrary-input equivalence theorems cover indexed resolution, complete instruction validation and
lowering, including malformed and ambiguous metadata. The list-based `resolveConstrained` remains
the specification used by those theorems; production validation and lowering use
`DispatchIndex.resolve`.

Validation and lowering each construct their own index; they do not share it across invocations. The
helper APIs `constrainedSiteWindow`, `constrainedSites`, `lowerConstrainedInstruction`,
`lowerConstrainedCode` and their streaming equivalence theorems accept a resolver function.

Public layout projection validation constructs balanced indexes for artifact selection and nested
public-index expansion. Ordered sets replace the three quadratic list-uniqueness checks.
`LayoutProjectionValid_iff_list` proves exact equivalence to all list-based conditions for arbitrary
inputs, including malformed indices and catalogs. `Tests.LayoutProjectionIndexes` checks reordering,
empty catalogs, duplicate identities/indices, case-sensitive identity, missing indices and nested
expansion.

The unfolded projection proposition exposes `projectionDistinct ... = true` and
`projectionMetadataMatches`. Consumers can recover the list-based uniqueness and metadata
conditions through `LayoutProjectionValid_iff_list`.

## Interface and theorem audits

Imported-interface auditing selects declarations from the imported module catalogs rather than
materializing and filtering every declaration in the Lean environment. Current-file declarations
still use the environment scan. Private and auxiliary declarations are included and their actual
module ownership is checked. Dependency traversal visits shared expression nodes only once;
contract serialization uses canonical expressions. `Tests.ContractClosure` compares selected membership
with the list-based scan, including current, imported, missing and duplicate modules. The imports
suite compiles that test against its already certified library instead of rebuilding the library's
dependencies in the repository checkout.

Fresh consumer verification audits the extraction certificate and requested proof in one native
import environment. Both artifacts must match their kernel-replayed module paths, and their
individual theorem types, premises and allowed axioms are still checked. This removes a repeated
closure import; it does not reuse a previous proof result or skip fresh verification.

`Tests/ConsumerCertificateReuse.cs` checks combined certificate/theorem audits and rejects
corrupted receipts, changed extraction and generated-source modifications.

### Allocation reference-step proof search

`fixed_fallback` normalizes mapped stack constructors definitionally and rewrites the target profile
once. It avoids repeatedly asking the simplifier to discharge the large dispatcher's negative match
conditions. Reference operations use a proved finite classification before stack case analysis.

The native auditor parses contract source import headers with
Lean's parser. Parsing still rejects malformed headers, retains comments and module-system import syntax, and never
elaborates source commands. The imports fixture checks those properties explicitly.

### Core example batches

Core's ten immutable example proofs share one generated verification batch. Each keeps its own
extraction, theorem audit, exact translation certificate and output identity check. The source,
environment, receipt and assembly mutation scenarios remain separate. The focused `dotnet run --file
Tests/CoreExamples.cs` fixture uses the same implementation; `--separate` reproduces the separate
verification loop, and `--check-existing <directory>` checks all reports and rejects changed proof
identity or batch source.

The generic-method, F# and universal-contract fixtures also batch their immutable positive proofs.
The generic instance and other fixed-memory contracts retain their exact statements; batching does
not turn them into arbitrary-memory specifications. Mutated assemblies and expected failures retain
their isolated checks.

Standalone proofs and generated batches combine their final replay and theorem audit when eligible.
Dependency certification, artifact identity checks and failure diagnostics remain; audits needing
source-location metadata still import the checked artifacts.

Compatible consumer requests can share that final replay and audit too. Each selected theorem and
its reachable replay-target declarations must belong to the request's own import closure. Duplicate
declarations and skipped consumer support conservatively retain separate checking. The fallback
replays each request's import-closed target set independently, preventing a forged proof from
borrowing an undeclared sibling dependency before an isolated axiom audit. `Tests/JointReplay.cs`
covers target and external owners, duplicate bodies and hidden dependencies. The existing consumer
batch checks also reject a theorem available only in another request.

`Tests/ConsumerCombinedAudit.cs` checks successful requests, expected failures and an
undeclared reference to an unapproved sibling axiom. Both shared and isolated fallback paths
must reject the hidden dependency. Its `--without-hidden` option selects the comparison workload.

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

`Tests/JointReplay.cs` exercises bootstrap and native replay against import-closed targets,
repeated equation lemmas, conflicting declarations, hidden dependencies and forged theorems.
Rejected joint sets fall back to per-module replay with individual failure attribution.
After auditor authentication, `--replay-separately` performs this fallback natively. Each module
gets its own imported environment and sequential kernel replay; no successful sibling can
supply an undeclared dependency. Bootstrap and profiling use the toolchain frontend runner.
Tests also cover malformed or missing target files, missing imports and changed bootstrap sources.

A single request whose fused audit reports a kernel rejection proceeds directly to isolated
replay. Unrecognized diagnostics and metadata/eligibility failures use the ordinary joint retry.
Within a batch workspace, an isolated helper rejection rejects later requests importing that
helper. Successful requests receive their own checks; successful joint module results are not
reused across request scopes. Each eligible request can fuse its own replay and theorem audit
after another request fails. The mixed-batch regressions check every status, certificate,
hidden-sibling rejection and isolated failure attribution.

The native auditor also accepts `replayTargets` in an audit request. It retains the kernel's checked
environment for structural theorem and constant checks, avoiding a second dependency import. Any
duplicate declaration, interface/closure/namespace request, or contract refutation requiring source
locations retains the ordinary audit import. This does not change the standalone replay duplicate
rule: equal theorem types can have different proof bodies, so a merged replay environment must not
choose which body's axioms a subsequent audit sees. `JointReplay` checks both duplicate orders, a
forged body, source-location fallback and toolchain shadowing in both paths.
Single-request consumer groups use this path, except export callbacks, full-import audits
and profiled replay. Existing byte snapshots, module-path checks and post-audit integrity checks
still bind the result. A rejected joint set retains per-module failure attribution. The verifier
records `auditFused` so measured runs distinguish shared environments from metadata or
duplicate-declaration fallbacks.

### Evidence-suite reuse

The evidence runner compiles its test modules once against the authenticated CIL library, without
asking Lake to rebuild that library from copied build traces. Test dependencies are ordered before
their importers, with at most two independent compilations running together. Child fixtures validate
the parent's source/output hashes before reusing a completed test; standalone fixture invocations
retain their original build path. The `dispatch` runner prepares its own modules the same way.
Reproduce this preparation with `dotnet run --file Tests/ExtractionEvidence.cs -- --prepare-only`
or `Tests/DispatchEvidence.cs -- --prepare-only`.

Generated rejection batches retain each mutation's original expected diagnostic markers. A Lean
command saves and restores the complete command state around each case, including its declarations,
attributes, scopes and options. Messages are collected with Lean's `#guard_msgs` command, then
associated with the original case's line range. A rejected neighbor, missing marker, successful
mutation or leaked failed simp theorem cannot satisfy another case's check;
`Tests/RejectedEvidenceTests.cs` exercises these failures. No rejection result is published until
every case passes. Existing audited positive batches still replay with `leanchecker`; direct
semantic fixtures retain their original frontend kernel checks while sharing imports.

The four capability profiles share one generated verification batch. Every profile keeps its own
extraction identity, execution theorem, certificate audit and final regeneration check. A regression
rejects reuse of the scalar report under the x64-v3 profile. The runtime-scope constants in the
scalar, type-test, throw, span and imported-layout fixtures use the existing byte representation,
whose equality to the full assembly-name literal is already proved by `runtimeScope_eq`.

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

Closed typeof comparisons cover value-producing calls, operandless `ceq` and short/long
reference-equality branches.
The branch cases check both identity outcomes in shared feature/scalar certificates; forged targets,
wrong opcodes, forwarded scopes and branches into erased operands fail independently. Runtime
comparisons exercise three closed generic instantiations in one generated proof batch.

Feature-flow validation indexes addressed local slots and classifies exact local types once, then
shares that index across state-shape checks, local transfers and emitted local operations.
`FeatureLocalIndex.eligible_eq` proves equality with the original raw instruction/type scan for
every index and fact, including malformed metadata and missing locals. The focused feature regression also
checks boolean bounds, both address-taking opcodes, wrong assembly scopes and malformed address
operands.

### Full verification and publication

Full-verification term transfer encodes each structurally distinct expression node once and writes a
compact data table instead of elaborating a recursively expanded constructor term. Structural
equality includes binder spelling and annotations; names retain numeric and string components, and
universe expressions retain their full structure. Metadata is stripped. The decoder
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
their independently replayed caller composition.
Consumer workspaces restore
authenticated, source-bound support before compiling published interfaces. Identical interfaces can
therefore reuse their compiled artifacts across extraction groups, while each workspace still
kernel-replays them and checks their canonical contract closures against its own imports.
Artifact integrity checks surround compilation. `Tests/ContractImports.cs --interface-reuse-only`
checks two fresh profile groups with one interface compilation and independent replays.

Consumer and standalone verification audit `Extracted.translation_valid` directly after kernel replay.
The native auditor requires a theorem
declaration, the exact `TranslationValid` application over the emitted tables and program, and the
approved axiom set. Consumer reports therefore name `Extracted.translation_valid` in
`extractionAudit`. Workspaces
containing expected proof rejections retain the wrapper, since those requests can finish before the
final native audit. Compiled extraction and component artifacts are hashed before consumer proof
checking and checked again afterward. Authenticated native replay also handles single-module target
sets; profiling retains the toolchain frontend, and rejected native replays retain the existing
per-module fallback.

Restored extraction modules and their components come from one complete authenticated generation.
Matching source hashes alone cannot justify mixing compiled generations: different bytes for an
import can make Lake rebuild its importer during proof checking. A focused real-Lake fixture
produces two valid compilations of identical sources, reproduces that rewrite with mixed restored
modules, and checks that restoring the complete closure keeps the extraction fixed when the proof
changes. Missing closures require certificate preparation before the integrity snapshot.

A two-request consumer fixture rewrites a compiled extraction artifact during proof compilation,
after warming both clean requests. It checks authenticated-restored and freshly built preparation:
the changed request reports extraction integrity, distinct before/after hashes and build provenance,
removes its stale certificate, and fails even when proof rejection was expected. The unrelated
request still verifies.

The component-reuse and support-union fixtures skip their framework-only warmup verification when
`LEANCIL_CERTIFIED_LIBRARY` is supplied. Their actual batches still authenticate that library and
verify every original request with success caching disabled. Without a supplied library, the
original warmup remains.

### Fold discovery

Fold discovery counts decoded local references once with a balanced tree instead of filtering the
entire instruction body per local. `foldRoles_eq_filter` proves exact equality to the filter-based
specification, including malformed operands and out-of-range local indexes. Methods without locals
skip count construction. The separate positional lookup of local types remains linear; this change
does not make all of fold discovery linear.

Exception folds inspect at most three message loads, since admitted constructors accept at most two.
`throwFold_eq_takeWhile` proves equality to the unrestricted prefix scan. Long rejected prefixes
still permit an admitted fold starting later. Span and throw evidence tests cover extra uses,
malformed local operands, oversized prefixes and valid suffix folds.

### Transitive composition replay

The transitive import suite runs its staged-bundle mutation probe in a separate process of its
already compiled executable. This preserves process isolation and all mutation checks without
compiling the shared verifier a second time. The helper remains a tracked suite input through its
include directive. Full composition also shares its final replay and exact audit; the transitive
fixture checks that this path uses the native auditor in one invocation.

### Fixed profile references

The profile-family fixture disables persistent receipts for its initial three-profile export. It
requires one fixed-reference build and three independent profile extraction replays. Source-bound
authenticated references already shared compilation; the verifier avoids Lake invocations when their
restored module parts and traces still match exactly.

## Allocation-relative reference helpers

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
