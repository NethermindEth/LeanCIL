# Contract export and consumer validation

<!-- audience: maintainers -->

This page lists what the `exports` partitions check, and the regressions behind extraction
bookkeeping, metadata indexes, interface and theorem audits, joint kernel replay and full
verification. Read it before changing contract export, the native auditor or an indexed validator.

## Export suite selection

`dotnet run --file Tests/ContractExport.cs` runs every export cohort once. `dotnet run --file
scripts/Test.cs -- --suite all` runs the same partitions once with the other suites. Each
partition has a fresh SDK and proof workspace. Full verification keeps fresh extraction, source
audit, independent kernel replay, and all report and artifact checks.

Run one partition with `dotnet run --file scripts/Test.cs -- --suite NAME`:

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
| `exportsstatics` | Standalone modular static exports with their own SDK setup and assertions |
| `exportsfullstatics` | The same fixture with `--full-composition`: forced full verification of app and library tables with one local index and one table shared by two imported slots, run after a repeated ordinary verification restored a receipt; a republished bundle with forged static records fails in preflight and a re-certified changed table fails the independent library proof; a chain of Top, App and library independently composes the table reader with its static-world premise |
| `exportstransitive` | A chain of App, A and B, and a four-node diamond where A and C share B; full mode rechecks each selected export despite warm receipts, rejects changed deployment pins and cycles before building, rejects forged dependency composition, and detects B changing staged A before A builds |
| `exportstransitiveoutcomes` | A chain of App, C, A and B independently preserves normal returns and the named exceptional outcome through three forwarders |
| `exportsdiscovery` | Real producer SDK/publication bootstrap, then the six-argument discovery fixture |
| `exportstyped` | Standalone closed-generic, imported-layout and imported-local fixture with its own SDK setup and assertions |
| `exportsderived` | Standalone derived public contracts: `Holds.weaken` exports, sidecar-only callers, refuted weakenings |
| `exportsinitialized` | A static-readonly struct library exports a named initialization premise; its caller retains the scoped premise, malformed descriptors reject, and full verification is unavailable |
| `exportsprofiles` | One family theorem across three profiles, independent full composition, outcome families and scoped initialization premises; disagreeing flags, unequal programs, malformed selections, forged audit declarations and compiled-reference mutation reject |

[ExportVerificationSuites.cs](../scripts/ExportVerificationSuites.cs) registers the 23 partitions
and their case IDs. [Suite jobs](CI.md#suite-jobs) gives their CI time limits.

### Case ledger

- The base ledger has 49 cases: 22 core, 3 protected, 2 callback, 2 resolution and 20 full cases.
  Each partition rejects an omitted, repeated or unexpected completion.
- The artifact-mode rejection runs after consumer requests that succeed, so it checks removal of
  a successful report that a request wrote.
- The default eight-argument `Tests/FullImportVerification.cs` invocation runs resolution and all
  full cohorts once; `--cohort NAME` selects one full cohort. Unknown, missing or duplicate
  selections fail before fixture setup. The full plan holds only its ten base cohorts; the
  standalone and discovery partitions cannot enter it.
- `exportsstatics`, `exportsfullstatics`, `exportstransitive`, `exportstransitiveoutcomes`,
  `exportstyped`, `exportsderived`, `exportsinitialized` and `exportsprofiles` run directly, with
  no core export bootstrap or nested post-call. Their fixture assertions are separate from the 49
  base case IDs, and a standalone fixture cannot use an empty base completion ledger to claim
  coverage.
- `exportsdiscovery` records one separate `discovery.fixture` completion after the child
  succeeds; the child's behaviors are outside the 49 base cases. The partition builds the
  producer library and creates its proof packages and publication. The child builds, extracts
  and verifies its own caller and needs no baseline caller artifact or verified report. The
  partition runs no core caller verification, restrictions, callbacks or full cases.
- `exportstyped` owns its fixture and five input proof/interface modules; shared model and proof
  dependencies keep their own owners.
- `exportsderived` owns its fixture and the five `Derived*` interface, producer and caller modules
  in `Tests/ContractImports`. It proves exact internal method and outcome contracts on its own
  extraction and exports public ones derived only through `Holds.weaken`. Callers verify from the
  sidecar alone, on normal and named-exception paths. Stronger posts, weaker preconditions,
  smaller footprints and renamed exceptions are refuted on the same extraction; at the exporter,
  one renamed exception fails only its refinement proof.

Full integration results come from the CI partition jobs. The routing tests,
`dotnet run --file scripts/TestSelectVerification.cs`, need no Lean build or fixture SDK project.

## Extraction and metadata checks

### Fixtures

- `Tests/PointerOperations.cs` compares seven compiled pointer methods with .NET: int32/native
  byte subtraction, pointer differences and four unsigned orderings. The Lean scalar certificate
  must reject subtraction forged as addition. The Lean fixtures cover negative offsets and
  differences, end positions, readonly preservation, every unsigned branch, and null,
  cross-allocation, invalid-position and signed-comparison rejection.
- `Tests/ExtractionGenerics.lean` and the 15 generated generic-method samples in
  `Tests/GenericEvidence.cs` cover managed-call proof construction. Direct tactic rejection checks
  cover changed signedness, assembly scope, generic arguments and argument count.
- `Tests/GenericEvidence.cs` also checks exact external-call identity sharing, repeated emission,
  pruned-only identities and Unicode/escaped characters. Changed bytes, versions and tokens fail
  the generated equality proof. Replacing a raw target with another correctly encoded identity, or
  changing its emitted intrinsic, fails the unchanged division certificate. The specialization and
  raw/translated metadata rejection cases run alongside.
- `Tests/AllocationImports.cs`, in `core`, checks that the CIL umbrella omits allocation
  refinement, builds both explicit allocation acceptance modules, and jointly replays every
  additional imported module, which ordinary consumers do not import. The compiled namespace
  audit checks their theorem axiom closures even on warm builds and binds the audited paths and
  module bytes to those replayed. An isolated theorem depending on `sorryAx` passes kernel replay
  but must fail that audit; build output is also checked.
- The registered constrained and import evidence suites test unreachable switch-prefix bypass,
  duplicate switch targets, short reachability, both import-table bounds, and trailing-prefix and
  extra-emitted-instruction rejection for constrained and opaque-local evidence.
- The transitive import regression checks identical imports before rejecting ambiguous versions.

### Indexed validators

Each validator below uses an index in place of repeated list scans. The table gives the
equivalence theorem or property stated for each index and the regression that covers it.

| Check | Guarantee | Regression |
| --- | --- | --- |
| Certificate successor index | `FlowIndex.build_spec` proves prefix consumption and exact list lookup equivalence. Feature and scalar validators use the proved optional-lookup interface. The shared state-pairing proof uses explicit list-shape cases and depends only on `propext`. | `Tests.FlowIndex`: empty and singleton inputs, odd/even partitions, missing certificate states, out-of-bounds lookups and untouched suffixes |
| Region closure | Builds an ordered map of each method's minimum starting pc, visits program methods in order and checks each included body once. Absent region entries are skipped and region membership is kept for absent callees: execution validity is a separate obligation. The equivalence theorem covers the list-based specification exactly, including duplicate starts and out-of-range pcs. | `Tests.RegionRun`; `Tests/RegionScaling.lean` is a standalone workload for `leanprof elab --heartbeats` |
| Region suffix membership | Fallthrough closure is automatic, since `lower ≤ pc` implies `lower ≤ pc + 1`, so the checker looks up only explicit branch targets and callees. Its equivalence theorem covers every instruction, including a final fallthrough beyond the body; instruction availability is a separate execution obligation. | `Tests.RegionRun` |
| Constrained validation and lowering | Balanced instruction/reachability indexes and a set of all decoded branch destinations, including unreachable instructions and switch arms; lowering also indexes predecessor instructions. `lowerConstrainedRaw_eq_original` proves identical output for arbitrary raw bodies, including malformed prefixes. `ConstrainedCallsValid_iff_original` preserves the list-based rules. | Constrained evidence suites |
| Sequential constrained evidence | Validation consumes the raw, reachability and emitted lists together, keeping the previous instruction and reading the next from the tail; lowering keeps the raw predecessor before rewriting it. Malformed-neighbor and length rejection, method-target lookup, branch membership and dispatch metadata resolution are unchanged checks. | Constrained evidence suites |
| Managed-call validation | Indexes extracted methods and imported slots once per method check. `ManagedCallsValid_iff_original` preserves the list-based rules, including absent entries, import offsets and malformed lengths. `cil_managed_calls` uses structural metadata equalities before its kernel-decision fallback. | Import evidence suites |
| Home discovery, static sites, opaque locals | Balanced indexes: `Std.TreeSet`/`Std.TreeMap` for keyed membership and `FlowIndex` for positional lookup. Home discovery collects live stores and addresses once and keeps argument order while filtering the argument range. Static sites keep the first descriptor at a duplicate pc. Opaque-local discovery considers addresses in the complete raw body, including dead instructions, and reads each type from `zipIdx`. Equivalence theorems cover arbitrary input lists, including malformed indexes, duplicate sites and truncated masks; they require no new assumptions. | `Tests.ExtractionHomeIndexes` |
| Parameter home enumeration | Enumerates the collected ordered set and filters by the argument bound. The proved list equality keeps ascending order, duplicate elimination, out-of-range filtering and truncated reachability semantics. | `Tests/HomeEnumerationScaling.lean` compares both algorithms |
| Argument instruction validation | Shares indexes for argument types and appended home slots; expected home kinds use the argument-type index. The home-slot map keeps the first occurrence for duplicate home lists; missing argument indexes, hidden home accesses and unsupported replacements are rejected. Exact lookup/check equivalence theorems preserve the semantic consequence statements. | `Tests.ExtractionHomeIndexes` |
| Feature-flow local facts | Indexes addressed local slots and classifies exact local types once, shared across state-shape checks, local transfers and emitted local operations. `FeatureLocalIndex.eligible_eq` proves equality with the raw instruction/type scan for every index and fact, including malformed metadata and missing locals. | The focused feature regression also checks boolean bounds, both address-taking opcodes, wrong assembly scopes and malformed address operands |

[Fold discovery](#fold-discovery) has its own equivalence theorems.

### Extractor bookkeeping

These regressions cover the extractor's own C# indexes:

- Extraction bookkeeping indexes declaration names, imported assembly identities, imported call
  slots, batch proof modules and aggregate layout names, and keeps component imports in
  declaration order. `Tests/ConsumerSupportCandidates.cs` checks dependency ordering and
  conservative references in literal text; `Tests/InstructionIndexes.cs` checks nested layout
  ordering and absent types.
- Aggregate metadata validation rejects duplicate instance/static field names and duplicate full
  type names. It rebuilds its name counts on each public layout request, so later metadata
  mutations are visible. `Tests/InstructionIndexes.cs` includes those rejection and mutation
  cases.
- Template emission writes templates and callees in sorted order and profiles in input order,
  and rejects duplicate method identities before emission. An absent callee in an excluded
  profile gets a zero placeholder. `Tests/TemplateIndexes.cs` checks reordered methods,
  conditional absent callees, deterministic output and duplicate rejection without compiling Lean.
- Loaded contract libraries index exports by exact identity and certifications by exact
  (identity, profile). The production reader rejects duplicates before constructing either index.
  `Tests/ImportIndexes.cs` checks case-sensitive lookup, multiple profiles and the reader's exact
  duplicate diagnostics using an otherwise accepted interface.
- Blocker collection keeps ordered lists for sites, entries and call chains and deduplicates
  through indexes. Sites use record value equality; entries use exact (signature, profile) keys;
  chains use full ordinal element equality, including element boundaries and order. Findings and
  reaches have reference identity, so assigning a finding's output ID cannot change its hash.
  `Tests/Blockers.cs` checks distinct arrays with equal contents, distinct chain splits, profile
  case and first-seen output ordering. The full fixture report matches the single-request CLI
  except for its extractor hash.

## Layout and dispatch indexes

- Translation validation and Lean emission each own a `LayoutContext`, scoped to one module and
  architecture, which reuses fully validated root layouts and field/position snapshots. Every
  new root runs the recursive validator with a fresh active set and recursive cache, so warming
  a child cannot bypass the 128-level nesting check. Contexts never cross metadata rewrites or
  extraction requests, and context-taking helpers reject module/architecture mismatches.
  `Tests/InstructionIndexes.cs` checks nested-root reuse, field identity/order, fresh-call
  mutation visibility, distinct x64/arm64 vector layouts and nesting rejection after warming a
  child.
- C# argument translation indexes argument home positions once per method in validation,
  emission and exception lint. Duplicate inputs keep their first position, missing homes stay
  absent, and raw locals are added to the home position when emitting local-slot instructions.
  `Tests/InstructionIndexes.cs` exercises loads, stores, addresses, duplicate homes and
  missing-store rejection.
- Interface-module merging detects spelling collisions ignoring ordinal case and writes its
  output in ordinal sorted order. Exact duplicate names with identical source are accepted;
  changed source or different casing is rejected, including Unicode ordinal case pairs.
  `Tests/ImportIndexes.cs` exercises this rule independently of interface admission.
- Static initializer bindings use the emitter's method-identity index. Null initializers use
  zero and missing initializers produce the `-1` sentinel. Validation shares a read-only
  `StaticValues.Context` within one metadata validation walk. Specialization creates detached
  clones, so the
  compiled module is unchanged. Each validation gets a fresh context, and no index persists for
  the module. Index construction records resolution failures, so a later failure cannot replace
  the earlier writer diagnostic. `Tests/StaticValueIndexes.cs` checks scalar copies, duplicate
  stores, prefix control flow, branch/switch and foreign targets, first outside writer, closure
  address-taking, fresh contexts and resolution-error ordering, and that computable scalars never
  resolve as unknown while random seeds do.
- Layout computation accumulates field placements in reverse and restores declaration order
  once. `computeLayout_eq_append` proves equality to the complete list-based computation for
  arbitrary layouts, architectures and nested-layout tables. `Tests.LayoutAccumulation` covers
  order, explicit overlaps, empty layouts, missing children, packing/offset failures and vector
  architecture restrictions.
- Constrained dispatch validation and lowering each build ordered dispatch candidate indexes
  once per invocation and reuse them across call sites, never across invocations. The indexes
  support type identity, method token/name and explicit interface override lookup. Candidate
  buckets keep duplicates, exact type checks and explicit override precedence; repeated override
  tokens within one method contribute one candidate. Arbitrary-input equivalence theorems cover
  indexed resolution, complete instruction validation and lowering, including malformed and
  ambiguous metadata. The list-based `resolveConstrained` is the specification those theorems
  use; production validation and lowering use `DispatchIndex.resolve`. The helpers
  `constrainedSiteWindow`, `constrainedSites`, `lowerConstrainedInstruction`,
  `lowerConstrainedCode` and their streaming equivalence theorems accept a resolver function.
- Public layout projection validation indexes artifact selection and nested public-index
  expansion, and uses ordered sets for its three uniqueness checks.
  `LayoutProjectionValid_iff_list` proves exact equivalence to all list-based conditions for
  arbitrary inputs, including malformed indices and catalogs. The unfolded proposition exposes
  `projectionDistinct ... = true` and `projectionMetadataMatches`; recover the list-based
  uniqueness and metadata conditions through `LayoutProjectionValid_iff_list`.
  `Tests.LayoutProjectionIndexes` checks reordering, empty catalogs, duplicate identities/indices,
  case-sensitive identity, missing indices and nested expansion.

## Interface and theorem audits

- Imported-interface auditing selects declarations from the imported module catalogs.
  `interfaceDeclarations` finds current-file declarations in the second stage of Lean's staged
  constant map; it scans every constant when the map is still in its first stage or the current
  module reuses an imported module's name. Private and auxiliary declarations are included and
  their module ownership is checked. Dependency traversal visits shared
  expression nodes once; contract serialization uses canonical expressions.
  `Tests.ContractClosure` compares selected membership with the list-based scan, including
  current, imported, missing and duplicate modules and a colliding module name. The `imports`
  suite compiles that test against its certified library.
- Fresh consumer verification audits the extraction certificate and requested proof in one native
  import environment. Both artifacts must match their kernel-replayed module paths, and their
  individual theorem types, premises and allowed axioms are checked. This audit reuses no
  previous proof result and skips no fresh verification. The `certificate-reuse`
  [consumer check](VALIDATION-COVERAGE.md#consumer-checks) covers it.
- The native auditor parses contract source import headers with Lean's parser. It rejects
  malformed headers, keeps comments and module-system import syntax, and never elaborates source
  commands. The `imports` fixture checks those properties.
- Consumer and standalone verification audit `Extracted.translation_valid` directly after kernel
  replay. The native auditor requires a theorem declaration, the exact `TranslationValid`
  application over the emitted tables and program, and the approved axiom set. Consumer reports
  name `Extracted.translation_valid` in `extractionAudit`. Workspaces containing expected proof
  rejections keep the wrapper, since those requests can finish before the final native audit.
- Compiled extraction and component artifacts are hashed before consumer proof checking and
  checked again afterward.

### Allocation reference-step proof search

`fixed_fallback` normalizes mapped stack constructors definitionally and rewrites the target
profile once, without asking the simplifier to discharge the large dispatcher's negative match
conditions. Reference operations use a proved finite classification before stack case analysis.

### Core example batches

Core's ten immutable example proofs share one generated verification batch. Each keeps its own
extraction, theorem audit, exact translation certificate and output identity check. The source,
environment, receipt and assembly mutation scenarios run separately.

`dotnet run --file Tests/CoreExamples.cs` runs the same implementation alone; `--separate`
verifies each example in its own request, and `--check-existing <directory>` checks all reports
and rejects changed proof identity or batch source.

The generic-method, F# and universal-contract fixtures also batch their immutable positive proofs.
The generic instance and other fixed-memory contracts keep their exact statements, so batching
leaves them fixed-memory specifications. Mutated assemblies and expected failures have isolated
checks.

### Native joint kernel replay

`leancil-audit --replay INPUT`, run after the executable is authenticated, accepts a JSON array of
module names. It uses the same `CIL/Replay.lean` algorithm as fresh-library bootstrap
certification: import non-target dependencies without extensions, reject conflicting declarations
and replay target constants in the kernel. Identical on-demand theorem duplicates follow the
toolchain rule. The native executable is checked before and after replay. Before it is
authenticated, bootstrap uses the source captured when the verifier starts and rejects changes
before executing it. Bootstrap and profiling use the toolchain frontend runner.

| Situation | Behavior |
| --- | --- |
| Standalone proof, generated batch or single-request consumer group, when eligible | Final replay and theorem audit run together in one native environment, including single-module target sets. Dependency certification, artifact identity checks and failure diagnostics are unchanged. |
| Compatible consumer requests | May share that replay and audit. Each selected theorem and its reachable replay-target declarations must belong to the request's own import closure. The fallback replays each request's import-closed target set independently, so a forged proof cannot use an undeclared sibling dependency before an isolated axiom audit. |
| Duplicate declarations, skipped consumer support | Checked separately. |
| Export callback, full-import audit, profiled replay, audit needing source locations | Use the ordinary audit import of the checked artifacts. |
| Direct and consumer contract interfaces | Replayed and validated in the same native environment when their complete declaration ownership is unambiguous. The ownership map enumerates private, auxiliary and unused declarations; interface checks do not select only the exported contract's dependencies. A reached declaration that neither the map nor the imported module index places in a module fails the closure walk. |
| Imported interface outside the replay target set, duplicate ownership, conflicting code-generator ownership | Metadata import fallback. |
| Rejected joint set | `--replay-separately` replays per module: each module gets its own imported environment and sequential kernel replay, so no successful sibling can supply an undeclared dependency, and each failure is attributed to its module. |
| Single request whose fused audit reports a kernel rejection | Goes directly to isolated replay. Unrecognized diagnostics and metadata or eligibility failures use the ordinary joint retry. |
| Batch workspace with an isolated helper rejection | Later requests importing that helper are rejected. Successful requests get their own checks; successful joint module results are not reused across request scopes, and each eligible request can fuse its own replay and audit after another fails. |

An audit request may carry `replayTargets`: the auditor then keeps the kernel's checked
environment for structural theorem and constant checks, with no second dependency import. Any
duplicate declaration, interface/closure/namespace request, or contract refutation requiring
source locations uses the ordinary audit import. Standalone replay keeps its duplicate rule:
equal theorem types can have different proof bodies, so a merged replay environment must not
choose which body's axioms a subsequent audit reads. Byte snapshots, module-path checks and
post-audit integrity checks bind the result. The verifier records `auditFused`, so measured runs
distinguish shared environments from metadata or duplicate-declaration fallbacks.

Single-request contract exports combine declaration replay with the complete theorem, constant and
closure audit; source and artifact checks surround the export callback.

These regressions cover joint replay:

- `Tests/JointReplay.cs` exercises bootstrap and native replay against import-closed targets,
  repeated equation lemmas, conflicting declarations, hidden dependencies and forged theorems;
  target and external owners and duplicate bodies; malformed or missing target files, missing
  imports and changed bootstrap sources; both duplicate orders, a forged body, source-location
  fallback and toolchain shadowing in both paths. It compares ordinary and replayed interface
  verdicts, including module-system private declarations, unused forbidden axioms, misleading
  namespaces and equation auxiliaries. `-- --audit-only` runs the native audit regressions without
  the independent bootstrap and native replay regressions.
- `Tests/ConsumerCombinedAudit.cs` checks successful requests, expected failures and an undeclared
  reference to an unapproved sibling axiom; both the shared and the isolated fallback path must
  reject the hidden dependency. `--without-hidden` selects the comparison workload.
- The consumer batch checks reject a theorem available only in another request. The mixed-batch
  regressions check every status, certificate, hidden-sibling rejection and isolated failure
  attribution.

### Evidence-suite reuse

- The `evidence` runner compiles its test modules once against the authenticated CIL library,
  without asking Lake to rebuild that library from copied build traces. Child fixtures validate
  the parent's source/output hashes before reusing a completed test; a standalone fixture
  invocation builds on its own. The `dispatch` runner prepares its modules the
  same way. Run this preparation alone with
  `dotnet run --file Tests/ExtractionEvidence.cs -- --prepare-only` or
  `Tests/DispatchEvidence.cs -- --prepare-only`.
- Generated rejection batches keep each mutation's expected diagnostic markers. A Lean command
  saves and restores the complete command state around each case, including its declarations,
  attributes, scopes and options. Messages are collected with `#guard_msgs` and associated with
  the case's line range. A rejected neighbor, missing marker, successful mutation or leaked failed
  simp theorem cannot satisfy another case's check; `Tests/RejectedEvidenceTests.cs` exercises
  these failures. No rejection result is published until every case passes. Audited positive
  batches replay with `leanchecker`; direct semantic fixtures keep their frontend kernel checks
  while sharing imports.
- The four capability profiles share one generated verification batch. Every profile keeps its
  own extraction identity, execution theorem, certificate audit and final regeneration check. A
  regression rejects reuse of the scalar report under the x64-v3 profile.
- The runtime-scope constants in the scalar, type-test, throw, span and imported-layout fixtures
  use the byte representation whose equality to the full assembly-name literal `runtimeScope_eq`
  proves. Generated generic constraint lists name the byte-backed
  `CIL.Extraction.valueTypeConstraint` and `CIL.Extraction.unmanagedTypeConstraint`, whose equality
  theorems prove them equal to the scoped metadata strings; other constraint identities stay
  string literals.
- `Tests/ScalarEvidence.lean` groups related kernel-decided cases into named private theorems,
  each a conjunction of the original statements followed by `#print axioms`; the other cases stay
  separate.
- [Coverage](VALIDATION-COVERAGE.md#evidence-batches) gives the positive-control rules for
  constrained-call rejection fixtures.
- Static-span proofs share one batch across original and mutated assemblies, and UTF-8 identity
  mutations use isolated rejection scopes.
- Generated verification batches use the authenticated native kernel replay command when it
  succeeds and the toolchain checker as the failure fallback for the same module set.
- Translation-audit fixtures share one checked prefix across their certificate variants;
  [coverage](VALIDATION-COVERAGE.md#standalone-certificates-and-translation-audit) lists the
  cases.
- Generic substitution, managed-call and method-shape mutations select their corresponding emitted
  validator; type-test mutations select feature-flow validation. External-call mutation fixtures
  check only the intended division or intrinsic validator, with a complete positive certificate
  and a checked unchanged-obligation control in the replayed evidence batch. Unchanged controls
  compile first, with repeated generic controls deduplicated. Byte-backed identity definitions
  keep their UTF-8 witnesses. Evidence-list omission and reordering check the complete
  certificate, because they test agreement between records and no single validator.
- Closed typeof comparisons cover value-producing calls, operandless `ceq` and short/long
  reference-equality branches. The branch cases check both identity outcomes in shared
  feature/scalar certificates; forged targets, wrong opcodes, forwarded scopes and branches into
  erased operands fail independently. Runtime comparisons exercise three closed generic
  instantiations in one generated proof batch.

### Full verification and publication

- Full-verification term transfer encodes each structurally distinct expression node once and
  writes a compact data table. Structural equality includes binder spelling and annotations;
  names keep numeric and string components, and universe expressions keep their full structure.
  Metadata is stripped. The decoder rejects missing, cyclic and forward references, unknown
  binder annotations and malformed table data. Free variables and expression/universe
  metavariables are not supported. Decoding constructs expressions only; each transferred
  declaration is kernel-checked as [full verification](FULL_VERIFICATION.md) describes, then
  passes the independent replay and exact composition audit. The generated source imports the
  decoder from the certified `CIL.Interface.FullTransfer` module. `Tests.FullTransfer` checks exact
  reconstructed types and values across binders, universes, projections, local lets, string
  literals and proofs, plus malformed table rejection. The full transitive suite covers forged
  dependency, staged mutation, changed implementation, cyclic dependency and missing-bundle
  regressions.
- Contract publication audits interface declarations and their requested closures in one
  imported environment. The fresh consumer theorem audit also requests each export's closure and
  certified statement, including independently rebuilt full-verification exports. Export
  callbacks consume that authenticated response after the artifact and source guards, without
  importing the environment again. The closure digest, contract kind, theorem axioms and
  statement checks are separate obligations. `exportsaudit` exercises source and
  compiled-artifact mutation after those callbacks and requires the original integrity failures.
- Exports whose artifacts lie outside the proof root share one consumer input snapshot and the
  extraction-group verification machinery; each request keeps its own exact export audit and
  checked result. Artifacts inside the proof root keep individual snapshots, so their output
  exclusion does not hide another request's source. `exportsfullpair` checks two exported methods
  and their independently replayed caller composition.
- Consumer workspaces restore authenticated, source-bound support before compiling published
  interfaces. Identical interfaces can reuse their compiled artifacts across extraction groups,
  while each workspace kernel-replays them and checks their canonical contract closures against
  its own imports. Artifact integrity checks surround compilation.
  `Tests/ContractImports.cs --interface-reuse-only` checks two fresh profile groups with one
  interface compilation and independent replays.
- Restored extraction modules and their components come from one complete authenticated
  generation. Matching source hashes alone cannot justify mixing compiled generations: different
  bytes for an import can make Lake rebuild its importer during proof checking. A focused
  fixture that runs Lake produces two valid compilations of identical sources, reproduces that
  rewrite with mixed restored modules, and checks that restoring the complete closure keeps the
  extraction fixed when the proof changes. Missing closures require certificate preparation
  before the integrity snapshot.
- A two-request consumer fixture rewrites a compiled extraction artifact during proof
  compilation, after warming both clean requests. For both authenticated-restored and freshly
  built preparation, the changed request reports extraction integrity, distinct before/after
  hashes and build provenance, removes its stale certificate, and fails even when proof rejection
  was expected. The unrelated request verifies.
- The component-reuse and support-union fixtures skip their framework-only warmup verification
  when `LEANCIL_CERTIFIED_LIBRARY` is supplied. Their batches authenticate that library and
  verify every request with success caching disabled.

### Fold discovery

Fold discovery counts decoded local references once. `foldRoles_eq_filter` proves exact equality
to the filter-based specification, including malformed operands and out-of-range local indexes.
Methods without locals skip count construction. The positional lookup of local types is linear,
so fold discovery as a whole is not linear.

Exception folds inspect at most three message loads, since admitted constructors accept at most
two. `throwFold_eq_takeWhile` proves equality to the unrestricted prefix scan. A long rejected
prefix does not prevent an admitted fold starting later. Span and throw evidence tests cover extra
uses, malformed local operands, oversized prefixes and valid suffix folds.

### Transitive composition replay

The transitive import suite runs its staged-bundle mutation probe in a separate process of its
compiled executable, which keeps process isolation and all mutation checks. The helper is a
tracked suite input through its include directive. Full composition shares its final replay and
exact audit; the transitive fixture checks that this path uses the native auditor in one
invocation.

### Fixed profile references

The profile-family fixture disables persistent receipts for its initial three-profile export. It
requires one fixed-reference build and three independent profile extraction replays. The verifier
makes no Lake invocation for a source-bound authenticated reference whose restored module parts
and traces match exactly.

## Allocation-relative reference helpers

`Unsafe.AreSame<T>`, `IsAddressLessThan<T>`, `IsAddressGreaterThan<T>`, `ByteOffset<T>`,
`AddByteOffset<T>`, `SubtractByteOffset<T>` (signed and unsigned native offsets) and element
`Subtract<T>` use the checked allocation-relative reference operations, whose admitted forms
[OPCODES](OPCODES.md#reference-observations) lists and whose limits
[reference observations](SOUNDNESS-EVIDENCE.md#reference-observations) states. Generic storage
types must have a supported managed layout. Lean translation evidence checks exact runtime
identity, closed signatures, offset signedness and byte scaling. `ByteOffset` accepts readonly
views, and byte and element offsets from a readonly reference stay readonly.

Tests compare native wraparound with the runtime and reject forged strides and signedness in Lean
evidence. These operations do not model arbitrary numeric addresses or establish runtime placement
of separate allocations.
